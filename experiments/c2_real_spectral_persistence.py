#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import json
import math
from dataclasses import asdict, dataclass
from decimal import Decimal, localcontext
from pathlib import Path
from typing import Any, Sequence

import numpy as np

import c2_real_spectral_grid as scanner
import c2_real_spectral_mechanism as mechanism


@dataclass(frozen=True)
class TrackedMinimum:
    candidate: int
    cut: int
    grid_index: int
    t_decimal: str
    t_float: float
    score: float
    dimension_free_residual: float
    blind_fraction: float
    total_energy: float
    visible_angle_degrees: float
    seed_bracket_cosine: float | None
    camera_residual_alignment: float


def _decimal_list(text: str) -> tuple[Decimal, ...]:
    values = tuple(Decimal(part.strip()) for part in text.split(",") if part.strip())
    if not values:
        raise ValueError("at least one candidate is required")
    return values


def _int_list(text: str) -> tuple[int, ...]:
    values = tuple(int(part.strip()) for part in text.split(",") if part.strip())
    if not values or any(value < 1 for value in values):
        raise ValueError("cuts must be positive integers")
    return values


def _atlas_list(text: str) -> tuple[tuple[int, ...], ...]:
    values = tuple(
        scanner.parse_primes(block.strip())
        for block in text.split(";")
        if block.strip()
    )
    if not values:
        raise ValueError("at least one atlas is required")
    return values


def _local_grid(center: Decimal, radius: Decimal, step: Decimal) -> scanner.DecimalGrid:
    if radius <= 0 or step <= 0:
        raise ValueError("radius and dt must be positive")
    with localcontext() as ctx:
        ctx.prec = 50
        lower = center - radius
        upper = center + radius
    return scanner.DecimalGrid.from_strings(
        format(lower, "f"), format(upper, "f"), format(step, "f")
    )


def local_grid_minimum(
    center: Decimal,
    radius: Decimal,
    step: Decimal,
    primes: Sequence[int],
    cut: int,
    candidate_index: int,
) -> TrackedMinimum:
    """Select the minimum on an exact decimal grid, with no continuous refinement."""
    grid = _local_grid(center, radius, step)
    ts = grid.float_values()
    models = scanner.build_prime_models(tuple(primes), cut, np)
    scores = np.asarray(
        scanner.evaluate_operator_chunk(ts, models, np), dtype=np.float64
    )
    index = int(np.argmin(scores))
    t_decimal = grid.text_at(index)
    t_float = float(ts[index])
    diagnostic = mechanism.evaluate_mechanism(t_float, tuple(primes), cut)
    return TrackedMinimum(
        candidate=candidate_index,
        cut=cut,
        grid_index=index,
        t_decimal=t_decimal,
        t_float=t_float,
        score=float(diagnostic["score"]),
        dimension_free_residual=float(diagnostic["dimension_free_residual"]),
        blind_fraction=float(diagnostic["blind_fraction"]),
        total_energy=float(diagnostic["total_energy"]),
        visible_angle_degrees=float(diagnostic["visible_angle_degrees"]),
        seed_bracket_cosine=diagnostic["seed_bracket_cosine"],
        camera_residual_alignment=float(diagnostic["camera_residual_alignment"]),
    )


def _power_decay_exponent(
    cuts: Sequence[int], values: Sequence[float]
) -> float | None:
    pairs = [
        (float(cut), float(value))
        for cut, value in zip(cuts, values)
        if cut > 0 and value > 0.0 and math.isfinite(value)
    ]
    if len(pairs) < 2:
        return None
    x = np.log([pair[0] for pair in pairs])
    y = np.log([pair[1] for pair in pairs])
    slope = float(np.polyfit(x, y, 1)[0])
    return -slope


def _shift_signature(values: Sequence[float]) -> dict[str, Any]:
    shifts = [right - left for left, right in zip(values, values[1:])]
    nonzero_signs = [1 if shift > 0 else -1 for shift in shifts if shift != 0.0]
    alternations = sum(
        left != right for left, right in zip(nonzero_signs, nonzero_signs[1:])
    )
    return {
        "shifts": shifts,
        "max_abs_shift": max((abs(shift) for shift in shifts), default=0.0),
        "alternation_count": alternations,
        "classification": "oscillatory_boundary" if alternations >= 1 else "regular",
    }


def run_lab(
    candidates: Sequence[Decimal],
    cuts: Sequence[int],
    primes: Sequence[int],
    radius: Decimal,
    step: Decimal,
    atlas_sets: Sequence[Sequence[int]],
) -> dict[str, Any]:
    """Track candidate valleys, controls and atlas dependence across finite cuts."""
    tracked: list[TrackedMinimum] = []
    summaries: list[dict[str, Any]] = []
    for candidate_index, seed in enumerate(candidates, 1):
        center = seed
        rows: list[TrackedMinimum] = []
        for cut in cuts:
            row = local_grid_minimum(
                center, radius, step, primes, cut, candidate_index
            )
            rows.append(row)
            tracked.append(row)
            center = Decimal(row.t_decimal)
        heights = [row.t_float for row in rows]
        residuals = [row.dimension_free_residual for row in rows]
        summaries.append(
            {
                "candidate": candidate_index,
                "seed_decimal": format(seed, "f"),
                "residual_decay_exponent": _power_decay_exponent(cuts, residuals),
                "height_dynamics": _shift_signature(heights),
                "last": asdict(rows[-1]),
            }
        )

    controls: list[dict[str, Any]] = []
    for control_index, (left, right) in enumerate(
        zip(candidates, candidates[1:]), 1
    ):
        point = (left + right) / 2
        rows = []
        values = []
        for cut in cuts:
            diagnostic = mechanism.evaluate_mechanism(
                float(point), tuple(primes), cut
            )
            value = float(diagnostic["dimension_free_residual"])
            values.append(value)
            rows.append({"cut": cut, "dimension_free_residual": value})
        controls.append(
            {
                "control": control_index,
                "t_decimal": format(point, "f"),
                "residual_decay_exponent": _power_decay_exponent(cuts, values),
                "rows": rows,
            }
        )

    max_cut = max(cuts)
    atlas: list[dict[str, Any]] = []
    for summary in summaries:
        center = Decimal(summary["last"]["t_decimal"])
        candidate = int(summary["candidate"])
        rows = []
        for prime_set in atlas_sets:
            row = local_grid_minimum(
                center, radius, step, prime_set, max_cut, candidate
            )
            rows.append({"primes": list(prime_set), **asdict(row)})
        heights = [row["t_float"] for row in rows]
        atlas.append(
            {
                "candidate": candidate,
                "max_height_spread": max(heights) - min(heights),
                "rows": rows,
            }
        )

    return {
        "schema": "org.genuine.real-spectral-persistence/v1",
        "status": "FINITE_NUMERICAL_PERSISTENCE_AUDIT",
        "no_continuous_refinement": True,
        "primes": list(primes),
        "cuts": list(cuts),
        "local_grid_radius": format(radius, "f"),
        "local_grid_step": format(step, "f"),
        "candidate_summaries": summaries,
        "tracked_minima": [asdict(row) for row in tracked],
        "controls": controls,
        "atlas_comparison": atlas,
    }


def write_csv(path: Path, payload: dict[str, Any]) -> None:
    rows = payload["tracked_minima"]
    if not rows:
        return
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Track finite Genuine-first resonances across cuts"
    )
    parser.add_argument("--candidates", required=True, help="comma-separated decimal grid seeds")
    parser.add_argument("--cuts", default="64,128,256,512,1024")
    parser.add_argument("--primes", default="3,5,7,11")
    parser.add_argument("--radius", default="0.001")
    parser.add_argument("--dt", default="0.00001")
    parser.add_argument("--atlas-sets", default="3;3,5;3,5,7;3,5,7,11")
    parser.add_argument("--json-output", type=Path, required=True)
    parser.add_argument("--csv-output", type=Path, default=None)
    args = parser.parse_args()
    payload = run_lab(
        _decimal_list(args.candidates),
        _int_list(args.cuts),
        scanner.parse_primes(args.primes),
        Decimal(args.radius),
        Decimal(args.dt),
        _atlas_list(args.atlas_sets),
    )
    args.json_output.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    if args.csv_output is not None:
        write_csv(args.csv_output, payload)
    print(
        json.dumps(
            {
                "json": str(args.json_output),
                "csv": str(args.csv_output) if args.csv_output else None,
                "candidate_count": len(payload["candidate_summaries"]),
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
