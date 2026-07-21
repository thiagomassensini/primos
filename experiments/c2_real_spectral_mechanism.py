#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any, Sequence

import numpy as np

import c2_real_spectral_grid as scanner


def _safe_cosine(first: complex, second: complex) -> float | None:
    denom = abs(first) * abs(second)
    if denom == 0.0:
        return None
    return float(np.real(np.conj(first) * second) / denom)


def _visibility(resultant: complex, energy: float, count: int) -> float:
    if count <= 0 or not energy > 0.0:
        return math.nan
    return float(abs(resultant) ** 2 / (count * energy))


def evaluate_mechanism(t: float, primes: Sequence[int], m_cut: int) -> dict[str, Any]:
    """Reconstruct the full finite coordinate state before scalar synthesis.

    The report separates the dimension-normalized score from the dimension-free
    residual, the visible and blind energies, the seed/bracket channels and the
    residuals of each prime camera. It is a finite float64 audit, not an interval
    proof of an infinite-volume zero.
    """
    if not math.isfinite(t):
        raise ValueError("t must be finite")
    models = scanner.build_prime_models(tuple(primes), m_cut, np)
    camera_count = len(models)
    all_coordinates: list[np.ndarray] = []
    cameras: list[dict[str, Any]] = []
    global_seed = 0j
    global_bracket = 0j

    for prime, model in zip(primes, models):
        seed_coordinates_raw = model["seed_amp"] * np.exp(-1j * t * model["seed_log"])
        center_phase = np.exp(-1j * t * model["center_log"])
        minus_phase = np.exp(-1j * t * model["minus_log"])
        plus_phase = np.exp(-1j * t * model["plus_log"])
        curvature_raw = (
            model["minus_amp"] * minus_phase
            - 2.0 * model["center_amp"][:, None] * center_phase[:, None]
            + model["plus_amp"] * plus_phase
        )
        factor = 1.0 - np.sqrt(model["p"]) * np.exp(
            -1j * t * model["calibration_log"]
        )
        normalization = factor * camera_count
        seed_coordinates = np.asarray(
            seed_coordinates_raw / normalization, dtype=np.complex128
        )
        bracket_coordinates = np.asarray(
            curvature_raw.reshape(-1) / normalization, dtype=np.complex128
        )
        coordinates = np.concatenate((seed_coordinates, bracket_coordinates))
        all_coordinates.append(coordinates)

        seed_resultant = complex(seed_coordinates.sum())
        bracket_resultant = complex(bracket_coordinates.sum())
        camera_resultant = seed_resultant + bracket_resultant
        camera_energy = float(np.vdot(coordinates, coordinates).real)
        cameras.append(
            {
                "prime": int(prime),
                "coordinate_count": int(coordinates.size),
                "factor": {"real": float(factor.real), "imag": float(factor.imag)},
                "seed_resultant": {
                    "real": seed_resultant.real,
                    "imag": seed_resultant.imag,
                },
                "bracket_resultant": {
                    "real": bracket_resultant.real,
                    "imag": bracket_resultant.imag,
                },
                "resultant": {
                    "real": camera_resultant.real,
                    "imag": camera_resultant.imag,
                },
                "energy": camera_energy,
                "visibility": _visibility(
                    camera_resultant, camera_energy, int(coordinates.size)
                ),
                "seed_bracket_cosine": _safe_cosine(
                    seed_resultant, bracket_resultant
                ),
                "seed_bracket_magnitude_ratio": (
                    float(abs(seed_resultant) / abs(bracket_resultant))
                    if abs(bracket_resultant) > 0.0
                    else None
                ),
            }
        )
        global_seed += seed_resultant
        global_bracket += bracket_resultant

    coordinates = np.concatenate(all_coordinates)
    count = int(coordinates.size)
    resultant = complex(coordinates.sum())
    total_energy = float(np.vdot(coordinates, coordinates).real)
    visible_energy = float(abs(resultant) ** 2 / count)
    blind_energy = float(max(0.0, total_energy - visible_energy))
    score = visible_energy / total_energy
    dimension_free_residual = float(abs(resultant) ** 2 / total_energy)
    visible_angle_degrees = float(
        math.degrees(math.acos(math.sqrt(min(1.0, max(0.0, score)))))
    )

    projection = np.full(count, resultant / count, dtype=np.complex128)
    projected_twice = np.full(count, projection.sum() / count, dtype=np.complex128)
    probe = np.exp(1j * np.sqrt(2.0) * np.arange(count, dtype=np.float64))
    probe /= np.linalg.norm(probe)
    projected_probe = np.full(count, probe.sum() / count, dtype=np.complex128)
    idempotence_defect = float(np.linalg.norm(projected_twice - projection))
    self_adjoint_defect = float(
        abs(np.vdot(projection, probe) - np.vdot(coordinates, projected_probe))
    )

    camera_resultants = np.asarray(
        [
            entry["resultant"]["real"] + 1j * entry["resultant"]["imag"]
            for entry in cameras
        ],
        dtype=np.complex128,
    )
    camera_residual_energy = float(np.vdot(camera_resultants, camera_resultants).real)
    camera_alignment = (
        float(
            abs(camera_resultants.sum()) ** 2
            / (camera_count * camera_residual_energy)
        )
        if camera_residual_energy > 0.0
        else math.nan
    )

    scanner_score = float(
        np.asarray(
            scanner.evaluate_operator_chunk(np.array([t]), models, np),
            dtype=np.float64,
        )[0]
    )
    return {
        "status": "FINITE_NUMERICAL_MECHANISM_AUDIT",
        "t": float(t),
        "primes": [int(p) for p in primes],
        "m_cut": int(m_cut),
        "coordinate_count": count,
        "resultant": {"real": resultant.real, "imag": resultant.imag},
        "seed_resultant": {"real": global_seed.real, "imag": global_seed.imag},
        "bracket_resultant": {
            "real": global_bracket.real,
            "imag": global_bracket.imag,
        },
        "total_energy": total_energy,
        "visible_energy": visible_energy,
        "blind_energy": blind_energy,
        "blind_fraction": blind_energy / total_energy,
        "score": score,
        "scanner_score": scanner_score,
        "score_consistency_error": abs(score - scanner_score),
        "dimension_free_residual": dimension_free_residual,
        "visible_angle_degrees": visible_angle_degrees,
        "seed_bracket_cosine": _safe_cosine(global_seed, global_bracket),
        "seed_bracket_magnitude_ratio": (
            float(abs(global_seed) / abs(global_bracket))
            if abs(global_bracket) > 0.0
            else None
        ),
        "camera_residual_alignment": camera_alignment,
        "projection_idempotence_defect": idempotence_defect,
        "projection_self_adjoint_defect": self_adjoint_defect,
        "cameras": cameras,
    }


def parse_primes(text: str) -> tuple[int, ...]:
    return scanner.parse_primes(text)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Finite mechanism audit for the Genuine-first real spectral readout"
    )
    parser.add_argument("--t", type=float, required=True)
    parser.add_argument("--m-cut", type=int, default=1024)
    parser.add_argument("--primes", default="3,5,7,11")
    parser.add_argument("--json-output", type=Path, default=None)
    args = parser.parse_args()
    result = evaluate_mechanism(
        args.t, parse_primes(args.primes), args.m_cut
    )
    text = json.dumps(result, indent=2, sort_keys=True)
    print(text)
    if args.json_output is not None:
        args.json_output.write_text(text + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
