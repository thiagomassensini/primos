#!/usr/bin/env python3
"""Canonical finite-grid scanner for the Genuine-first real spectral operator.

The spectral parameter is a real number ``t``. Complex numbers are used only
as the phase/amplitude carrier of

    psi_t(n) = n^(-1/2) exp(-i t log n).

The canonical result is a grid resonance: an integer index ``k`` and the exact
decimal coordinate ``t_min + k * dt``. Continuous local optimization is opt-in
and never replaces the finite-grid certificate.

This is a reproducible finite numerical audit, not an interval proof of an
infinite-volume zero. The exact algebraic identities defining the finite charts
are formalized separately in Lean 4.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import multiprocessing as mp
import platform
import time
from dataclasses import asdict, dataclass
from decimal import Decimal, ROUND_FLOOR, localcontext
from pathlib import Path
from typing import Any, Iterable, Sequence

import numpy as np
import scipy
from scipy.optimize import minimize_scalar
from scipy.signal import find_peaks

try:
    import cupy as cp

    HAS_CUPY = True
except Exception:
    cp = None
    HAS_CUPY = False


GRID_SCHEMA = "org.genuine.real-spectral-grid/v1"
DEFAULT_PRIMES = (3, 5, 7, 11)
FLOAT_TINY = np.finfo(np.float64).tiny


@dataclass(frozen=True)
class DecimalGrid:
    """Integer-indexed decimal grid with exact published coordinates."""

    t_min: Decimal
    t_max: Decimal
    step: Decimal
    count: int
    decimal_places: int

    @classmethod
    def from_strings(cls, t_min: str, t_max: str, step: str) -> "DecimalGrid":
        try:
            lower = Decimal(t_min)
            upper = Decimal(t_max)
            delta = Decimal(step)
        except Exception as exc:
            raise ValueError(f"invalid decimal grid: {exc}") from exc

        if not lower.is_finite() or not upper.is_finite() or not delta.is_finite():
            raise ValueError("t-min, t-max and dt must be finite decimals")
        if delta <= 0:
            raise ValueError("dt must be positive")
        if upper < lower:
            raise ValueError("t-max must be greater than or equal to t-min")

        with localcontext() as ctx:
            ctx.prec = max(50, len(t_min) + len(t_max) + len(step) + 16)
            steps_decimal = ((upper - lower) / delta).to_integral_value(
                rounding=ROUND_FLOOR
            )
        count = int(steps_decimal) + 1
        if count > np.iinfo(np.int64).max:
            raise ValueError("grid is too large for int64 indexing")

        decimal_places = max(
            0,
            -lower.as_tuple().exponent,
            -upper.as_tuple().exponent,
            -delta.as_tuple().exponent,
        )
        return cls(lower, upper, delta, count, decimal_places)

    def decimal_at(self, index: int) -> Decimal:
        if index < 0 or index >= self.count:
            raise IndexError(f"grid index {index} outside [0, {self.count})")
        return self.t_min + self.step * index

    def text_at(self, index: int) -> str:
        return f"{self.decimal_at(index):.{self.decimal_places}f}"

    def float_values(self) -> np.ndarray:
        # Integer multiplication avoids cumulative np.arange step drift.
        indices = np.arange(self.count, dtype=np.float64)
        return float(self.t_min) + float(self.step) * indices

    @property
    def actual_t_max(self) -> Decimal:
        return self.decimal_at(self.count - 1)


@dataclass(frozen=True)
class GridCandidate:
    rank: int
    grid_index: int
    t_decimal: str
    t_float_hex: str
    score: float
    left_score: float | None
    right_score: float | None
    scan_score: float


@dataclass(frozen=True)
class RefinedCandidate:
    grid_index: int
    grid_t_decimal: str
    refined_t: float
    refined_score: float


def is_prime(value: int) -> bool:
    if value < 2:
        return False
    if value % 2 == 0:
        return value == 2
    return all(value % divisor for divisor in range(3, math.isqrt(value) + 1, 2))


def parse_primes(text: str) -> tuple[int, ...]:
    try:
        values = tuple(int(part.strip()) for part in text.split(",") if part.strip())
    except ValueError as exc:
        raise ValueError("primes must be a comma-separated list of integers") from exc
    if not values:
        raise ValueError("at least one prime camera is required")
    if len(set(values)) != len(values):
        raise ValueError("prime cameras must be distinct")
    invalid = [p for p in values if p < 3 or p % 2 == 0 or not is_prime(p)]
    if invalid:
        raise ValueError(f"only odd prime cameras are accepted; invalid: {invalid}")
    return values


def build_prime_models(
    primes: Sequence[int], m_cut: int, xp: Any
) -> tuple[dict[str, Any], ...]:
    """Precompute amplitudes and logarithms for every prime camera."""
    if m_cut < 1:
        raise ValueError("m-cut must be at least 1")

    models: list[dict[str, Any]] = []
    for p in primes:
        half_range = (p - 1) // 2
        seeds = xp.arange(1, half_range + 1, dtype=xp.float64)
        radii = xp.arange(1, half_range + 1, dtype=xp.float64)[None, :]
        levels = xp.arange(1, m_cut + 1, dtype=xp.float64)[:, None]
        centers = p * levels
        centers_flat = centers[:, 0]
        models.append(
            {
                "p": xp.asarray(float(p), dtype=xp.float64),
                "seed_log": xp.log(seeds),
                "seed_amp": 1.0 / xp.sqrt(seeds),
                "center_log": xp.log(centers_flat),
                "center_amp": 1.0 / xp.sqrt(centers_flat),
                "minus_log": xp.log(centers - radii),
                "minus_amp": 1.0 / xp.sqrt(centers - radii),
                "plus_log": xp.log(centers + radii),
                "plus_amp": 1.0 / xp.sqrt(centers + radii),
                "coordinate_count": half_range * (m_cut + 1),
                "calibration_log": xp.log(xp.asarray(float(p), dtype=xp.float64)),
            }
        )
    return tuple(models)


def evaluate_operator_chunk(
    t_array: Sequence[float] | np.ndarray,
    prime_models: Sequence[dict[str, Any]],
    xp: Any = np,
) -> Any:
    """Evaluate the finite squared visibility at real frequencies ``t``.

    The returned score is

        |sum_e z_e|^2 / (N * sum_e |z_e|^2),

    where every seed and every local second difference is retained as a
    coordinate until the final scalar synthesis.
    """
    t = xp.asarray(t_array, dtype=xp.float64)
    if t.ndim != 1:
        raise ValueError("t_array must be one-dimensional")
    if not prime_models:
        raise ValueError("prime_models must not be empty")

    global_resultant = xp.zeros(t.shape[0], dtype=xp.complex128)
    global_energy = xp.zeros(t.shape[0], dtype=xp.float64)
    coordinate_count = 0
    camera_count = len(prime_models)
    camera_count_sq = camera_count * camera_count

    for model in prime_models:
        seed_states = xp.exp(-1j * xp.outer(t, model["seed_log"]))
        chart_sum = xp.dot(seed_states, model["seed_amp"])
        chart_energy = xp.full(
            t.shape[0],
            xp.dot(model["seed_amp"], model["seed_amp"]),
            dtype=xp.float64,
        )

        center_phase = xp.exp(-1j * xp.outer(t, model["center_log"]))
        minus_phase = xp.exp(
            -1j * (t[:, None, None] * model["minus_log"][None, :, :])
        )
        plus_phase = xp.exp(
            -1j * (t[:, None, None] * model["plus_log"][None, :, :])
        )
        local_curvature = (
            model["minus_amp"][None, :, :] * minus_phase
            - 2.0
            * model["center_amp"][None, :, None]
            * center_phase[:, :, None]
            + model["plus_amp"][None, :, :] * plus_phase
        )
        chart_sum += xp.sum(local_curvature, axis=(1, 2))
        chart_energy += xp.sum(xp.abs(local_curvature) ** 2, axis=(1, 2))

        chart_factor = 1.0 - xp.sqrt(model["p"]) * xp.exp(
            -1j * t * model["calibration_log"]
        )
        factor_energy = xp.abs(chart_factor) ** 2
        global_resultant += (chart_sum / chart_factor) / camera_count
        global_energy += chart_energy / (factor_energy * camera_count_sq)
        coordinate_count += model["coordinate_count"]

    return xp.abs(global_resultant) ** 2 / (coordinate_count * global_energy)


def _worker_scan(args: tuple[np.ndarray, Sequence[dict[str, Any]]]) -> np.ndarray:
    t_chunk, prime_models = args
    return evaluate_operator_chunk(t_chunk, prime_models, np)


def resolve_backend(requested: str, workload_units: int) -> tuple[Any, str]:
    if requested == "cpu":
        return np, "CPU"
    if requested == "cuda":
        if not HAS_CUPY:
            raise RuntimeError("CUDA requested but CuPy is not installed")
        try:
            if cp.cuda.runtime.getDeviceCount() < 1:
                raise RuntimeError("no CUDA device is available")
        except Exception as exc:
            raise RuntimeError(f"failed to initialize CUDA/CuPy: {exc}") from exc
        return cp, "GPU"
    if HAS_CUPY and workload_units >= 8_000_000:
        try:
            if cp.cuda.runtime.getDeviceCount() > 0:
                return cp, "GPU(auto)"
        except Exception:
            pass
    return np, "CPU(auto)"


def scan_scores(
    ts: np.ndarray,
    primes: Sequence[int],
    m_cut: int,
    backend: str,
    workers: int | None,
    gpu_batch: int,
) -> tuple[np.ndarray, str, int, tuple[dict[str, Any], ...]]:
    scan_xp, backend_name = resolve_backend(
        backend, workload_units=len(ts) * m_cut * len(primes)
    )
    prime_models_np = build_prime_models(primes, m_cut, np)

    if scan_xp is np:
        worker_count = (
            min(8, max(1, mp.cpu_count() - 1))
            if workers is None
            else max(1, workers)
        )
        chunk_size = max(1, len(ts) // max(1, worker_count * 4))
        chunks = [ts[start : start + chunk_size] for start in range(0, len(ts), chunk_size)]
        tasks = [(chunk, prime_models_np) for chunk in chunks]
        if worker_count == 1:
            scores = np.concatenate([_worker_scan(task) for task in tasks])
        else:
            with mp.Pool(worker_count) as pool:
                scores = np.concatenate(pool.map(_worker_scan, tasks))
        return scores, backend_name, worker_count, prime_models_np

    worker_count = 1
    prime_models_gpu = build_prime_models(primes, m_cut, scan_xp)
    batch_size = max(1, int(gpu_batch))
    while True:
        try:
            scores = np.empty(ts.shape[0], dtype=np.float64)
            for start in range(0, len(ts), batch_size):
                chunk = ts[start : start + batch_size]
                scores[start : start + len(chunk)] = cp.asnumpy(
                    evaluate_operator_chunk(chunk, prime_models_gpu, scan_xp)
                )
            cp.cuda.Stream.null.synchronize()
            return scores, backend_name, worker_count, prime_models_np
        except Exception as exc:
            is_oom = "OutOfMemoryError" in str(type(exc)) or "OutOfMemoryError" in str(exc)
            if not is_oom or batch_size <= 2048:
                raise
            batch_size //= 2
            cp.get_default_memory_pool().free_all_blocks()


def detect_grid_candidates(
    scores: np.ndarray, prominence: float
) -> tuple[np.ndarray, dict[str, np.ndarray]]:
    log_visibility = -np.log10(np.maximum(scores, FLOAT_TINY))
    return find_peaks(log_visibility, prominence=prominence)


def canonicalize_candidates_on_cpu(
    peak_indices: Iterable[int],
    ts: np.ndarray,
    prime_models_np: Sequence[dict[str, Any]],
) -> list[tuple[int, float, float | None, float | None]]:
    """Re-evaluate every peak and its two neighbors with NumPy float64."""
    candidates: dict[int, tuple[float, float | None, float | None]] = {}
    count = len(ts)
    for raw_index in peak_indices:
        neighborhood = sorted(
            index
            for index in (int(raw_index) - 1, int(raw_index), int(raw_index) + 1)
            if 0 <= index < count
        )
        neighborhood_scores = np.asarray(
            evaluate_operator_chunk(ts[neighborhood], prime_models_np, np),
            dtype=np.float64,
        )
        index = neighborhood[int(np.argmin(neighborhood_scores))]
        witness_indices = [
            candidate
            for candidate in (index - 1, index, index + 1)
            if 0 <= candidate < count
        ]
        witness_scores = np.asarray(
            evaluate_operator_chunk(ts[witness_indices], prime_models_np, np),
            dtype=np.float64,
        )
        score_by_index = dict(zip(witness_indices, witness_scores))
        center_score = float(score_by_index[index])
        left_score = float(score_by_index[index - 1]) if index - 1 in score_by_index else None
        right_score = float(score_by_index[index + 1]) if index + 1 in score_by_index else None
        if left_score is not None and center_score > left_score:
            continue
        if right_score is not None and center_score > right_score:
            continue
        candidates[index] = (center_score, left_score, right_score)
    return [(index, *candidates[index]) for index in sorted(candidates)]


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def package_versions() -> dict[str, str | None]:
    return {
        "python": platform.python_version(),
        "numpy": np.__version__,
        "scipy": scipy.__version__,
        "cupy": getattr(cp, "__version__", None) if HAS_CUPY else None,
    }


def write_certificate(
    path: Path,
    *,
    grid: DecimalGrid,
    primes: Sequence[int],
    m_cut: int,
    threshold: float | None,
    prominence: float,
    backend_name: str,
    workers: int,
    elapsed: float,
    raw_peak_indices: Sequence[int],
    candidates: Sequence[GridCandidate],
    discarded: Sequence[dict[str, Any]],
    refined: Sequence[RefinedCandidate],
    refinement_requested: bool,
    script_path: Path,
) -> None:
    payload: dict[str, Any] = {
        "schema": GRID_SCHEMA,
        "status": "FINITE_NUMERICAL_GRID_AUDIT",
        "no_refinement_is_canonical": True,
        "grid": {
            "t_min": format(grid.t_min, "f"),
            "requested_t_max": format(grid.t_max, "f"),
            "actual_t_max": format(grid.actual_t_max, "f"),
            "dt": format(grid.step, "f"),
            "count": grid.count,
            "coordinate_rule": "t_k = t_min + k * dt",
        },
        "operator": {
            "primes": list(primes),
            "m_cut": m_cut,
            "threshold": threshold,
            "prominence_log10": prominence,
            "score": "abs(sum_e z_e)^2 / (N * sum_e abs(z_e)^2)",
        },
        "selection": {
            "scan_backend": backend_name,
            "published_candidate_scores_backend": "CPU/NumPy float64",
            "workers": workers,
            "raw_peak_count": len(raw_peak_indices),
            "kept_count": len(candidates),
            "discarded_count": len(discarded),
            "refinement_requested": refinement_requested,
        },
        "candidates": [asdict(candidate) for candidate in candidates],
        "discarded": list(discarded),
        "refined_noncanonical": [asdict(candidate) for candidate in refined],
        "runtime": {
            "elapsed_seconds": elapsed,
            "versions": package_versions(),
            "script_sha256": file_sha256(script_path),
        },
    }
    path.write_text(
        json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Canonical real-spectral finite-grid scanner (CPU/GPU)"
    )
    parser.add_argument("--t-min", default="10.0", help="exact decimal lower bound")
    parser.add_argument("--t-max", default="50.0", help="exact decimal upper bound")
    parser.add_argument("--dt", default="0.005", help="exact decimal grid spacing")
    parser.add_argument("--m-cut", type=int, default=128, help="finite geometric depth")
    parser.add_argument(
        "--primes",
        default=",".join(map(str, DEFAULT_PRIMES)),
        help="comma-separated odd prime cameras",
    )
    parser.add_argument(
        "--threshold",
        type=float,
        default=1e-6,
        help="maximum CPU-rechecked score; negative disables the filter",
    )
    parser.add_argument(
        "--prominence",
        type=float,
        default=0.8,
        help="prominence of valleys in -log10(score)",
    )
    parser.add_argument(
        "--backend", choices=("auto", "cpu", "cuda"), default="auto"
    )
    parser.add_argument("--workers", type=int, default=None)
    parser.add_argument("--gpu-batch", type=int, default=8192)
    refinement = parser.add_mutually_exclusive_group()
    refinement.add_argument(
        "--refine",
        action="store_true",
        help="also run noncanonical local continuous minimization",
    )
    refinement.add_argument(
        "--no-refine",
        action="store_false",
        dest="refine",
        help="compatibility flag; grid-only mode is already the default",
    )
    parser.set_defaults(refine=False)
    parser.add_argument("--json-output", type=Path, default=None)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        grid = DecimalGrid.from_strings(args.t_min, args.t_max, args.dt)
        primes = parse_primes(args.primes)
    except ValueError as exc:
        parser.error(str(exc))
    if args.m_cut < 1:
        parser.error("m-cut must be at least 1")
    if args.prominence < 0:
        parser.error("prominence must be nonnegative")
    threshold = None if args.threshold is not None and args.threshold < 0 else args.threshold

    ts = grid.float_values()
    print("=" * 86)
    print(" GENUINE-FIRST REAL SPECTRAL OPERATOR — CANONICAL FINITE GRID")
    print("=" * 86)
    print(f" Real spectrum       : {grid.text_at(0)} <= t <= {grid.text_at(grid.count - 1)}")
    print(f" Exact grid law      : t_k = {format(grid.t_min, 'f')} + k * {format(grid.step, 'f')}")
    print(f" Grid points         : {grid.count}")
    print(f" Prime cameras       : {primes}")
    print(f" Geometric cut (M)   : {args.m_cut}")
    print(f" Refinement          : {'requested (noncanonical)' if args.refine else 'disabled (canonical)'}")
    print("-" * 86)

    started = time.time()
    scores, backend_name, workers, prime_models_np = scan_scores(
        ts, primes, args.m_cut, args.backend, args.workers, args.gpu_batch
    )
    raw_peak_indices, _properties = detect_grid_candidates(scores, args.prominence)
    cpu_candidates = canonicalize_candidates_on_cpu(raw_peak_indices, ts, prime_models_np)

    kept: list[GridCandidate] = []
    discarded: list[dict[str, Any]] = []
    for index, center_score, left_score, right_score in cpu_candidates:
        entry = {
            "grid_index": int(index),
            "t_decimal": grid.text_at(int(index)),
            "score": center_score,
            "scan_score": float(scores[index]),
        }
        if threshold is not None and center_score > threshold:
            discarded.append(entry)
            continue
        kept.append(
            GridCandidate(
                rank=len(kept) + 1,
                grid_index=int(index),
                t_decimal=grid.text_at(int(index)),
                t_float_hex=float(ts[index]).hex(),
                score=center_score,
                left_score=left_score,
                right_score=right_score,
                scan_score=float(scores[index]),
            )
        )

    refined: list[RefinedCandidate] = []
    if args.refine:
        step_float = float(grid.step)
        for candidate in kept:
            t_grid = float(ts[candidate.grid_index])
            result = minimize_scalar(
                lambda t_value: float(
                    evaluate_operator_chunk(
                        np.asarray([t_value], dtype=np.float64), prime_models_np, np
                    )[0]
                ),
                bounds=(t_grid - step_float, t_grid + step_float),
                method="bounded",
            )
            refined.append(
                RefinedCandidate(
                    grid_index=candidate.grid_index,
                    grid_t_decimal=candidate.t_decimal,
                    refined_t=float(result.x),
                    refined_score=float(result.fun),
                )
            )

    elapsed = time.time() - started
    print(f" Scan backend        : {backend_name}")
    print(f" CPU workers         : {workers}")
    print(f" Raw discrete valleys: {len(raw_peak_indices)}")
    print(f" CPU local minima    : {len(cpu_candidates)}")
    print(f" Published           : {len(kept)}")
    print(f" Discarded by score  : {len(discarded)}")
    print("-" * 86)
    print(
        f" {'#':>3} | {'grid k':>10} | {'exact decimal t_k':>20} | "
        f"{'CPU score':>13} | {'left':>13} | {'right':>13}"
    )
    print("-" * 86)
    for candidate in kept:
        left = "-" if candidate.left_score is None else f"{candidate.left_score:.6e}"
        right = "-" if candidate.right_score is None else f"{candidate.right_score:.6e}"
        print(
            f" {candidate.rank:3d} | {candidate.grid_index:10d} | "
            f"{candidate.t_decimal:>20} | {candidate.score:13.6e} | "
            f"{left:>13} | {right:>13}"
        )

    if refined:
        print("-" * 86)
        print(" Noncanonical refinements (never replace the grid certificate)")
        for rank, item in enumerate(refined, 1):
            print(
                f" {rank:3d} | grid {item.grid_t_decimal} -> "
                f"{item.refined_t:.14f} | {item.refined_score:.6e}"
            )

    print("=" * 86)
    print(f" Elapsed             : {elapsed:.3f} seconds")
    print(" Canonical statement : every published t is the exact decimal t_min + k*dt")
    print(" Numerical caveat    : transcendental scores are float64 evaluations of that grid")
    print("=" * 86)

    if args.json_output is not None:
        write_certificate(
            args.json_output,
            grid=grid,
            primes=primes,
            m_cut=args.m_cut,
            threshold=threshold,
            prominence=args.prominence,
            backend_name=backend_name,
            workers=workers,
            elapsed=elapsed,
            raw_peak_indices=[int(index) for index in raw_peak_indices],
            candidates=kept,
            discarded=discarded,
            refined=refined,
            refinement_requested=args.refine,
            script_path=Path(__file__),
        )
        print(f"Certificate written to {args.json_output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
