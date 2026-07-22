#!/usr/bin/env python3
"""Empirical Genuine-first operator written entirely over real two-vectors.

The canonical state is

    psi_t(n) = n**(-1/2) R(-t log n) e_1,

where R(theta) is a 2 x 2 real rotation matrix and e_1 = (1, 0).  Every
prime camera applies a centered second-difference bracket and the real camera
calibration

    (I - sqrt(p) R(-t log p))**(-1).

The scan never constructs a complex scalar or accepts a complex parameter.
The accelerated kernel contracts the first column of the same rotation matrix
instead of materializing millions of 2 x 2 matrices.  ``rotation_matrix`` is
kept explicit and tested against that contraction.

This is a finite numerical laboratory.  It reports finite-grid resonances and
finite Green/boundary ledgers; it is not an interval proof of an infinite
operator statement.
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


SCHEMA = "org.genuine.real-rotation-operator/v1"
DEFAULT_CAMERAS = (3, 5, 7, 11)
FLOAT_TINY = np.finfo(np.float64).tiny
SHOW_CHOICES = frozenset(
    {"score", "energy", "cameras", "green", "boundary", "return", "all"}
)


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
            raise ValueError("tmin, tmax and grid must be finite decimals")
        if delta <= 0:
            raise ValueError("grid spacing must be positive")
        if upper < lower:
            raise ValueError("tmax must be greater than or equal to tmin")

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


def parse_cameras(text: str) -> tuple[int, ...]:
    try:
        values = tuple(int(part.strip()) for part in text.split(",") if part.strip())
    except ValueError as exc:
        raise ValueError("cameras must be a comma-separated list of integers") from exc
    return validate_cameras(values)


def validate_cameras(values: Sequence[int]) -> tuple[int, ...]:
    cameras = tuple(int(value) for value in values)
    if not cameras:
        raise ValueError("at least one prime camera is required")
    if len(set(cameras)) != len(cameras):
        raise ValueError("prime cameras must be distinct")
    invalid = [p for p in cameras if p < 3 or p % 2 == 0 or not is_prime(p)]
    if invalid:
        raise ValueError(f"only odd prime cameras are accepted; invalid: {invalid}")
    return cameras


def parse_show(text: str) -> frozenset[str]:
    values = {part.strip().lower() for part in text.split(",") if part.strip()}
    if not values:
        values = {"score"}
    invalid = values - SHOW_CHOICES
    if invalid:
        raise ValueError(
            "unknown --show channel(s): "
            + ", ".join(sorted(invalid))
            + "; choose from "
            + ", ".join(sorted(SHOW_CHOICES))
        )
    if "all" in values:
        values = set(SHOW_CHOICES) - {"all"}
    values.add("score")
    return frozenset(values)


def rotation_matrix(angle: Any, xp: Any = np) -> Any:
    """Return the standard real matrix R(angle), vectorized over ``angle``."""
    theta = xp.asarray(angle, dtype=xp.float64)
    cosine = xp.cos(theta)
    sine = xp.sin(theta)
    first_row = xp.stack((cosine, -sine), axis=-1)
    second_row = xp.stack((sine, cosine), axis=-1)
    return xp.stack((first_row, second_row), axis=-2)


def rotate_unit_axis(angle: Any, xp: Any = np) -> Any:
    """Compute R(angle)e_1 without allocating the unused matrix column."""
    theta = xp.asarray(angle, dtype=xp.float64)
    return xp.stack((xp.cos(theta), xp.sin(theta)), axis=-1)


def real_spectral_state(t: float, size: int, xp: Any = np) -> Any:
    """Return n^(-1/2) R(-t log n)e_1 for 1 <= n <= size."""
    if size < 2:
        raise ValueError("size must be at least 2")
    if not math.isfinite(float(t)):
        raise ValueError("t must be finite")
    n = xp.arange(1, size + 1, dtype=xp.float64)
    amplitudes = 1.0 / xp.sqrt(n)
    return amplitudes[:, None] * rotate_unit_axis(-float(t) * xp.log(n), xp)


def _states_from_log(t: Any, logs: Any, amplitudes: Any, xp: Any) -> Any:
    """Batch version of n^(-1/2)R(-t log n)e_1."""
    frequencies = xp.asarray(t, dtype=xp.float64)
    reshape = (frequencies.shape[0],) + (1,) * logs.ndim
    angles = -frequencies.reshape(reshape) * logs[None, ...]
    return amplitudes[None, ..., None] * rotate_unit_axis(angles, xp)


def calibration_matrix(t: Any, p: int, xp: Any = np) -> Any:
    """Return I - sqrt(p) R(-t log p) over the real plane."""
    frequencies = xp.asarray(t, dtype=xp.float64)
    rotation = rotation_matrix(-frequencies * math.log(p), xp)
    identity = xp.eye(2, dtype=xp.float64)
    return identity - math.sqrt(p) * rotation


def inverse_calibration_matrix(t: Any, p: int, xp: Any = np) -> Any:
    """Return the explicit inverse of the real prime-camera calibration."""
    frequencies = xp.asarray(t, dtype=xp.float64)
    theta = frequencies * math.log(p)
    u = 1.0 - math.sqrt(p) * xp.cos(theta)
    v = math.sqrt(p) * xp.sin(theta)
    determinant = u * u + v * v
    first_row = xp.stack((u, v), axis=-1)
    second_row = xp.stack((-v, u), axis=-1)
    return xp.stack((first_row, second_row), axis=-2) / determinant[..., None, None]


def apply_inverse_calibration(
    vectors: Any, t: Any, p: int, xp: Any = np
) -> Any:
    """Apply (I - sqrt(p)R(-t log p))^-1 without matrix allocation."""
    frequencies = xp.asarray(t, dtype=xp.float64)
    theta = frequencies * math.log(p)
    u = 1.0 - math.sqrt(p) * xp.cos(theta)
    v = math.sqrt(p) * xp.sin(theta)
    determinant = u * u + v * v

    x = vectors[..., 0]
    y = vectors[..., 1]
    while u.ndim < x.ndim:
        u = u[..., None]
        v = v[..., None]
        determinant = determinant[..., None]
    return xp.stack(
        ((u * x + v * y) / determinant, (-v * x + u * y) / determinant),
        axis=-1,
    )


def calibration_determinant(t: Any, p: int, xp: Any = np) -> Any:
    frequencies = xp.asarray(t, dtype=xp.float64)
    theta = frequencies * math.log(p)
    u = 1.0 - math.sqrt(p) * xp.cos(theta)
    v = math.sqrt(p) * xp.sin(theta)
    return u * u + v * v


def build_prime_models(
    cameras: Sequence[int], cutoff: int, xp: Any = np
) -> tuple[dict[str, Any], ...]:
    """Precompute the finite bracket chart for every selected camera."""
    if cutoff < 1:
        raise ValueError("cutoff must be at least 1")
    cameras = validate_cameras(cameras)

    models: list[dict[str, Any]] = []
    for p in cameras:
        half_range = (p - 1) // 2
        seeds = xp.arange(1, half_range + 1, dtype=xp.float64)
        radii = xp.arange(1, half_range + 1, dtype=xp.float64)[None, :]
        levels = xp.arange(1, cutoff + 1, dtype=xp.float64)[:, None]
        centers = p * levels
        centers_flat = centers[:, 0]
        models.append(
            {
                "p": p,
                "seed_log": xp.log(seeds),
                "seed_amp": 1.0 / xp.sqrt(seeds),
                "center_log": xp.log(centers_flat),
                "center_amp": 1.0 / xp.sqrt(centers_flat),
                "minus_log": xp.log(centers - radii),
                "minus_amp": 1.0 / xp.sqrt(centers - radii),
                "plus_log": xp.log(centers + radii),
                "plus_amp": 1.0 / xp.sqrt(centers + radii),
                "coordinate_count": half_range * (cutoff + 1),
            }
        )
    return tuple(models)


def evaluate_operator_chunk(
    t_array: Sequence[float] | np.ndarray,
    prime_models: Sequence[dict[str, Any]],
    xp: Any = np,
    *,
    return_balance: bool = False,
) -> Any:
    """Evaluate the real-vector operator on a one-dimensional frequency batch.

    The score is

        ||sum_e z_e||^2 / (N sum_e ||z_e||^2),

    with every seed and local bracket coordinate retained until synthesis.
    """
    t = xp.asarray(t_array, dtype=xp.float64)
    if t.ndim != 1:
        raise ValueError("t_array must be one-dimensional")
    if not prime_models:
        raise ValueError("prime_models must not be empty")

    global_resultant = xp.zeros((t.shape[0], 2), dtype=xp.float64)
    global_energy = xp.zeros(t.shape[0], dtype=xp.float64)
    coordinate_count = 0
    camera_count = len(prime_models)
    camera_count_sq = camera_count * camera_count

    for model in prime_models:
        seed_states = _states_from_log(t, model["seed_log"], model["seed_amp"], xp)
        seed_sum = xp.sum(seed_states, axis=1)
        seed_energy = xp.full(
            t.shape[0],
            xp.sum(model["seed_amp"] * model["seed_amp"]),
            dtype=xp.float64,
        )

        center_states = _states_from_log(
            t, model["center_log"], model["center_amp"], xp
        )
        minus_states = _states_from_log(
            t, model["minus_log"], model["minus_amp"], xp
        )
        plus_states = _states_from_log(
            t, model["plus_log"], model["plus_amp"], xp
        )
        local_bracket = (
            minus_states - 2.0 * center_states[:, :, None, :] + plus_states
        )
        bracket_sum = xp.sum(local_bracket, axis=(1, 2))
        bracket_energy = xp.sum(local_bracket * local_bracket, axis=(1, 2, 3))

        raw_resultant = seed_sum + bracket_sum
        camera_resultant = apply_inverse_calibration(
            raw_resultant, t, int(model["p"]), xp
        ) / camera_count
        determinant = calibration_determinant(t, int(model["p"]), xp)

        global_resultant += camera_resultant
        global_energy += (seed_energy + bracket_energy) / (
            determinant * camera_count_sq
        )
        coordinate_count += int(model["coordinate_count"])

    resultant_norm_sq = xp.sum(global_resultant * global_resultant, axis=1)
    denominator = coordinate_count * global_energy
    score = resultant_norm_sq / xp.maximum(
        denominator, xp.asarray(np.finfo(np.float64).tiny, dtype=xp.float64)
    )
    if not return_balance:
        return score
    return {
        "score": score,
        "resultant": global_resultant,
        "resultant_norm_sq": resultant_norm_sq,
        "total_energy": global_energy,
        "coordinate_count": coordinate_count,
    }


def _worker_scan(args: tuple[np.ndarray, Sequence[dict[str, Any]]]) -> np.ndarray:
    t_chunk, prime_models = args
    return np.asarray(evaluate_operator_chunk(t_chunk, prime_models, np))


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
    cameras: Sequence[int],
    cutoff: int,
    backend: str,
    workers: int | None,
    gpu_batch: int,
) -> tuple[np.ndarray, str, int, tuple[dict[str, Any], ...]]:
    scan_xp, backend_name = resolve_backend(
        backend, workload_units=len(ts) * cutoff * len(cameras)
    )
    prime_models_np = build_prime_models(cameras, cutoff, np)

    if scan_xp is np:
        worker_count = (
            min(8, max(1, mp.cpu_count() - 1))
            if workers is None
            else max(1, workers)
        )
        chunk_size = max(1, len(ts) // max(1, worker_count * 4))
        chunks = [
            ts[start : start + chunk_size]
            for start in range(0, len(ts), chunk_size)
        ]
        tasks = [(chunk, prime_models_np) for chunk in chunks]
        if worker_count == 1:
            scores = np.concatenate([_worker_scan(task) for task in tasks])
        else:
            with mp.Pool(worker_count) as pool:
                scores = np.concatenate(pool.map(_worker_scan, tasks))
        return scores, backend_name, worker_count, prime_models_np

    worker_count = 1
    prime_models_gpu = build_prime_models(cameras, cutoff, scan_xp)
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
            if not is_oom or batch_size <= 256:
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
    """Re-evaluate each peak and its neighbors in NumPy float64."""
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
        left_score = (
            float(score_by_index[index - 1]) if index - 1 in score_by_index else None
        )
        right_score = (
            float(score_by_index[index + 1]) if index + 1 in score_by_index else None
        )
        if left_score is not None and center_score > left_score:
            continue
        if right_score is not None and center_score > right_score:
            continue
        candidates[index] = (center_score, left_score, right_score)
    return [(index, *candidates[index]) for index in sorted(candidates)]


def _vector_norm(vector: np.ndarray) -> float:
    return float(np.sqrt(np.dot(vector, vector)))


def _safe_cosine(first: np.ndarray, second: np.ndarray) -> float | None:
    denominator = _vector_norm(first) * _vector_norm(second)
    if denominator == 0.0:
        return None
    return float(np.dot(first, second) / denominator)


def _visibility(resultant: np.ndarray, energy: float, count: int) -> float:
    if count <= 0 or not energy > 0.0:
        return math.nan
    return float(np.dot(resultant, resultant) / (count * energy))


def _camera_coordinates(
    t: float, model: dict[str, Any], camera_count: int
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    seed_raw = model["seed_amp"][:, None] * rotate_unit_axis(
        -t * model["seed_log"], np
    )
    center = model["center_amp"][:, None] * rotate_unit_axis(
        -t * model["center_log"], np
    )
    minus = model["minus_amp"][..., None] * rotate_unit_axis(
        -t * model["minus_log"], np
    )
    plus = model["plus_amp"][..., None] * rotate_unit_axis(
        -t * model["plus_log"], np
    )
    bracket_raw = minus - 2.0 * center[:, None, :] + plus
    seed = apply_inverse_calibration(seed_raw, t, int(model["p"]), np) / camera_count
    bracket = (
        apply_inverse_calibration(
            bracket_raw.reshape(-1, 2), t, int(model["p"]), np
        )
        / camera_count
    )
    return seed, bracket, np.concatenate((seed, bracket), axis=0)


def evaluate_mechanism(
    t: float, cameras: Sequence[int], cutoff: int
) -> dict[str, Any]:
    """Open the coordinate state before the final scalar visibility readout."""
    if not math.isfinite(t):
        raise ValueError("t must be finite")
    models = build_prime_models(tuple(cameras), cutoff, np)
    camera_count = len(models)
    all_coordinates: list[np.ndarray] = []
    camera_reports: list[dict[str, Any]] = []
    global_seed = np.zeros(2, dtype=np.float64)
    global_bracket = np.zeros(2, dtype=np.float64)

    for model in models:
        p = int(model["p"])
        seed_coordinates, bracket_coordinates, coordinates = _camera_coordinates(
            t, model, camera_count
        )
        all_coordinates.append(coordinates)

        seed_resultant = np.sum(seed_coordinates, axis=0)
        bracket_resultant = np.sum(bracket_coordinates, axis=0)
        camera_resultant = seed_resultant + bracket_resultant
        camera_energy = float(np.sum(coordinates * coordinates))
        matrix = np.asarray(calibration_matrix(t, p, np), dtype=np.float64)
        inverse = np.asarray(inverse_calibration_matrix(t, p, np), dtype=np.float64)
        camera_reports.append(
            {
                "prime": p,
                "coordinate_count": int(coordinates.shape[0]),
                "calibration_matrix": matrix.tolist(),
                "inverse_calibration_matrix": inverse.tolist(),
                "calibration_inverse_error": float(
                    np.linalg.norm(matrix @ inverse - np.eye(2))
                ),
                "seed_resultant": seed_resultant.tolist(),
                "bracket_resultant": bracket_resultant.tolist(),
                "resultant": camera_resultant.tolist(),
                "energy": camera_energy,
                "visibility": _visibility(
                    camera_resultant, camera_energy, int(coordinates.shape[0])
                ),
                "seed_bracket_cosine": _safe_cosine(
                    seed_resultant, bracket_resultant
                ),
                "seed_bracket_magnitude_ratio": (
                    _vector_norm(seed_resultant) / _vector_norm(bracket_resultant)
                    if _vector_norm(bracket_resultant) > 0.0
                    else None
                ),
            }
        )
        global_seed += seed_resultant
        global_bracket += bracket_resultant

    coordinates = np.concatenate(all_coordinates, axis=0)
    count = int(coordinates.shape[0])
    resultant = np.sum(coordinates, axis=0)
    total_energy = float(np.sum(coordinates * coordinates))
    visible_energy = float(np.dot(resultant, resultant) / count)
    blind_energy = float(max(0.0, total_energy - visible_energy))
    score = visible_energy / total_energy
    dimension_free_residual = float(np.dot(resultant, resultant) / total_energy)
    visible_angle_degrees = float(
        math.degrees(math.acos(math.sqrt(min(1.0, max(0.0, score)))))
    )

    mean_coordinate = resultant / count
    projection = np.broadcast_to(mean_coordinate, coordinates.shape).copy()
    projected_twice = np.broadcast_to(
        np.mean(projection, axis=0), coordinates.shape
    ).copy()
    probe = rotate_unit_axis(
        math.sqrt(2.0) * np.arange(count, dtype=np.float64), np
    )
    probe /= math.sqrt(float(np.sum(probe * probe)))
    projected_probe = np.broadcast_to(np.mean(probe, axis=0), probe.shape).copy()
    idempotence_defect = float(np.linalg.norm(projected_twice - projection))
    self_adjoint_defect = float(
        abs(np.sum(projection * probe) - np.sum(coordinates * projected_probe))
    )

    camera_resultants = np.asarray(
        [entry["resultant"] for entry in camera_reports], dtype=np.float64
    )
    camera_residual_energy = float(np.sum(camera_resultants * camera_resultants))
    camera_alignment = (
        float(
            np.dot(np.sum(camera_resultants, axis=0), np.sum(camera_resultants, axis=0))
            / (camera_count * camera_residual_energy)
        )
        if camera_residual_energy > 0.0
        else math.nan
    )

    scanner_score = float(
        np.asarray(
            evaluate_operator_chunk(np.array([t]), models, np), dtype=np.float64
        )[0]
    )
    return {
        "status": "FINITE_REAL_VECTOR_MECHANISM_AUDIT",
        "t": float(t),
        "cameras": [int(p) for p in cameras],
        "cutoff": int(cutoff),
        "coordinate_count": count,
        "resultant": resultant.tolist(),
        "seed_resultant": global_seed.tolist(),
        "bracket_resultant": global_bracket.tolist(),
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
            _vector_norm(global_seed) / _vector_norm(global_bracket)
            if _vector_norm(global_bracket) > 0.0
            else None
        ),
        "camera_residual_alignment": camera_alignment,
        "projection_idempotence_defect": idempotence_defect,
        "projection_self_adjoint_defect": self_adjoint_defect,
        "camera_reports": camera_reports,
    }


def second_difference(values: np.ndarray) -> np.ndarray:
    if values.ndim != 2 or values.shape[1] != 2:
        raise ValueError("values must have shape (N, 2)")
    return values[2:] - 2.0 * values[1:-1] + values[:-2]


def green_return(curvature: np.ndarray, size: int) -> np.ndarray:
    """Triangular Green reconstruction with zero position and slope trace."""
    result = np.zeros((size, 2), dtype=np.float64)
    if curvature.size:
        result[2:] = np.cumsum(np.cumsum(curvature, axis=0), axis=0)
    return result


def affine_trace_return(a: np.ndarray, b: np.ndarray, size: int) -> np.ndarray:
    indices = np.arange(size, dtype=np.float64)[:, None]
    return a[None, :] + indices * b[None, :]


def _max_row_norm(values: np.ndarray) -> float:
    if values.size == 0:
        return 0.0
    return float(np.max(np.sqrt(np.sum(values * values, axis=-1))))


def audit_green_boundary_return(t: float, size: int) -> dict[str, Any]:
    """Audit f = G(Bf) + R(Tr f) and its polarized energy ledger."""
    state = np.asarray(real_spectral_state(t, size, np), dtype=np.float64)
    curvature = second_difference(state)
    trace_position = state[0]
    trace_slope = state[1] - state[0]
    green = green_return(curvature, size)
    boundary_return = affine_trace_return(trace_position, trace_slope, size)
    reconstructed = green + boundary_return

    reconstruction_error = _max_row_norm(state - reconstructed)
    green_curvature_error = _max_row_norm(second_difference(green) - curvature)
    trace_green_error = max(
        _vector_norm(green[0]), _vector_norm(green[1] - green[0])
    )
    boundary_curvature_error = _max_row_norm(second_difference(boundary_return))

    state_energy = float(np.sum(state * state))
    bracket_energy = float(np.sum(curvature * curvature))
    green_energy = float(np.sum(green * green))
    boundary_energy = float(np.sum(boundary_return * boundary_return))
    polarized_cross = float(2.0 * np.sum(green * boundary_return))
    reconstructed_energy = green_energy + boundary_energy + polarized_cross

    return {
        "status": "FINITE_REAL_GREEN_BOUNDARY_RETURN_AUDIT",
        "identity": "f = G(Bf) + R(Tr f)",
        "t": float(t),
        "size": int(size),
        "trace": {
            "position": trace_position.tolist(),
            "slope": trace_slope.tolist(),
        },
        "endpoints": {
            "state_left": state[0].tolist(),
            "state_right": state[-1].tolist(),
            "green_right": green[-1].tolist(),
            "boundary_return_right": boundary_return[-1].tolist(),
            "reconstructed_right": reconstructed[-1].tolist(),
        },
        "errors": {
            "max_reconstruction": reconstruction_error,
            "max_green_curvature": green_curvature_error,
            "trace_of_green": trace_green_error,
            "max_boundary_curvature": boundary_curvature_error,
        },
        "energy": {
            "state": state_energy,
            "bracket": bracket_energy,
            "green": green_energy,
            "boundary_return": boundary_energy,
            "polarized_cross_term": polarized_cross,
            "reconstructed": reconstructed_energy,
            "ledger_error": abs(state_energy - reconstructed_energy),
        },
    }


def _refine_candidate(
    index: int,
    ts: np.ndarray,
    prime_models_np: Sequence[dict[str, Any]],
) -> RefinedCandidate | None:
    if index <= 0 or index >= len(ts) - 1:
        return None

    def objective(value: float) -> float:
        return float(
            np.asarray(
                evaluate_operator_chunk(np.array([value]), prime_models_np, np),
                dtype=np.float64,
            )[0]
        )

    result = minimize_scalar(
        objective,
        bounds=(float(ts[index - 1]), float(ts[index + 1])),
        method="bounded",
        options={"xatol": max(1e-14, abs(ts[index + 1] - ts[index - 1]) * 1e-8)},
    )
    return RefinedCandidate(
        grid_index=index,
        grid_t_decimal="",
        refined_t=float(result.x),
        refined_score=float(result.fun),
    )


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def package_versions() -> dict[str, str | None]:
    return {
        "python": platform.python_version(),
        "numpy": np.__version__,
        "scipy": scipy.__version__,
        "cupy": getattr(cp, "__version__", None) if HAS_CUPY else None,
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Genuine-first real 2D rotation/bracket scanner (CPU/CuPy)"
    )
    parser.add_argument("--tmin", "--t-min", dest="tmin", default="10.0")
    parser.add_argument("--tmax", "--t-max", dest="tmax", default="50.0")
    parser.add_argument(
        "--grid", "--dt", dest="grid", default="0.005", help="exact decimal spacing"
    )
    parser.add_argument(
        "--cutoff", "--m-cut", dest="cutoff", type=int, default=128
    )
    cameras = parser.add_mutually_exclusive_group()
    cameras.add_argument(
        "--camera-prime",
        "--prime",
        dest="camera_primes",
        action="append",
        type=int,
        help="select one camera; repeat the flag for an atlas",
    )
    cameras.add_argument(
        "--cameras",
        "--primes",
        dest="cameras",
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
        help="valley prominence in -log10(score)",
    )
    parser.add_argument(
        "--backend", choices=("auto", "cpu", "cuda"), default="auto"
    )
    parser.add_argument("--workers", type=int, default=None)
    parser.add_argument("--gpu-batch", type=int, default=8192)
    parser.add_argument(
        "--show",
        default="score",
        help="comma list: score,energy,cameras,green,boundary,return,all",
    )
    parser.add_argument(
        "--ledger-size",
        type=int,
        default=15,
        help="state size for Green/boundary/return diagnostics",
    )
    parser.add_argument(
        "--inspect-t",
        action="append",
        type=float,
        default=[],
        help="also inspect an explicit real frequency; repeat as needed",
    )
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
        help="grid-only mode (already the default)",
    )
    parser.set_defaults(refine=False)
    parser.add_argument(
        "--output", "--json-output", dest="output", type=Path, default=None
    )
    return parser


def _print_mechanism(report: dict[str, Any], channels: frozenset[str]) -> None:
    if "energy" in channels:
        print(f"    resultant R2        : {report['resultant']}")
        print(f"    total energy        : {report['total_energy']:.12e}")
        print(f"    visible energy      : {report['visible_energy']:.12e}")
        print(f"    blind energy        : {report['blind_energy']:.12e}")
        print(f"    blind fraction      : {report['blind_fraction']:.12e}")
        print(f"    visible angle       : {report['visible_angle_degrees']:.9f} deg")
        print(f"    dimension-free res. : {report['dimension_free_residual']:.12e}")
        print(f"    seed/bracket cosine : {report['seed_bracket_cosine']}")
    if "cameras" in channels:
        for camera in report["camera_reports"]:
            print(
                f"    camera p={camera['prime']:<3d} "
                f"energy={camera['energy']:.9e} "
                f"visibility={camera['visibility']:.9e} "
                f"resultant={camera['resultant']}"
            )


def _print_ledger(report: dict[str, Any], channels: frozenset[str]) -> None:
    energy = report["energy"]
    errors = report["errors"]
    if "green" in channels:
        print(f"    bracket energy      : {energy['bracket']:.12e}")
        print(f"    Green energy        : {energy['green']:.12e}")
        print(f"    Green curvature err : {errors['max_green_curvature']:.12e}")
    if "boundary" in channels:
        print(f"    boundary energy     : {energy['boundary_return']:.12e}")
        print(f"    boundary curvature  : {errors['max_boundary_curvature']:.12e}")
        print(f"    boundary endpoint   : {report['endpoints']['boundary_return_right']}")
    if "return" in channels:
        print(f"    state energy        : {energy['state']:.12e}")
        print(f"    polarized cross     : {energy['polarized_cross_term']:.12e}")
        print(f"    reconstructed       : {energy['reconstructed']:.12e}")
        print(f"    ledger error        : {energy['ledger_error']:.12e}")
        print(f"    reconstruction err  : {errors['max_reconstruction']:.12e}")


def main(argv: Sequence[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        grid = DecimalGrid.from_strings(args.tmin, args.tmax, args.grid)
        selected_cameras = (
            validate_cameras(args.camera_primes)
            if args.camera_primes
            else parse_cameras(args.cameras)
            if args.cameras
            else DEFAULT_CAMERAS
        )
        show_channels = parse_show(args.show)
    except ValueError as exc:
        parser.error(str(exc))
    if args.cutoff < 1:
        parser.error("cutoff must be at least 1")
    if args.ledger_size < 2:
        parser.error("ledger-size must be at least 2")
    if args.prominence < 0:
        parser.error("prominence must be nonnegative")
    if args.gpu_batch < 1:
        parser.error("gpu-batch must be positive")
    if any(not math.isfinite(value) for value in args.inspect_t):
        parser.error("inspect-t values must be finite")

    threshold = None if args.threshold < 0 else args.threshold
    ts = grid.float_values()
    print("=" * 88)
    print(" GENUINE-FIRST EMPIRICAL OPERATOR — REAL ROTATION MATRICES OVER R^2")
    print("=" * 88)
    print(f" Real time interval  : {grid.text_at(0)} <= t <= {grid.text_at(grid.count - 1)}")
    print(
        " Exact grid law     : "
        f"t_k = {format(grid.t_min, 'f')} + k * {format(grid.step, 'f')}"
    )
    print(f" Grid points         : {grid.count}")
    print(f" Prime cameras       : {selected_cameras}")
    print(f" Geometric cutoff    : {args.cutoff}")
    print(f" Coordinate field    : R^2 (float64 only)")
    print(f" Diagnostics         : {', '.join(sorted(show_channels))}")
    print(f" Refinement          : {'requested (noncanonical)' if args.refine else 'disabled'}")
    print("-" * 88)

    started = time.time()
    scores, backend_name, workers, prime_models_np = scan_scores(
        ts,
        selected_cameras,
        args.cutoff,
        args.backend,
        args.workers,
        args.gpu_batch,
    )
    raw_peak_indices, _properties = detect_grid_candidates(scores, args.prominence)
    cpu_candidates = canonicalize_candidates_on_cpu(
        raw_peak_indices, ts, prime_models_np
    )

    kept: list[GridCandidate] = []
    discarded: list[dict[str, Any]] = []
    for index, center_score, left_score, right_score in cpu_candidates:
        entry = {
            "grid_index": int(index),
            "t_decimal": grid.text_at(index),
            "score": center_score,
        }
        if threshold is not None and center_score > threshold:
            discarded.append({**entry, "reason": "above_threshold"})
            continue
        kept.append(
            GridCandidate(
                rank=len(kept) + 1,
                grid_index=int(index),
                t_decimal=grid.text_at(index),
                t_float_hex=float(ts[index]).hex(),
                score=center_score,
                left_score=left_score,
                right_score=right_score,
                scan_score=float(scores[index]),
            )
        )

    refined: list[RefinedCandidate] = []
    if args.refine:
        for candidate in kept:
            result = _refine_candidate(
                candidate.grid_index, ts, prime_models_np
            )
            if result is not None:
                refined.append(
                    RefinedCandidate(
                        grid_index=result.grid_index,
                        grid_t_decimal=candidate.t_decimal,
                        refined_t=result.refined_t,
                        refined_score=result.refined_score,
                    )
                )

    diagnostic_times: list[tuple[str, float]] = [
        (candidate.t_decimal, float(ts[candidate.grid_index])) for candidate in kept
    ]
    diagnostic_times.extend((repr(value), float(value)) for value in args.inspect_t)
    need_mechanism = bool({"energy", "cameras"} & show_channels)
    need_ledger = bool({"green", "boundary", "return"} & show_channels)
    diagnostics: list[dict[str, Any]] = []
    for label, value in diagnostic_times:
        row: dict[str, Any] = {"t_label": label, "t": value}
        if need_mechanism:
            row["mechanism"] = evaluate_mechanism(
                value, selected_cameras, args.cutoff
            )
        if need_ledger:
            row["green_boundary_return"] = audit_green_boundary_return(
                value, args.ledger_size
            )
        diagnostics.append(row)

    elapsed = time.time() - started
    print(f" Backend             : {backend_name}")
    print(f" CPU workers         : {workers}")
    print(f" Raw valleys         : {len(raw_peak_indices)}")
    print(f" Kept candidates     : {len(kept)}")
    print(f" Elapsed             : {elapsed:.3f} s")
    print("-" * 88)
    for candidate in kept:
        print(
            f" #{candidate.rank:02d} k={candidate.grid_index:<9d} "
            f"t={candidate.t_decimal:<14s} score={candidate.score:.12e}"
        )
        matching = next(
            (
                row
                for row in diagnostics
                if row["t_label"] == candidate.t_decimal
                and row["t"] == float(ts[candidate.grid_index])
            ),
            None,
        )
        if matching and "mechanism" in matching:
            _print_mechanism(matching["mechanism"], show_channels)
        if matching and "green_boundary_return" in matching:
            _print_ledger(matching["green_boundary_return"], show_channels)
    for row in diagnostics[len(kept) :]:
        print(f" inspect t={row['t_label']}")
        if "mechanism" in row:
            _print_mechanism(row["mechanism"], show_channels)
        if "green_boundary_return" in row:
            _print_ledger(row["green_boundary_return"], show_channels)
    print("=" * 88)

    payload: dict[str, Any] = {
        "schema": SCHEMA,
        "status": "FINITE_REAL_VECTOR_GRID_AUDIT",
        "operator": {
            "state": "n^(-1/2) R(-t log n) e1",
            "prime_camera": "(I - sqrt(p) R(-t log p))^(-1)",
            "bracket": "psi(pm-r) - 2 psi(pm) + psi(pm+r)",
            "coordinate_field": "R^2",
            "phase_carrier": "2x2 real rotation matrix",
            "cameras": list(selected_cameras),
            "cutoff": args.cutoff,
            "score": "norm(sum_e z_e)^2 / (N * sum_e norm(z_e)^2)",
        },
        "grid": {
            "tmin": format(grid.t_min, "f"),
            "requested_tmax": format(grid.t_max, "f"),
            "actual_tmax": format(grid.actual_t_max, "f"),
            "spacing": format(grid.step, "f"),
            "count": grid.count,
            "law": "t_k = tmin + k * grid",
        },
        "selection": {
            "threshold": threshold,
            "prominence_log10": args.prominence,
            "scan_backend": backend_name,
            "published_scores_backend": "CPU/NumPy float64",
            "workers": workers,
            "raw_peak_count": len(raw_peak_indices),
            "kept_count": len(kept),
            "discarded_count": len(discarded),
            "refinement_requested": args.refine,
            "no_refinement_is_canonical": True,
        },
        "candidates": [asdict(candidate) for candidate in kept],
        "discarded": discarded,
        "refined_noncanonical": [asdict(candidate) for candidate in refined],
        "diagnostic_channels": sorted(show_channels),
        "diagnostics": diagnostics,
        "runtime": {
            "elapsed_seconds": elapsed,
            "versions": package_versions(),
            "script_sha256": file_sha256(Path(__file__).resolve()),
        },
    }
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(
            json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
            encoding="utf-8",
        )
        print(f"Output written to {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
