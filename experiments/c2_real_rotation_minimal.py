#!/usr/bin/env python3
"""Scanner minimal do operador Genuine em R^2, usando somente float64.

O estado de cada inteiro n e um vetor real girando no plano:

    estado(n, t) = (1 / sqrt(n)) * R(-t log(n)) * (1, 0)

Cada camera prima aplica o bracket centrado nas coordenadas p*m +/- r.
O programa percorre uma grade fixa, sem refinamento, e imprime apenas as
alturas dos vales que passam pelo corte interno de visibilidade.

Isto e um experimento numerico finito, nao uma prova de zeros do operador
infinito.
"""

from __future__ import annotations

import argparse
import math

import numpy as np


TMIN = np.float64(1.0)
ZERO_SCORE = np.float64(1e-6)
BATCH_SIZE = 128


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    return all(n % d for d in range(3, math.isqrt(n) + 1, 2))


def rotation_states(t: np.ndarray, logs: np.ndarray, amplitudes: np.ndarray) -> np.ndarray:
    """Calcula (1/sqrt(n)) R(-t log(n)) (1,0), sempre em float64."""
    angle = -t.reshape((-1,) + (1,) * logs.ndim) * logs[None, ...]
    return amplitudes[None, ..., None] * np.stack(
        (np.cos(angle), np.sin(angle)), axis=-1
    )


def build_camera(camera: int, cutoff: int) -> dict[str, np.ndarray | int]:
    """Prepara sementes, centros e pernas da camera prima."""
    radius_count = (camera - 1) // 2
    seeds = np.arange(1, radius_count + 1, dtype=np.float64)
    radii = np.arange(1, radius_count + 1, dtype=np.float64)[None, :]
    levels = np.arange(1, cutoff + 1, dtype=np.float64)[:, None]
    centers = camera * levels

    return {
        "camera": camera,
        "coordinate_count": radius_count * (cutoff + 1),
        "seed_log": np.log(seeds),
        "seed_amp": 1.0 / np.sqrt(seeds),
        "center_log": np.log(centers[:, 0]),
        "center_amp": 1.0 / np.sqrt(centers[:, 0]),
        "minus_log": np.log(centers - radii),
        "minus_amp": 1.0 / np.sqrt(centers - radii),
        "plus_log": np.log(centers + radii),
        "plus_amp": 1.0 / np.sqrt(centers + radii),
    }


def camera_score(t: np.ndarray, model: dict[str, np.ndarray | int]) -> np.ndarray:
    """Visibilidade do vetor semente + bracket da camera."""
    seed = rotation_states(t, model["seed_log"], model["seed_amp"])
    center = rotation_states(t, model["center_log"], model["center_amp"])
    minus = rotation_states(t, model["minus_log"], model["minus_amp"])
    plus = rotation_states(t, model["plus_log"], model["plus_amp"])

    bracket = minus - 2.0 * center[:, :, None, :] + plus
    resultant = np.sum(seed, axis=1) + np.sum(bracket, axis=(1, 2))

    seed_energy = np.sum(model["seed_amp"] ** 2)
    bracket_energy = np.sum(bracket * bracket, axis=(1, 2, 3))
    total_energy = seed_energy + bracket_energy

    # A calibracao real da camera e uma rotacao seguida de uma escala comum.
    # Por isso ela cancela neste quociente de visibilidade de uma unica camera.
    visible_energy = np.sum(resultant * resultant, axis=1)
    return visible_energy / (model["coordinate_count"] * total_energy)


def scan_grid(ts: np.ndarray, camera: int, cutoff: int) -> np.ndarray:
    """Varre a grade em lotes pequenos para manter a memoria previsivel."""
    model = build_camera(camera, cutoff)
    scores = np.empty(ts.size, dtype=np.float64)
    for start in range(0, ts.size, BATCH_SIZE):
        stop = min(start + BATCH_SIZE, ts.size)
        scores[start:stop] = camera_score(ts[start:stop], model)
    return scores


def grid_zeros(scores: np.ndarray) -> np.ndarray:
    """Seleciona apenas minimos locais abaixo do corte fixo, sem refinamento."""
    if scores.size < 3:
        return np.empty(0, dtype=np.int64)
    middle = scores[1:-1]
    is_minimum = (middle <= scores[:-2]) & (middle < scores[2:])
    is_zero = middle <= ZERO_SCORE
    return np.flatnonzero(is_minimum & is_zero).astype(np.int64) + 1


def decimal_places(text: str) -> int:
    """Numero de casas pedido pelo usuario, usado somente para imprimir."""
    value = text.lower()
    if "e" in value:
        coefficient, exponent = value.split("e", 1)
        fraction = coefficient.partition(".")[2]
        return max(0, len(fraction) - int(exponent))
    return len(value.partition(".")[2].rstrip("0"))


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Operador Genuine minimal em R^2: imprime somente os zeros da grade."
    )
    parser.add_argument("--tmax", default="50", help="altura maxima (padrao: 50)")
    parser.add_argument("--camera", type=int, default=3, help="camera prima impar (padrao: 3)")
    parser.add_argument("--cutoff", type=int, default=1024, help="corte geometrico (padrao: 1024)")
    parser.add_argument("--grid", default="0.0005", help="passo da grade (padrao: 0.0005)")
    return parser


def main() -> int:
    args = build_parser().parse_args()

    try:
        tmax = np.float64(args.tmax)
        grid = np.float64(args.grid)
    except ValueError as exc:
        raise SystemExit(f"erro: tmax e grid devem ser numeros reais: {exc}") from exc

    if not np.isfinite(tmax) or tmax < TMIN:
        raise SystemExit("erro: tmax deve ser finito e maior ou igual a 1")
    if not np.isfinite(grid) or grid <= 0.0:
        raise SystemExit("erro: grid deve ser finito e positivo")
    if args.cutoff < 1:
        raise SystemExit("erro: cutoff deve ser positivo")
    if args.camera < 3 or args.camera % 2 == 0 or not is_prime(args.camera):
        raise SystemExit("erro: camera deve ser um primo impar (3, 5, 7, 11, ...)")

    point_count = int(np.floor((tmax - TMIN) / grid)) + 1
    ts = TMIN + np.arange(point_count, dtype=np.float64) * grid
    zeros = grid_zeros(scan_grid(ts, args.camera, args.cutoff))
    places = decimal_places(args.grid)

    for rank, index in enumerate(zeros, start=1):
        print(f"zero {rank:02d}  t = {ts[index]:.{places}f}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
