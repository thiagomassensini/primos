#!/usr/bin/env python3
"""Finite numerical audit of the discrete valve identity.

The algebraic identity is independent of floating point and is formalized in
Lean 4. This script evaluates it on the real-spectral state

    psi_t(n) = n^(-1/2) exp(-i t log n)

and prints the complete polarized energy ledger. The large Green and boundary
energies do not add: their negative cross term is essential.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Sequence

import numpy as np


def real_spectral_state(t: float, size: int) -> np.ndarray:
    if size < 2:
        raise ValueError("size must be at least 2")
    n = np.arange(1, size + 1, dtype=np.float64)
    return (1.0 / np.sqrt(n)) * np.exp(-1j * t * np.log(n))


def second_difference(values: np.ndarray) -> np.ndarray:
    return values[2:] - 2.0 * values[1:-1] + values[:-2]


def green_return(curvature: np.ndarray, size: int) -> np.ndarray:
    result = np.zeros(size, dtype=np.complex128)
    for n in range(2, size):
        j = np.arange(n - 1)
        result[n] = np.sum((n - 1 - j) * curvature[j])
    return result


def affine_trace_return(a: complex, b: complex, size: int) -> np.ndarray:
    return a + np.arange(size, dtype=np.float64) * b


def audit_discrete_valve(t: float, size: int) -> dict[str, float | str | int]:
    state = real_spectral_state(t, size)
    curvature = second_difference(state)
    trace_a = state[0]
    trace_b = state[1] - state[0]
    green = green_return(curvature, size)
    boundary = affine_trace_return(trace_a, trace_b, size)
    reconstructed = green + boundary

    reconstruction_error = float(np.max(np.abs(state - reconstructed)))
    curvature_error = float(np.max(np.abs(second_difference(green) - curvature)))
    trace_green_error = float(max(abs(green[0]), abs(green[1] - green[0])))
    boundary_curvature_error = float(np.max(np.abs(second_difference(boundary))))

    state_energy = float(np.vdot(state, state).real)
    green_energy = float(np.vdot(green, green).real)
    boundary_energy = float(np.vdot(boundary, boundary).real)
    polarized_cross = float(2.0 * np.vdot(green, boundary).real)
    reconstructed_energy = green_energy + boundary_energy + polarized_cross
    energy_ledger_error = abs(state_energy - reconstructed_energy)

    return {
        "status": "FINITE_NUMERICAL_AUDIT",
        "t": repr(t),
        "size": size,
        "trace_a": repr(trace_a),
        "trace_b": repr(trace_b),
        "max_reconstruction_error": reconstruction_error,
        "max_green_curvature_error": curvature_error,
        "trace_of_green_error": trace_green_error,
        "max_boundary_curvature_error": boundary_curvature_error,
        "state_energy": state_energy,
        "green_energy": green_energy,
        "boundary_energy": boundary_energy,
        "polarized_cross_term": polarized_cross,
        "reconstructed_energy": reconstructed_energy,
        "energy_ledger_error": energy_ledger_error,
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Discrete valve boundary audit")
    parser.add_argument("--t", type=float, default=14.13472514173469)
    parser.add_argument("--size", type=int, default=15)
    parser.add_argument("--json-output", type=Path, default=None)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    result = audit_discrete_valve(args.t, args.size)

    print("=" * 78)
    print(" DISCRETE VALVE — INTERIOR, BOUNDARY AND POLARIZED ENERGY")
    print("=" * 78)
    print(f" Real spectral t                  : {result['t']}")
    print(f" State size                       : {result['size']}")
    print(f" Trace position a                 : {result['trace_a']}")
    print(f" Trace slope b                    : {result['trace_b']}")
    print("-" * 78)
    print(f" max |f - (G Bf + R Tr f)|        : {result['max_reconstruction_error']:.6e}")
    print(f" max |B(G Bf) - Bf|               : {result['max_green_curvature_error']:.6e}")
    print(f" ||Tr(G Bf)||_max                 : {result['trace_of_green_error']:.6e}")
    print(f" max |B(R Tr f)|                  : {result['max_boundary_curvature_error']:.6e}")
    print("-" * 78)
    print(f" ||f||^2                          : {result['state_energy']:.12f}")
    print(f" ||G Bf||^2                       : {result['green_energy']:.12f}")
    print(f" ||R Tr f||^2                     : {result['boundary_energy']:.12f}")
    print(f" 2 Re <G Bf, R Tr f>              : {result['polarized_cross_term']:.12f}")
    print(f" reconstructed polarized energy   : {result['reconstructed_energy']:.12f}")
    print(f" energy ledger error              : {result['energy_ledger_error']:.6e}")
    print("=" * 78)

    if args.json_output is not None:
        args.json_output.write_text(
            json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        print(f"Audit written to {args.json_output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
