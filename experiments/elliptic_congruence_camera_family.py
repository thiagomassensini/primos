#!/usr/bin/env python3
"""Gate 2: finite family test for elliptic congruence cameras.

This experiment stays in finite affine arithmetic.  It checks three layers:

1. discriminant divisibility, singular residues, and local lift-fiber energy;
2. the exact first-order lift law at every tested modular point;
3. CRT inheritance of point counts, fiber sizes, defect support, and energy.

It does not construct the projective elliptic-curve group, rank, Selmer data,
an elliptic L-function, or a zero-transfer theorem.
"""

from __future__ import annotations

import argparse
import json
import math
from collections import Counter
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Mapping

from experiments.elliptic_congruence_camera import (
    Point,
    ShortWeierstrassCurve,
    affine_points_mod,
    fiber_profile,
    is_prime,
    summarize_level,
)


@dataclass(frozen=True)
class CurveSpec:
    name: str
    a: int
    b: int
    equation: str


@dataclass(frozen=True)
class PrimeCameraCase:
    curve_name: str
    a: int
    b: int
    discriminant: int
    prime: int
    discriminant_valuation: int
    discriminant_divisible: bool
    point_count_mod_prime: int
    singular_points: list[list[int]]
    singular_point_count: int
    first_fiber_histogram: dict[str, int]
    first_defect_energy: int
    first_defective_point_count: int
    singular_fiber_sizes: dict[str, int]
    smooth_points_have_regular_fibers: bool
    defective_support_equals_singular_support: bool
    linearized_lift_law_matches_first_level: bool
    second_fiber_histogram: dict[str, int] | None
    second_defect_energy: int | None
    linearized_lift_law_matches_second_level: bool | None
    signature: str


@dataclass(frozen=True)
class CompositeCameraCase:
    curve_name: str
    left_base: int
    right_base: int
    composite_base: int
    left_point_count: int
    right_point_count: int
    composite_point_count: int
    point_count_identity: bool
    fiber_product_identity: bool
    fiber_product_mismatches: int
    direct_defect_energy: int
    product_predicted_defect_energy: int
    energy_identity: bool
    direct_defective_point_count: int
    inherited_defective_point_count: int
    support_count_identity: bool
    support_factor_identity: bool
    regular_partner_scaled_energy: int | None
    regular_partner_scaling_identity: bool | None


PRIMES: tuple[int, ...] = (5, 7, 11, 13, 17, 19, 23, 29, 31)

CURVE_FAMILY: tuple[CurveSpec, ...] = (
    CurveSpec(
        name="control_2_3_only",
        a=0,
        b=1,
        equation="y^2 = x^3 + 1",
    ),
    CurveSpec(
        name="single_bad_5",
        a=-2,
        b=-1,
        equation="y^2 = x^3 - 2*x - 1",
    ),
    CurveSpec(
        name="single_bad_23",
        a=-1,
        b=1,
        equation="y^2 = x^3 - x + 1",
    ),
    CurveSpec(
        name="two_bad_13_19",
        a=1,
        b=-3,
        equation="y^2 = x^3 + x - 3",
    ),
    CurveSpec(
        name="two_bad_5_7",
        a=2,
        b=-2,
        equation="y^2 = x^3 + 2*x - 2",
    ),
    CurveSpec(
        name="persistent_bad_5",
        a=2,
        b=-3,
        equation="y^2 = x^3 + 2*x - 3",
    ),
)

COMPOSITE_PLAN: tuple[tuple[str, int, int], ...] = (
    ("control_2_3_only", 5, 7),
    ("single_bad_5", 5, 7),
    ("single_bad_23", 23, 5),
    ("two_bad_13_19", 13, 5),
    ("two_bad_5_7", 5, 7),
    ("persistent_bad_5", 5, 7),
    ("persistent_bad_5", 11, 7),
)


def p_adic_valuation(value: int, prime: int) -> int:
    """Return v_prime(value), with value required to be nonzero."""

    if value == 0:
        raise ValueError("valuation is undefined for zero in this experiment")
    if not is_prime(prime):
        raise ValueError("valuation base must be prime")
    remaining = abs(value)
    valuation = 0
    while remaining % prime == 0:
        remaining //= prime
        valuation += 1
    return valuation


def predicted_lift_count(
    curve: ShortWeierstrassCurve,
    prime: int,
    depth: int,
    point: Point,
) -> int:
    """Predict the exact lift count from p^k to p^(k+1).

    Write F(x,y)=0 for the affine equation and m=p^k.  For
    (x+u*m,y+v*m), all second-order terms vanish modulo p*m, so the lift
    condition is the single linear equation

        F(x,y)/m + u*F_x(x,y) + v*F_y(x,y) = 0 mod p.

    A nonzero gradient gives exactly p solutions.  A zero gradient gives all
    p^2 candidate lifts or none, depending on the residual quotient.
    """

    if not is_prime(prime):
        raise ValueError("prime must be prime")
    if depth < 1:
        raise ValueError("depth must be positive")
    modulus = prime**depth
    x, y = point
    if not (0 <= x < modulus and 0 <= y < modulus):
        raise ValueError("point must be a canonical residue at the given depth")
    residual = curve.residual(x, y)
    if residual % modulus != 0:
        raise ValueError("point is not on the congruence curve")

    residual_quotient = (residual // modulus) % prime
    grad_x, grad_y = curve.gradient_mod(point, prime)
    if grad_x == 0 and grad_y == 0:
        return prime * prime if residual_quotient == 0 else 0
    return prime


def _first_level_counts(
    curve: ShortWeierstrassCurve,
    base: int,
) -> tuple[list[Point], dict[Point, int]]:
    points = affine_points_mod(curve, base)
    fibers, _ = fiber_profile(curve, base, 1, points)
    return points, {point: len(lifts) for point, lifts in fibers.items()}


def _energy(counts: Mapping[Point, int], expected: int) -> int:
    return sum((count - expected) ** 2 for count in counts.values())


def _point_key(point: Point) -> str:
    return f"{point[0]},{point[1]}"


def analyze_prime_camera(spec: CurveSpec, prime: int) -> PrimeCameraCase:
    if not is_prime(prime):
        raise ValueError("prime camera analysis requires a prime base")
    curve = ShortWeierstrassCurve(a=spec.a, b=spec.b)
    source = affine_points_mod(curve, prime)
    first, next_points, first_counts = summarize_level(curve, prime, 1, source)

    singular = {
        point
        for point in source
        if curve.is_singular_mod(point, prime)
    }
    defective = {
        point
        for point, count in first_counts.items()
        if count != prime
    }
    smooth_regular = all(
        first_counts[point] == prime
        for point in source
        if point not in singular
    )
    first_linearized = all(
        first_counts[point] == predicted_lift_count(curve, prime, 1, point)
        for point in source
    )

    second_histogram: dict[str, int] | None = None
    second_energy: int | None = None
    second_linearized: bool | None = None
    if singular:
        second, _, second_counts = summarize_level(
            curve,
            prime,
            2,
            next_points,
        )
        second_histogram = second.fiber_histogram
        second_energy = second.defect_energy
        second_linearized = all(
            second_counts[point] == predicted_lift_count(curve, prime, 2, point)
            for point in next_points
        )

    if not singular:
        signature = "SMOOTH_UNIFORM"
    elif second_energy == 0:
        signature = "TRANSIENT_BOUNDARY_PULSE"
    else:
        signature = "PERSISTENT_LOCAL_REDISTRIBUTION"

    return PrimeCameraCase(
        curve_name=spec.name,
        a=spec.a,
        b=spec.b,
        discriminant=curve.discriminant,
        prime=prime,
        discriminant_valuation=p_adic_valuation(curve.discriminant, prime),
        discriminant_divisible=curve.discriminant % prime == 0,
        point_count_mod_prime=len(source),
        singular_points=[[x, y] for x, y in sorted(singular)],
        singular_point_count=len(singular),
        first_fiber_histogram=first.fiber_histogram,
        first_defect_energy=first.defect_energy,
        first_defective_point_count=first.defective_point_count,
        singular_fiber_sizes={
            _point_key(point): first_counts[point]
            for point in sorted(singular)
        },
        smooth_points_have_regular_fibers=smooth_regular,
        defective_support_equals_singular_support=defective == singular,
        linearized_lift_law_matches_first_level=first_linearized,
        second_fiber_histogram=second_histogram,
        second_defect_energy=second_energy,
        linearized_lift_law_matches_second_level=second_linearized,
        signature=signature,
    )


def analyze_composite_camera(
    spec: CurveSpec,
    left_base: int,
    right_base: int,
) -> CompositeCameraCase:
    if math.gcd(left_base, right_base) != 1:
        raise ValueError("composite camera factors must be coprime")
    curve = ShortWeierstrassCurve(a=spec.a, b=spec.b)
    composite = left_base * right_base

    left_points, left_counts = _first_level_counts(curve, left_base)
    right_points, right_counts = _first_level_counts(curve, right_base)
    composite_points, composite_counts = _first_level_counts(curve, composite)

    mismatches = 0
    support_factor_identity = True
    for point in composite_points:
        x, y = point
        left_point = (x % left_base, y % left_base)
        right_point = (x % right_base, y % right_base)
        predicted_count = left_counts[left_point] * right_counts[right_point]
        if composite_counts[point] != predicted_count:
            mismatches += 1
        predicted_defective = (
            left_counts[left_point] != left_base
            or right_counts[right_point] != right_base
        )
        if (composite_counts[point] != composite) != predicted_defective:
            support_factor_identity = False

    left_energy = _energy(left_counts, left_base)
    right_energy = _energy(right_counts, right_base)
    direct_energy = _energy(composite_counts, composite)
    predicted_energy = sum(
        (
            left_counts[left_point] * right_counts[right_point]
            - composite
        )
        ** 2
        for left_point in left_points
        for right_point in right_points
    )

    left_defective = sum(count != left_base for count in left_counts.values())
    right_defective = sum(count != right_base for count in right_counts.values())
    inherited_defective = (
        left_defective * len(right_points)
        + len(left_points) * right_defective
        - left_defective * right_defective
    )
    direct_defective = sum(
        count != composite
        for count in composite_counts.values()
    )

    scaled_energy: int | None = None
    scaled_identity: bool | None = None
    if left_energy > 0 and right_energy == 0:
        scaled_energy = len(right_points) * (right_base**2) * left_energy
        scaled_identity = direct_energy == scaled_energy
    elif right_energy > 0 and left_energy == 0:
        scaled_energy = len(left_points) * (left_base**2) * right_energy
        scaled_identity = direct_energy == scaled_energy
    elif left_energy == 0 and right_energy == 0:
        scaled_energy = 0
        scaled_identity = direct_energy == 0

    return CompositeCameraCase(
        curve_name=spec.name,
        left_base=left_base,
        right_base=right_base,
        composite_base=composite,
        left_point_count=len(left_points),
        right_point_count=len(right_points),
        composite_point_count=len(composite_points),
        point_count_identity=(
            len(composite_points) == len(left_points) * len(right_points)
        ),
        fiber_product_identity=mismatches == 0,
        fiber_product_mismatches=mismatches,
        direct_defect_energy=direct_energy,
        product_predicted_defect_energy=predicted_energy,
        energy_identity=direct_energy == predicted_energy,
        direct_defective_point_count=direct_defective,
        inherited_defective_point_count=inherited_defective,
        support_count_identity=direct_defective == inherited_defective,
        support_factor_identity=support_factor_identity,
        regular_partner_scaled_energy=scaled_energy,
        regular_partner_scaling_identity=scaled_identity,
    )


def _case_lookup(
    cases: list[PrimeCameraCase],
) -> dict[tuple[str, int], PrimeCameraCase]:
    return {(case.curve_name, case.prime): case for case in cases}


def generate_gate2_ledger() -> dict[str, object]:
    specs = {spec.name: spec for spec in CURVE_FAMILY}
    prime_cases = [
        analyze_prime_camera(spec, prime)
        for spec in CURVE_FAMILY
        for prime in PRIMES
    ]
    composite_cases = [
        analyze_composite_camera(specs[curve_name], left, right)
        for curve_name, left, right in COMPOSITE_PLAN
    ]

    lookup = _case_lookup(prime_cases)
    local_equivalence = all(
        (
            case.discriminant_divisible
            == (case.singular_point_count > 0)
            == (case.first_defect_energy > 0)
        )
        for case in prime_cases
    )
    local_lift_law = all(
        case.smooth_points_have_regular_fibers
        and case.defective_support_equals_singular_support
        and case.linearized_lift_law_matches_first_level
        and (
            case.linearized_lift_law_matches_second_level
            in (None, True)
        )
        for case in prime_cases
    )
    exact_bad_prime_support = all(
        {
            prime
            for prime in PRIMES
            if lookup[(spec.name, prime)].first_defect_energy > 0
        }
        == {
            prime
            for prime in PRIMES
            if ShortWeierstrassCurve(spec.a, spec.b).discriminant % prime == 0
        }
        for spec in CURVE_FAMILY
    )
    signatures = {case.signature for case in prime_cases}
    has_dead_singular_fiber = any(
        any(size == 0 for size in case.singular_fiber_sizes.values())
        for case in prime_cases
    )
    has_excess_singular_fiber = any(
        any(size > case.prime for size in case.singular_fiber_sizes.values())
        for case in prime_cases
    )
    composite_identities = all(
        case.point_count_identity
        and case.fiber_product_identity
        and case.energy_identity
        and case.support_count_identity
        and case.support_factor_identity
        and case.regular_partner_scaling_identity in (None, True)
        for case in composite_cases
    )

    observations = {
        "discriminant_singularity_energy_equivalence_on_family": local_equivalence,
        "linearized_lift_law_matches_every_tested_fiber": local_lift_law,
        "bad_prime_support_matches_discriminant_support": exact_bad_prime_support,
        "transient_and_persistent_signatures_both_observed": {
            "TRANSIENT_BOUNDARY_PULSE",
            "PERSISTENT_LOCAL_REDISTRIBUTION",
        }.issubset(signatures),
        "dead_and_excess_singular_fibers_both_observed": (
            has_dead_singular_fiber and has_excess_singular_fiber
        ),
        "crt_point_fiber_support_energy_identities_hold": composite_identities,
    }
    gate_passed = all(observations.values())

    return {
        "schema": "elliptic-congruence-camera-gate2-v1",
        "status": "EXPERIMENTAL_NOT_KERNEL_CHECKED",
        "scope": {
            "model": "affine short Weierstrass congruence curves",
            "prime_range": list(PRIMES),
            "depths": (
                "first lift for every curve/prime; second lift when the "
                "first reduction is singular"
            ),
            "excluded_claims": [
                "projective elliptic-curve group",
                "rank",
                "Selmer group",
                "BSD",
                "elliptic L-function",
                "zero transfer",
            ],
        },
        "definitions": {
            "fiber_defect": "delta(P)=#lifts(P from q^k to q^(k+1))-q",
            "quadratic_energy": "E(q,k)=sum_P delta(P)^2",
            "linearized_lift_equation": (
                "F(P)/p^k + u*F_x(P) + v*F_y(P) = 0 mod p"
            ),
            "crt_fiber_product": (
                "L_(ab)(P_a,P_b)=L_a(P_a)*L_b(P_b) for gcd(a,b)=1"
            ),
        },
        "curves": [
            {
                **asdict(spec),
                "discriminant": ShortWeierstrassCurve(
                    spec.a,
                    spec.b,
                ).discriminant,
            }
            for spec in CURVE_FAMILY
        ],
        "prime_cases": [asdict(case) for case in prime_cases],
        "composite_cases": [asdict(case) for case in composite_cases],
        "observations": observations,
        "gate_passed": gate_passed,
    }


def print_summary(ledger: dict[str, object]) -> None:
    print("Elliptic congruence camera Gate 2")
    print(f"status: {ledger['status']}")
    print(f"gate_passed: {ledger['gate_passed']}")
    print()
    print("nonzero prime-camera energies:")
    for row in ledger["prime_cases"]:
        assert isinstance(row, dict)
        if int(row["first_defect_energy"]) > 0:
            print(
                f"  {row['curve_name']:>20} p={row['prime']:>2} "
                f"v_p(Delta)={row['discriminant_valuation']} "
                f"E1={row['first_defect_energy']} "
                f"E2={row['second_defect_energy']} "
                f"{row['signature']}"
            )
    print()
    print("composite-camera energies:")
    for row in ledger["composite_cases"]:
        assert isinstance(row, dict)
        print(
            f"  {row['curve_name']:>20} "
            f"{row['left_base']}*{row['right_base']}="
            f"{row['composite_base']}: "
            f"E={row['direct_defect_energy']} "
            f"product={row['product_predicted_defect_energy']}"
        )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(
            "experiments/results/elliptic_congruence_camera_gate2.json"
        ),
    )
    args = parser.parse_args()

    ledger = generate_gate2_ledger()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(ledger, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print_summary(ledger)
    if not ledger["gate_passed"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
