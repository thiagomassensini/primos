#!/usr/bin/env python3
"""Finite congruence-camera gate for a short Weierstrass curve.

This is an exploratory arithmetic laboratory, not a Lean theorem and not a
claim about an elliptic L-function.  It tests whether lift-fiber defects across
modular depths behave like a local boundary signal.

For a base ``q >= 2`` and depth ``k >= 1`` define

    X(q, k) = {(x, y) mod q^k : y^2 = x^3 + a*x + b mod q^k}.

Each point P in X(q, k) has a finite lift fiber in X(q, k + 1).  A regular
one-dimensional congruence fiber has q members, so the experiment records

    delta(P) = #fiber(P) - q,
    energy(q, k) = sum_P delta(P)^2.

The quadratic energy deliberately retains local redistribution that a scalar
point count can miss.
"""

from __future__ import annotations

import argparse
import json
import math
from collections import Counter
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Mapping

Point = tuple[int, int]


@dataclass(frozen=True)
class ShortWeierstrassCurve:
    """Integral affine model ``y^2 = x^3 + a*x + b``."""

    a: int
    b: int

    @property
    def discriminant(self) -> int:
        return -16 * (4 * self.a**3 + 27 * self.b**2)

    def residual(self, x: int, y: int) -> int:
        return y * y - x * x * x - self.a * x - self.b

    def contains(self, point: Point, modulus: int) -> bool:
        if modulus <= 0:
            raise ValueError("modulus must be positive")
        x, y = point
        return self.residual(x, y) % modulus == 0

    def gradient_mod(self, point: Point, modulus: int) -> Point:
        if modulus <= 0:
            raise ValueError("modulus must be positive")
        x, y = point
        # F(x,y) = y^2 - x^3 - a*x - b.
        return ((-3 * x * x - self.a) % modulus, (2 * y) % modulus)

    def is_singular_mod(self, point: Point, modulus: int) -> bool:
        return self.contains(point, modulus) and self.gradient_mod(point, modulus) == (0, 0)


@dataclass(frozen=True)
class CameraLevel:
    base: int
    depth: int
    modulus: int
    point_count: int
    next_point_count: int
    expected_fiber_size: int
    fiber_histogram: dict[str, int]
    defect_energy: int
    defective_point_count: int
    dead_fiber_count: int
    excess_lift_count: int
    normalized_population: str
    defective_points: list[dict[str, object]]
    defective_points_truncated: bool


@dataclass(frozen=True)
class CrtCheck:
    left_base: int
    right_base: int
    depth: int
    composite_base: int
    point_count_identity: bool
    fiber_product_identity: bool
    mismatches: int


def _require_base_depth(base: int, depth: int) -> None:
    if base < 2:
        raise ValueError("base must be at least 2")
    if depth < 1:
        raise ValueError("depth must be positive")


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    divisor = 3
    while divisor * divisor <= n:
        if n % divisor == 0:
            return False
        divisor += 2
    return True


def affine_points_mod(curve: ShortWeierstrassCurve, modulus: int) -> list[Point]:
    """Enumerate affine solutions with canonical residue representatives."""

    if modulus < 2:
        raise ValueError("modulus must be at least 2")
    return [
        (x, y)
        for x in range(modulus)
        for y in range(modulus)
        if curve.contains((x, y), modulus)
    ]


def lift_fiber(
    curve: ShortWeierstrassCurve,
    base: int,
    depth: int,
    point: Point,
) -> list[Point]:
    """Return all lifts from modulus ``base^depth`` to ``base^(depth+1)``."""

    _require_base_depth(base, depth)
    modulus = base**depth
    next_modulus = modulus * base
    x, y = point
    if not (0 <= x < modulus and 0 <= y < modulus):
        raise ValueError("point is not a canonical residue at this depth")
    if not curve.contains(point, modulus):
        raise ValueError("point is not on the congruence curve")

    return [
        (x + u * modulus, y + v * modulus)
        for u in range(base)
        for v in range(base)
        if curve.contains((x + u * modulus, y + v * modulus), next_modulus)
    ]


def fiber_profile(
    curve: ShortWeierstrassCurve,
    base: int,
    depth: int,
    points: Iterable[Point] | None = None,
) -> tuple[dict[Point, list[Point]], list[Point]]:
    """Compute every lift fiber and the complete next-level point set."""

    _require_base_depth(base, depth)
    source = list(points) if points is not None else affine_points_mod(curve, base**depth)
    fibers: dict[Point, list[Point]] = {}
    next_points: list[Point] = []
    seen: set[Point] = set()

    for point in source:
        lifts = lift_fiber(curve, base, depth, point)
        fibers[point] = lifts
        for lift in lifts:
            if lift in seen:
                raise AssertionError("distinct reduction fibers overlapped")
            seen.add(lift)
            next_points.append(lift)

    next_points.sort()
    return fibers, next_points


def _fraction_string(value: Fraction) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def summarize_level(
    curve: ShortWeierstrassCurve,
    base: int,
    depth: int,
    points: list[Point] | None = None,
) -> tuple[CameraLevel, list[Point], dict[Point, int]]:
    fibers, next_points = fiber_profile(curve, base, depth, points)
    counts = {point: len(lifts) for point, lifts in fibers.items()}
    histogram = Counter(counts.values())
    defects = {point: count - base for point, count in counts.items()}
    defective = {point: defect for point, defect in defects.items() if defect != 0}

    example_limit = 16
    defective_rows: list[dict[str, object]] = []
    for point, defect in sorted(defective.items())[:example_limit]:
        row: dict[str, object] = {
            "point": [point[0], point[1]],
            "fiber_size": counts[point],
            "defect": defect,
        }
        if is_prime(base):
            reduced = (point[0] % base, point[1] % base)
            row["reduction_mod_prime"] = [reduced[0], reduced[1]]
            row["reduction_is_singular"] = curve.is_singular_mod(reduced, base)
        defective_rows.append(row)

    normalized = Fraction(len(counts), base ** (depth - 1))
    level = CameraLevel(
        base=base,
        depth=depth,
        modulus=base**depth,
        point_count=len(counts),
        next_point_count=len(next_points),
        expected_fiber_size=base,
        fiber_histogram={str(size): amount for size, amount in sorted(histogram.items())},
        defect_energy=sum(defect * defect for defect in defects.values()),
        defective_point_count=len(defective),
        dead_fiber_count=sum(count == 0 for count in counts.values()),
        excess_lift_count=sum(max(0, count - base) for count in counts.values()),
        normalized_population=_fraction_string(normalized),
        defective_points=defective_rows,
        defective_points_truncated=len(defective) > example_limit,
    )
    return level, next_points, counts


def analyze_camera(
    curve: ShortWeierstrassCurve,
    base: int,
    max_depth: int,
) -> dict[str, object]:
    _require_base_depth(base, max_depth)
    points = affine_points_mod(curve, base)
    levels: list[CameraLevel] = []
    populations: list[int] = [len(points)]

    for depth in range(1, max_depth + 1):
        level, points, _ = summarize_level(curve, base, depth, points)
        levels.append(level)
        populations.append(len(points))

    normalized = [Fraction(count, base**index) for index, count in enumerate(populations)]
    green_curvatures: list[dict[str, object]] = []
    for center_index in range(1, len(normalized) - 1):
        curvature = normalized[center_index + 1] - 2 * normalized[center_index] + normalized[center_index - 1]
        green_curvatures.append(
            {
                "center_depth": center_index + 1,
                "value": _fraction_string(curvature),
            }
        )

    singular_points: list[list[int]] = []
    if is_prime(base):
        singular_points = [
            [x, y]
            for x, y in affine_points_mod(curve, base)
            if curve.is_singular_mod((x, y), base)
        ]

    return {
        "base": base,
        "prime_base": is_prime(base),
        "singular_points_mod_base": singular_points,
        "levels": [asdict(level) for level in levels],
        "normalized_populations": [_fraction_string(value) for value in normalized],
        "scalar_green_curvatures": green_curvatures,
    }


def _fiber_counts(
    curve: ShortWeierstrassCurve,
    base: int,
    depth: int,
) -> tuple[list[Point], Mapping[Point, int]]:
    points = affine_points_mod(curve, base**depth)
    fibers, _ = fiber_profile(curve, base, depth, points)
    return points, {point: len(lifts) for point, lifts in fibers.items()}


def check_crt_fiber_factorization(
    curve: ShortWeierstrassCurve,
    left_base: int,
    right_base: int,
    depth: int = 1,
) -> CrtCheck:
    """Check point-count and lift-fiber products for coprime camera bases."""

    _require_base_depth(left_base, depth)
    _require_base_depth(right_base, depth)
    if math.gcd(left_base, right_base) != 1:
        raise ValueError("CRT check requires coprime bases")

    composite = left_base * right_base
    left_points, left_counts = _fiber_counts(curve, left_base, depth)
    right_points, right_counts = _fiber_counts(curve, right_base, depth)
    composite_points, composite_counts = _fiber_counts(curve, composite, depth)

    left_modulus = left_base**depth
    right_modulus = right_base**depth
    mismatches = 0
    for x, y in composite_points:
        left_point = (x % left_modulus, y % left_modulus)
        right_point = (x % right_modulus, y % right_modulus)
        expected = left_counts[left_point] * right_counts[right_point]
        if composite_counts[(x, y)] != expected:
            mismatches += 1

    return CrtCheck(
        left_base=left_base,
        right_base=right_base,
        depth=depth,
        composite_base=composite,
        point_count_identity=len(composite_points) == len(left_points) * len(right_points),
        fiber_product_identity=mismatches == 0,
        mismatches=mismatches,
    )


def _level_energy(camera: dict[str, object], depth: int) -> int:
    levels = camera["levels"]
    assert isinstance(levels, list)
    row = levels[depth - 1]
    assert isinstance(row, dict)
    return int(row["defect_energy"])


def generate_gate1_ledger() -> dict[str, object]:
    curve = ShortWeierstrassCurve(a=-1, b=1)
    depth_plan = {
        2: 4,
        3: 3,
        5: 3,
        7: 3,
        11: 2,
        13: 2,
        23: 2,
        6: 2,
        10: 2,
        15: 2,
        21: 2,
    }
    cameras = {str(base): analyze_camera(curve, base, depth) for base, depth in depth_plan.items()}
    crt_checks = [
        check_crt_fiber_factorization(curve, 3, 5, 1),
        check_crt_fiber_factorization(curve, 3, 7, 1),
        check_crt_fiber_factorization(curve, 2, 3, 1),
        check_crt_fiber_factorization(curve, 2, 5, 1),
    ]

    good_prime_bases = (3, 5, 7, 11, 13)
    good_composite_bases = (15, 21)
    bad_composite_bases = (6, 10)

    good_primes_zero = all(
        all(int(level["defect_energy"]) == 0 for level in cameras[str(base)]["levels"])
        for base in good_prime_bases
    )
    good_composites_zero = all(
        all(int(level["defect_energy"]) == 0 for level in cameras[str(base)]["levels"])
        for base in good_composite_bases
    )
    bad_composites_detected = all(_level_energy(cameras[str(base)], 1) > 0 for base in bad_composite_bases)
    bad_two_detected = all(int(level["defect_energy"]) > 0 for level in cameras["2"]["levels"])
    bad_twenty_three_detected = (
        cameras["23"]["singular_points_mod_base"] == [[13, 0]]
        and _level_energy(cameras["23"], 1) == 23**2
    )
    crt_passed = all(check.point_count_identity and check.fiber_product_identity for check in crt_checks)

    observations = {
        "good_prime_cameras_have_zero_local_defect_energy": good_primes_zero,
        "good_composite_cameras_have_zero_local_defect_energy": good_composites_zero,
        "composites_containing_bad_prime_2_are_detected": bad_composites_detected,
        "prime_2_has_persistent_local_redistribution": bad_two_detected,
        "prime_23_has_one_dead_singular_fiber_at_first_lift": bad_twenty_three_detected,
        "crt_point_and_fiber_factorization_holds": crt_passed,
        "scalar_count_can_miss_local_defect": (
            cameras["2"]["scalar_green_curvatures"][-1]["value"] == "0"
            and _level_energy(cameras["2"], 4) > 0
        ),
    }
    gate_passed = all(bool(value) for value in observations.values())

    return {
        "schema": "elliptic-congruence-camera-gate1-v1",
        "status": "EXPERIMENTAL_NOT_KERNEL_CHECKED",
        "curve": {
            "affine_equation": "y^2 = x^3 - x + 1",
            "a": curve.a,
            "b": curve.b,
            "discriminant": curve.discriminant,
        },
        "definitions": {
            "state_space": "X(q,k)={(x,y) mod q^k : y^2=x^3-x+1 mod q^k}",
            "fiber_defect": "delta(P)=#lifts(P from q^k to q^(k+1))-q",
            "quadratic_defect_energy": "E(q,k)=sum_P delta(P)^2",
            "normalized_population": "A(q,k)=#X(q,k)/q^(k-1)",
            "scalar_green_curvature": "A(q,k+1)-2*A(q,k)+A(q,k-1)",
        },
        "scope_limits": [
            "Affine congruence points only; the projective point at infinity is not included.",
            "Finite exhaustive arithmetic only; no Lean theorem is claimed.",
            "No elliptic L-function, rank, Selmer group, BSD, or zero-transfer claim is made.",
            "The expected regular fiber size q is tested here, not imported as a premise of a proof.",
        ],
        "cameras": cameras,
        "crt_checks": [asdict(check) for check in crt_checks],
        "observations": observations,
        "gate_passed": gate_passed,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("experiments/results/elliptic_congruence_camera_gate1.json"),
        help="JSON ledger destination",
    )
    args = parser.parse_args()

    ledger = generate_gate1_ledger()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(ledger, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print(f"curve: {ledger['curve']['affine_equation']}")
    print(f"discriminant: {ledger['curve']['discriminant']}")
    for base in (2, 3, 5, 7, 11, 13, 23, 6, 10, 15, 21):
        camera = ledger["cameras"][str(base)]
        energies = [level["defect_energy"] for level in camera["levels"]]
        print(f"base {base:>2}: defect energies {energies}")
    print(f"gate_passed: {ledger['gate_passed']}")
    print(f"ledger: {args.output}")


if __name__ == "__main__":
    main()
