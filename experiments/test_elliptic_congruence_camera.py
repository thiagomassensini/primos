import unittest
from collections import Counter, defaultdict

from experiments.elliptic_congruence_camera import (
    ShortWeierstrassCurve,
    analyze_camera,
    check_crt_fiber_factorization,
    generate_gate1_ledger,
    summarize_level,
)


def direct_profile(
    curve: ShortWeierstrassCurve,
    base: int,
    depth: int,
) -> tuple[int, int, dict[int, int], int]:
    """Independent exhaustive check using the complete next modulus."""

    modulus = base**depth
    next_modulus = modulus * base
    source = [
        (x, y)
        for x in range(modulus)
        for y in range(modulus)
        if curve.contains((x, y), modulus)
    ]
    counts: defaultdict[tuple[int, int], int] = defaultdict(int)
    next_point_count = 0
    for x in range(next_modulus):
        for y in range(next_modulus):
            if curve.contains((x, y), next_modulus):
                counts[(x % modulus, y % modulus)] += 1
                next_point_count += 1

    histogram = Counter(counts[point] for point in source)
    energy = sum((counts[point] - base) ** 2 for point in source)
    return len(source), next_point_count, dict(sorted(histogram.items())), energy


class EllipticCongruenceCameraTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.curve = ShortWeierstrassCurve(a=-1, b=1)
        cls.ledger = generate_gate1_ledger()

    def test_curve_discriminant(self) -> None:
        self.assertEqual(self.curve.discriminant, -368)

    def test_good_prime_cameras_have_uniform_fibers(self) -> None:
        for base in (3, 5, 7, 11, 13):
            camera = self.ledger["cameras"][str(base)]
            for level in camera["levels"]:
                with self.subTest(base=base, depth=level["depth"]):
                    self.assertEqual(level["defect_energy"], 0)
                    self.assertEqual(level["defective_point_count"], 0)
                    self.assertEqual(level["fiber_histogram"], {str(base): level["point_count"]})

    def test_prime_23_defect_is_exactly_the_dead_singular_fiber(self) -> None:
        camera = analyze_camera(self.curve, 23, 2)
        first = camera["levels"][0]
        self.assertEqual(camera["singular_points_mod_base"], [[13, 0]])
        self.assertEqual(first["fiber_histogram"], {"0": 1, "23": 21})
        self.assertEqual(first["defect_energy"], 23**2)
        self.assertEqual(first["defective_points"][0]["point"], [13, 0])
        self.assertTrue(first["defective_points"][0]["reduction_is_singular"])
        self.assertEqual(camera["levels"][1]["defect_energy"], 0)

    def test_prime_2_keeps_local_defect_after_scalar_population_stabilizes(self) -> None:
        camera = self.ledger["cameras"]["2"]
        self.assertEqual(camera["normalized_populations"], ["2", "3", "5", "5", "5"])
        self.assertEqual(camera["scalar_green_curvatures"][-1]["value"], "0")
        self.assertGreater(camera["levels"][-1]["defect_energy"], 0)

    def test_good_and_bad_composite_cameras_separate(self) -> None:
        for base in (15, 21):
            camera = self.ledger["cameras"][str(base)]
            self.assertTrue(all(level["defect_energy"] == 0 for level in camera["levels"]))
        for base in (6, 10):
            camera = self.ledger["cameras"][str(base)]
            self.assertGreater(camera["levels"][0]["defect_energy"], 0)

    def test_base_6_first_fiber_histogram(self) -> None:
        level, _, _ = summarize_level(self.curve, 6, 1)
        self.assertEqual(level.fiber_histogram, {"6": 6, "12": 6})
        self.assertEqual(level.defect_energy, 216)

    def test_crt_factorizes_point_counts_and_fibers(self) -> None:
        for left, right in ((3, 5), (3, 7), (2, 3), (2, 5)):
            check = check_crt_fiber_factorization(self.curve, left, right, 1)
            with self.subTest(left=left, right=right):
                self.assertTrue(check.point_count_identity)
                self.assertTrue(check.fiber_product_identity)
                self.assertEqual(check.mismatches, 0)

    def test_independent_direct_enumeration_matches_lift_engine(self) -> None:
        expected = {
            (2, 1): (2, 6, {2: 1, 4: 1}, 4),
            (2, 4): (40, 80, {0: 16, 2: 8, 4: 16}, 128),
            (3, 1): (6, 18, {3: 6}, 0),
            (23, 1): (22, 483, {0: 1, 23: 21}, 529),
            (6, 1): (12, 108, {6: 6, 12: 6}, 216),
            (15, 1): (42, 630, {15: 42}, 0),
        }
        for key, target in expected.items():
            with self.subTest(base=key[0], depth=key[1]):
                self.assertEqual(direct_profile(self.curve, *key), target)

    def test_gate_passes_without_upgrading_evidence_status(self) -> None:
        self.assertTrue(self.ledger["gate_passed"])
        self.assertEqual(self.ledger["status"], "EXPERIMENTAL_NOT_KERNEL_CHECKED")


if __name__ == "__main__":
    unittest.main()
