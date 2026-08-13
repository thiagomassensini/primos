import unittest

from experiments.elliptic_congruence_camera_family import (
    CURVE_FAMILY,
    PRIMES,
    ShortWeierstrassCurve,
    generate_gate2_ledger,
    predicted_lift_count,
)


class EllipticCongruenceCameraFamilyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.ledger = generate_gate2_ledger()
        cls.prime_cases = {
            (row["curve_name"], row["prime"]): row
            for row in cls.ledger["prime_cases"]
        }
        cls.composite_cases = {
            (
                row["curve_name"],
                row["left_base"],
                row["right_base"],
            ): row
            for row in cls.ledger["composite_cases"]
        }

    def test_gate_passes_without_upgrading_evidence_status(self) -> None:
        self.assertTrue(self.ledger["gate_passed"])
        self.assertEqual(
            self.ledger["status"],
            "EXPERIMENTAL_NOT_KERNEL_CHECKED",
        )

    def test_discriminant_singularity_energy_equivalence(self) -> None:
        for row in self.ledger["prime_cases"]:
            with self.subTest(
                curve=row["curve_name"],
                prime=row["prime"],
            ):
                self.assertEqual(
                    row["discriminant_divisible"],
                    row["singular_point_count"] > 0,
                )
                self.assertEqual(
                    row["discriminant_divisible"],
                    row["first_defect_energy"] > 0,
                )
                self.assertTrue(
                    row["defective_support_equals_singular_support"]
                )
                self.assertTrue(
                    row["smooth_points_have_regular_fibers"]
                )

    def test_linearized_lift_law_matches_every_tested_fiber(self) -> None:
        for row in self.ledger["prime_cases"]:
            with self.subTest(
                curve=row["curve_name"],
                prime=row["prime"],
                depth=1,
            ):
                self.assertTrue(
                    row["linearized_lift_law_matches_first_level"]
                )
            if row["linearized_lift_law_matches_second_level"] is not None:
                with self.subTest(
                    curve=row["curve_name"],
                    prime=row["prime"],
                    depth=2,
                ):
                    self.assertTrue(
                        row["linearized_lift_law_matches_second_level"]
                    )

    def test_expected_bad_prime_signatures(self) -> None:
        expected = {
            ("single_bad_5", 5): (
                1,
                25,
                0,
                "TRANSIENT_BOUNDARY_PULSE",
            ),
            ("single_bad_23", 23): (
                1,
                529,
                0,
                "TRANSIENT_BOUNDARY_PULSE",
            ),
            ("two_bad_13_19", 13): (
                1,
                169,
                0,
                "TRANSIENT_BOUNDARY_PULSE",
            ),
            ("two_bad_13_19", 19): (
                1,
                361,
                0,
                "TRANSIENT_BOUNDARY_PULSE",
            ),
            ("two_bad_5_7", 5): (
                1,
                25,
                0,
                "TRANSIENT_BOUNDARY_PULSE",
            ),
            ("two_bad_5_7", 7): (
                1,
                49,
                0,
                "TRANSIENT_BOUNDARY_PULSE",
            ),
            ("persistent_bad_5", 5): (
                2,
                400,
                2875,
                "PERSISTENT_LOCAL_REDISTRIBUTION",
            ),
            ("persistent_bad_5", 11): (
                1,
                121,
                0,
                "TRANSIENT_BOUNDARY_PULSE",
            ),
        }
        observed = {
            key: (
                row["discriminant_valuation"],
                row["first_defect_energy"],
                row["second_defect_energy"],
                row["signature"],
            )
            for key, row in self.prime_cases.items()
            if row["first_defect_energy"] > 0
        }
        self.assertEqual(observed, expected)

    def test_control_curve_is_uniform_on_the_tested_prime_grid(self) -> None:
        for prime in PRIMES:
            row = self.prime_cases[("control_2_3_only", prime)]
            with self.subTest(prime=prime):
                self.assertEqual(row["first_defect_energy"], 0)
                self.assertEqual(row["singular_point_count"], 0)
                self.assertEqual(row["signature"], "SMOOTH_UNIFORM")

    def test_dead_and_excess_singular_fibers_are_distinguished(self) -> None:
        dead = self.prime_cases[("single_bad_5", 5)]
        excess = self.prime_cases[("persistent_bad_5", 5)]
        self.assertEqual(dead["singular_fiber_sizes"], {"3,0": 0})
        self.assertEqual(excess["singular_fiber_sizes"], {"1,0": 25})

    def test_crt_inherits_fiber_support_and_quadratic_energy(self) -> None:
        expected_energies = {
            ("control_2_3_only", 5, 7): 0,
            ("single_bad_5", 5, 7): 3675,
            ("single_bad_23", 23, 5): 92575,
            ("two_bad_13_19", 13, 5): 12675,
            ("two_bad_5_7", 5, 7): 13475,
            ("persistent_bad_5", 5, 7): 176400,
            ("persistent_bad_5", 11, 7): 53361,
        }
        for key, energy in expected_energies.items():
            row = self.composite_cases[key]
            with self.subTest(case=key):
                self.assertTrue(row["point_count_identity"])
                self.assertTrue(row["fiber_product_identity"])
                self.assertEqual(row["fiber_product_mismatches"], 0)
                self.assertTrue(row["energy_identity"])
                self.assertTrue(row["support_count_identity"])
                self.assertTrue(row["support_factor_identity"])
                self.assertEqual(row["direct_defect_energy"], energy)
                self.assertEqual(
                    row["product_predicted_defect_energy"],
                    energy,
                )
                self.assertIn(
                    row["regular_partner_scaling_identity"],
                    (None, True),
                )

    def test_bad_bad_composite_support_is_union_of_local_supports(self) -> None:
        row = self.composite_cases[("two_bad_5_7", 5, 7)]
        self.assertEqual(row["direct_defective_point_count"], 11)
        self.assertEqual(row["inherited_defective_point_count"], 11)
        self.assertEqual(row["direct_defect_energy"], 13475)

    def test_predictor_rejects_nonprime_base(self) -> None:
        spec = CURVE_FAMILY[0]
        curve = ShortWeierstrassCurve(spec.a, spec.b)
        with self.assertRaises(ValueError):
            predicted_lift_count(curve, 6, 1, (0, 1))


if __name__ == "__main__":
    unittest.main()
