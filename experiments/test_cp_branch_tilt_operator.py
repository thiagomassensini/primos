import math
import unittest

from experiments.cp_branch_tilt_operator import (
    CpBranchOperator,
    CpTiltOperator,
    CpWeightedBranchOperator,
    cp_legs,
)


class CpBranchTiltOperatorTests(unittest.TestCase):
    def test_canonical_branch_saturates_at_half(self) -> None:
        for p in (2, 3, 5, 7, 11):
            with self.subTest(p=p):
                self.assertAlmostEqual(CpBranchOperator(p).mass(0.5), 1.0)

    def test_tilt_sign_changes_only_at_half(self) -> None:
        for p in (3, 5, 7, 11):
            op = CpTiltOperator(p)
            center = op.center(op.k0, 1)
            with self.subTest(p=p, sigma=0.4):
                self.assertLess(op.theta_sigma(center, 0.4), 0.0)
            with self.subTest(p=p, sigma=0.5):
                self.assertAlmostEqual(op.theta_sigma(center, 0.5), 0.0)
            with self.subTest(p=p, sigma=0.6):
                self.assertGreater(op.theta_sigma(center, 0.6), 0.0)

    def test_weighted_normalization_restores_half_saturation(self) -> None:
        p = 5
        coefficients = {a: complex(a, 1 - a) for a in cp_legs(p)}
        op = CpWeightedBranchOperator(p, coefficients).normalized()
        self.assertAlmostEqual(op.mass(0.5), 1.0)
        self.assertTrue(math.isclose(op.critical_sigma(), 0.5))


if __name__ == "__main__":
    unittest.main()
