#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import pathlib
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parent


def load_module(name: str, filename: str):
    spec = importlib.util.spec_from_file_location(name, ROOT / filename)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


scanner = load_module("c2_real_spectral_grid", "c2_real_spectral_grid.py")
mechanism = load_module("c2_real_spectral_mechanism", "c2_real_spectral_mechanism.py")


class MechanismTests(unittest.TestCase):
    def test_mechanism_reconstructs_scanner_and_projection_ledger(self):
        result = mechanism.evaluate_mechanism(14.1347, (3, 5, 7, 11), 32)
        self.assertLess(result["score_consistency_error"], 1e-15)
        self.assertAlmostEqual(
            result["visible_energy"] + result["blind_energy"],
            result["total_energy"],
            places=14,
        )
        self.assertAlmostEqual(
            result["dimension_free_residual"],
            result["coordinate_count"] * result["score"],
            places=14,
        )
        self.assertLess(result["projection_idempotence_defect"], 1e-12)
        self.assertLess(result["projection_self_adjoint_defect"], 1e-12)

    def test_seed_and_bracket_close_destructively_near_first_resonance(self):
        result = mechanism.evaluate_mechanism(14.1347, (3, 5, 7, 11), 64)
        self.assertLess(result["seed_bracket_cosine"], -0.999)
        self.assertGreater(result["blind_fraction"], 0.999999)
        self.assertGreater(result["total_energy"], 0.0)
        self.assertEqual(result["coordinate_count"], 715)

    def test_every_camera_retains_positive_energy(self):
        result = mechanism.evaluate_mechanism(30.4249, (3, 5, 7, 11), 32)
        self.assertTrue(all(camera["energy"] > 0.0 for camera in result["cameras"]))
        self.assertTrue(
            all(0.0 <= camera["visibility"] <= 1.0 for camera in result["cameras"])
        )


if __name__ == "__main__":
    unittest.main()
