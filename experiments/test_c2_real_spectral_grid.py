#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import pathlib
import sys
import unittest

import numpy as np

ROOT = pathlib.Path(__file__).resolve().parent


def load_module(name: str, filename: str):
    spec = importlib.util.spec_from_file_location(name, ROOT / filename)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


scanner = load_module("c2_real_spectral_grid", "c2_real_spectral_grid.py")
valve = load_module("c2_discrete_valve_boundary", "c2_discrete_valve_boundary.py")


class DecimalGridTests(unittest.TestCase):
    def test_integer_indexed_decimal_grid(self):
        grid = scanner.DecimalGrid.from_strings("1", "1.001", "0.0001")
        self.assertEqual(grid.count, 11)
        self.assertEqual(grid.text_at(0), "1.0000")
        self.assertEqual(grid.text_at(7), "1.0007")
        self.assertEqual(grid.text_at(10), "1.0010")

    def test_float_grid_does_not_accumulate_arange_step(self):
        grid = scanner.DecimalGrid.from_strings("1", "2", "0.0001")
        values = grid.float_values()
        self.assertEqual(values.shape, (10001,))
        self.assertAlmostEqual(values[5000], 1.5, places=15)


class OperatorTests(unittest.TestCase):
    def test_score_is_finite_visibility(self):
        models = scanner.build_prime_models((3, 5), 8, np)
        scores = np.asarray(
            scanner.evaluate_operator_chunk(np.array([1.0, 2.0, 3.0]), models, np)
        )
        self.assertTrue(np.all(np.isfinite(scores)))
        self.assertTrue(np.all(scores >= 0.0))
        self.assertTrue(np.all(scores <= 1.0 + 1e-12))

    def test_candidate_is_a_grid_index_and_local_minimum(self):
        grid = scanner.DecimalGrid.from_strings("14.12", "14.15", "0.001")
        values = grid.float_values()
        models = scanner.build_prime_models((3, 5, 7, 11), 32, np)
        scores = np.asarray(scanner.evaluate_operator_chunk(values, models, np))
        peaks, _ = scanner.detect_grid_candidates(scores, 0.1)
        candidates = scanner.canonicalize_candidates_on_cpu(peaks, values, models)
        for index, score, left, right in candidates:
            self.assertEqual(grid.decimal_at(index), grid.t_min + grid.step * index)
            if left is not None:
                self.assertLessEqual(score, left)
            if right is not None:
                self.assertLessEqual(score, right)


class ValveTests(unittest.TestCase):
    def test_discrete_valve_closes_with_polarized_energy(self):
        result = valve.audit_discrete_valve(14.13472514173469, 15)
        self.assertLess(result["max_reconstruction_error"], 1e-12)
        self.assertLess(result["max_green_curvature_error"], 1e-12)
        self.assertLess(result["trace_of_green_error"], 1e-12)
        self.assertLess(result["max_boundary_curvature_error"], 1e-12)
        self.assertLess(result["energy_ledger_error"], 1e-10)


if __name__ == "__main__":
    unittest.main()
