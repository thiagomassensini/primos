from __future__ import annotations

import ast
import contextlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path

import numpy as np


EXPERIMENTS = Path(__file__).resolve().parent
if str(EXPERIMENTS) not in sys.path:
    sys.path.insert(0, str(EXPERIMENTS))

import c2_real_rotation_operator as operator


class RealRotationOperatorTests(unittest.TestCase):
    def test_rotation_matrix_and_accelerated_column_agree(self) -> None:
        angles = np.array([-3.0, -0.25, 0.0, 1.75])
        matrices = operator.rotation_matrix(angles)
        e1 = np.array([1.0, 0.0])
        explicit = matrices @ e1
        accelerated = operator.rotate_unit_axis(angles)
        np.testing.assert_allclose(explicit, accelerated, rtol=0.0, atol=0.0)

        identity = np.eye(2)
        for matrix in matrices:
            np.testing.assert_allclose(matrix.T @ matrix, identity, atol=2e-15)
            self.assertAlmostEqual(float(np.linalg.det(matrix)), 1.0, places=14)

    def test_real_spectral_state_has_canonical_amplitude(self) -> None:
        state = operator.real_spectral_state(14.1347, 32)
        norms_sq = np.sum(state * state, axis=1)
        expected = 1.0 / np.arange(1, 33, dtype=np.float64)
        np.testing.assert_allclose(norms_sq, expected, rtol=2e-15, atol=2e-15)

    def test_prime_camera_matrix_inverse(self) -> None:
        for p in (3, 5, 7, 11):
            matrix = operator.calibration_matrix(14.1347, p)
            inverse = operator.inverse_calibration_matrix(14.1347, p)
            np.testing.assert_allclose(matrix @ inverse, np.eye(2), atol=3e-15)

            vectors = np.array([[1.0, 2.0], [-3.0, 0.25]])
            contracted = operator.apply_inverse_calibration(vectors, 14.1347, p)
            explicit = vectors @ inverse.T
            np.testing.assert_allclose(contracted, explicit, atol=3e-15)

    def test_real_score_matches_legacy_scalar_reference(self) -> None:
        cameras = (3, 5, 7, 11)
        models = operator.build_prime_models(cameras, 24)
        ts = np.array([11.0, 14.1347, 21.0220, 29.25])
        real_scores = np.asarray(operator.evaluate_operator_chunk(ts, models))

        result = np.zeros(ts.shape[0], dtype=np.complex128)
        energy = np.zeros(ts.shape[0], dtype=np.float64)
        coordinate_count = 0
        camera_count = len(cameras)
        for model in models:
            seed = model["seed_amp"][None, :] * np.exp(
                -1j * ts[:, None] * model["seed_log"][None, :]
            )
            center = model["center_amp"][None, :] * np.exp(
                -1j * ts[:, None] * model["center_log"][None, :]
            )
            minus = model["minus_amp"][None, :, :] * np.exp(
                -1j * ts[:, None, None] * model["minus_log"][None, :, :]
            )
            plus = model["plus_amp"][None, :, :] * np.exp(
                -1j * ts[:, None, None] * model["plus_log"][None, :, :]
            )
            bracket = minus - 2.0 * center[:, :, None] + plus
            chart = np.sum(seed, axis=1) + np.sum(bracket, axis=(1, 2))
            chart_energy = np.sum(np.abs(seed) ** 2, axis=1) + np.sum(
                np.abs(bracket) ** 2, axis=(1, 2)
            )
            p = int(model["p"])
            factor = 1.0 - np.sqrt(p) * np.exp(-1j * ts * np.log(p))
            result += chart / (factor * camera_count)
            energy += chart_energy / (np.abs(factor) ** 2 * camera_count**2)
            coordinate_count += int(model["coordinate_count"])
        reference = np.abs(result) ** 2 / (coordinate_count * energy)
        np.testing.assert_allclose(real_scores, reference, rtol=3e-13, atol=3e-16)

    def test_known_m1024_mechanism_checkpoint(self) -> None:
        report = operator.evaluate_mechanism(14.1347, (3, 5, 7, 11), 1024)
        self.assertEqual(report["coordinate_count"], 11275)
        self.assertAlmostEqual(report["total_energy"], 0.16447463045995198, places=14)
        self.assertAlmostEqual(report["score"], 4.98224443013724e-13, places=24)
        self.assertLess(report["score_consistency_error"], 1e-24)
        self.assertGreater(report["blind_fraction"], 0.999999999999)
        for camera in report["camera_reports"]:
            self.assertLess(camera["calibration_inverse_error"], 1e-14)

    def test_green_boundary_return_identity_and_energy(self) -> None:
        report = operator.audit_green_boundary_return(14.13472514173469, 15)
        errors = report["errors"]
        energy = report["energy"]
        self.assertLess(errors["max_reconstruction"], 1e-12)
        self.assertLess(errors["max_green_curvature"], 1e-12)
        self.assertLess(errors["trace_of_green"], 1e-15)
        self.assertLess(errors["max_boundary_curvature"], 1e-12)
        self.assertLess(energy["ledger_error"], 1e-10)
        self.assertGreater(energy["green"], 2000.0)
        self.assertGreater(energy["boundary_return"], 2000.0)
        self.assertLess(energy["polarized_cross_term"], -4000.0)

    def test_operator_source_has_no_complex_runtime_constructs(self) -> None:
        source_path = Path(operator.__file__).resolve()
        tree = ast.parse(source_path.read_text(encoding="utf-8"))
        complex_constants = [
            node
            for node in ast.walk(tree)
            if isinstance(node, ast.Constant) and isinstance(node.value, complex)
        ]
        forbidden_attributes = [
            node.attr
            for node in ast.walk(tree)
            if isinstance(node, ast.Attribute)
            and node.attr in {"complex64", "complex128"}
        ]
        forbidden_calls = [
            node
            for node in ast.walk(tree)
            if isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id == "complex"
        ]
        self.assertEqual(complex_constants, [])
        self.assertEqual(forbidden_attributes, [])
        self.assertEqual(forbidden_calls, [])

    def test_cli_aliases_camera_selection_and_output(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "audit.json"
            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                status = operator.main(
                    [
                        "--tmin",
                        "14.12",
                        "--tmax",
                        "14.15",
                        "--grid",
                        "0.001",
                        "--cutoff",
                        "16",
                        "--camera-prime",
                        "3",
                        "--threshold",
                        "-1",
                        "--prominence",
                        "0",
                        "--no-refine",
                        "--show",
                        "all",
                        "--inspect-t",
                        "14.1347",
                        "--workers",
                        "1",
                        "--output",
                        str(output),
                    ]
                )
            self.assertEqual(status, 0)
            payload = json.loads(output.read_text(encoding="utf-8"))
            self.assertEqual(payload["operator"]["coordinate_field"], "R^2")
            self.assertEqual(payload["operator"]["cameras"], [3])
            self.assertEqual(payload["operator"]["cutoff"], 16)
            self.assertFalse(payload["selection"]["refinement_requested"])
            self.assertIn("green_boundary_return", payload["diagnostics"][-1])
            self.assertIn("REAL ROTATION MATRICES", stdout.getvalue())


if __name__ == "__main__":
    unittest.main()
