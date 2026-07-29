#!/usr/bin/env python3

from __future__ import annotations

import sys
import unittest
from pathlib import Path

import numpy as np


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import c2_real_rotation_minimal as minimal


class RealRotationMinimalTests(unittest.TestCase):
    def test_rotation_state_is_real_float64(self) -> None:
        states = minimal.rotation_states(
            np.array([0.0], dtype=np.float64),
            np.log(np.array([1.0, 4.0], dtype=np.float64)),
            np.array([1.0, 0.5], dtype=np.float64),
        )
        self.assertEqual(states.dtype, np.float64)
        np.testing.assert_array_equal(
            states,
            np.array([[[1.0, 0.0], [0.5, 0.0]]], dtype=np.float64),
        )

    def test_first_resonance_is_visible_in_each_camera(self) -> None:
        frequencies = np.array([14.1345, 15.0], dtype=np.float64)
        for camera in (3, 5, 7, 11):
            with self.subTest(camera=camera):
                scores = minimal.camera_score(
                    frequencies, minimal.build_camera(camera, cutoff=128)
                )
                self.assertEqual(scores.dtype, np.float64)
                self.assertLess(scores[0], minimal.ZERO_SCORE)
                self.assertGreater(scores[1], minimal.ZERO_SCORE)

    def test_grid_selection_does_not_refine(self) -> None:
        scores = np.array(
            [1.0, 1e-7, 1.0, 1e-8, 2e-8], dtype=np.float64
        )
        np.testing.assert_array_equal(
            minimal.grid_zeros(scores), np.array([1, 3], dtype=np.int64)
        )

    def test_only_four_cli_options_are_exposed(self) -> None:
        option_strings = {
            option
            for action in minimal.build_parser()._actions
            for option in action.option_strings
            if option != "--help" and option != "-h"
        }
        self.assertEqual(
            option_strings, {"--tmax", "--camera", "--cutoff", "--grid"}
        )


if __name__ == "__main__":
    unittest.main()
