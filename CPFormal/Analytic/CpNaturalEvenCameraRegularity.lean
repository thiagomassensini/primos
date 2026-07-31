import CPFormal.Analytic.CpNaturalCameraFactor

/-!
# Uniform regularity of the even natural-camera factor

The exact finite normal form of a natural even camera of width `b = 2a`
selects the factor

`1 - a^(-s) - (b - 2) b^(-s)`.

On the critical line, the last term has norm `(b - 2) / sqrt b`, while the
omitted middle-residue term has norm `1 / sqrt a`.  For every even `b ≥ 6`,
the former is strictly larger than the norm of the unit seed plus the latter.
Consequently the factor cannot vanish.

This file contains only the real arithmetic needed to discharge the
domination hypothesis isolated in `CpNaturalCameraFactor`.  In fact, the
estimate holds for every natural `b ≥ 6`; evenness is retained in the final
theorem to record the camera geometry.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Squaring a negative half power gives the reciprocal. -/
theorem rpow_neg_half_sq (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (-(1 : ℝ) / 2)) ^ 2 = x⁻¹ := by
  calc
    (x ^ (-(1 : ℝ) / 2)) ^ 2 =
        x ^ ((-(1 : ℝ) / 2) * (2 : ℝ)) := by
      exact (Real.rpow_mul_natCast hx (-(1 : ℝ) / 2) 2).symm
    _ = x ^ (-1 : ℝ) := by
      congr 1
      ring
    _ = x⁻¹ := by
      simpa using Real.rpow_neg_one x

/-- A rational upper bound for the largest omitted-residue amplitude. -/
theorem three_rpow_neg_half_lt_three_fifths :
    (3 : ℝ) ^ (-(1 : ℝ) / 2) < (3 : ℝ) / 5 := by
  let y : ℝ := (3 : ℝ) ^ (-(1 : ℝ) / 2)
  have hyPos : 0 < y := by
    dsimp [y]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hySq : y ^ 2 = (3 : ℝ)⁻¹ := by
    dsimp [y]
    exact rpow_neg_half_sq 3 (by norm_num)
  by_contra hnot
  have hlower : (3 : ℝ) / 5 ≤ y := le_of_not_gt hnot
  have hsquares :
      ((3 : ℝ) / 5) ^ 2 ≤ y ^ 2 :=
    (sq_le_sq₀ (by norm_num) hyPos.le).2 hlower
  rw [hySq] at hsquares
  norm_num at hsquares

/--
For `b ≥ 6`, the omitted middle-residue amplitude is strictly below `3/5`.
-/
theorem half_width_rpow_neg_half_lt_three_fifths
    (b : ℕ) (hb : 6 ≤ b) :
    ((b / 2 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) < (3 : ℝ) / 5 := by
  have hhalfNat : 3 ≤ b / 2 := by omega
  have hhalfReal : (3 : ℝ) ≤ ((b / 2 : ℕ) : ℝ) := by
    exact_mod_cast hhalfNat
  have hpow :
      ((b / 2 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) ≤
        (3 : ℝ) ^ (-(1 : ℝ) / 2) := by
    exact
      Real.rpow_le_rpow_of_nonpos
        (by norm_num : (0 : ℝ) < 3) hhalfReal (by norm_num)
  exact lt_of_le_of_lt hpow three_rpow_neg_half_lt_three_fifths

/--
For `b ≥ 6`, the full right-center channel has critical norm greater than
`8/5`.
-/
theorem eight_fifths_lt_sub_two_mul_rpow_neg_half
    (b : ℕ) (hb : 6 ≤ b) :
    (8 : ℝ) / 5 <
      ((b - 2 : ℕ) : ℝ) * (b : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hbTwo : 2 ≤ b := by omega
  have hbReal : (6 : ℝ) ≤ (b : ℝ) := by
    exact_mod_cast hb
  have hbPos : 0 < (b : ℝ) := by positivity
  have hcastSub :
      ((b - 2 : ℕ) : ℝ) = (b : ℝ) - 2 := by
    rw [Nat.cast_sub hbTwo]
    norm_num
  rw [hcastSub]
  let y : ℝ := (b : ℝ) ^ (-(1 : ℝ) / 2)
  have hyPos : 0 < y := by
    dsimp [y]
    exact Real.rpow_pos_of_pos hbPos _
  have hySq : y ^ 2 = ((b : ℝ))⁻¹ := by
    dsimp [y]
    exact rpow_neg_half_sq (b : ℝ) hbPos.le
  have hpoly :
      64 * (b : ℝ) < 25 * ((b : ℝ) - 2) ^ 2 := by
    have hproduct :
        0 ≤ ((b : ℝ) - 6) * (25 * (b : ℝ) - 14) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  by_contra hnot
  have hupper :
      ((b : ℝ) - 2) * y ≤ (8 : ℝ) / 5 :=
    le_of_not_gt hnot
  have hleftNonneg : 0 ≤ ((b : ℝ) - 2) * y :=
    mul_nonneg (by linarith) hyPos.le
  have hsquares :
      (((b : ℝ) - 2) * y) ^ 2 ≤ ((8 : ℝ) / 5) ^ 2 :=
    (sq_le_sq₀ hleftNonneg (by norm_num)).2 hupper
  rw [mul_pow, hySq] at hsquares
  have hscaled :=
    mul_le_mul_of_nonneg_left hsquares hbPos.le
  have hcancel :
      (b : ℝ) * (((b : ℝ) - 2) ^ 2 * (b : ℝ)⁻¹) =
        ((b : ℝ) - 2) ^ 2 := by
    calc
      (b : ℝ) * (((b : ℝ) - 2) ^ 2 * (b : ℝ)⁻¹) =
          ((b : ℝ) - 2) ^ 2 * ((b : ℝ) * (b : ℝ)⁻¹) := by
        ring
      _ = ((b : ℝ) - 2) ^ 2 := by
        rw [mul_inv_cancel₀ (ne_of_gt hbPos), mul_one]
  rw [hcancel] at hscaled
  nlinarith

/--
The explicit norm-domination inequality required by the even-camera factor
holds uniformly from width `6` onward.
-/
theorem naturalEvenCamera_critical_domination
    (b : ℕ) (hb : 6 ≤ b) :
    1 + ((b / 2 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) <
      ((b - 2 : ℕ) : ℝ) * (b : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hmiddle :=
    half_width_rpow_neg_half_lt_three_fifths b hb
  have hcenter :=
    eight_fifths_lt_sub_two_mul_rpow_neg_half b hb
  linarith

/--
Every even natural-camera factor of width at least `6` is nonzero on the
critical line.
-/
theorem naturalEvenCameraFactor_ne_zero_on_criticalLine_of_six_le
    (b : ℕ) (_hbeven : Even b) (hb : 6 ≤ b)
    {s : ℂ} (hs : s.re = (1 : ℝ) / 2) :
    naturalEvenCameraFactor b s ≠ 0 := by
  exact
    naturalEvenCameraFactor_ne_zero_of_criticalLine_of_domination
      b (by omega) hs (naturalEvenCamera_critical_domination b hb)

/--
The same regularity statement specialized to the complex parameter encoded
by the native rotating state.
-/
theorem naturalEvenCameraFactor_nativeCarryCriticalParameter_ne_zero
    (b : ℕ) (hbeven : Even b) (hb : 6 ≤ b) (time : ℝ) :
    naturalEvenCameraFactor b (nativeCarryCriticalParameter time) ≠ 0 := by
  exact
    naturalEvenCameraFactor_ne_zero_on_criticalLine_of_six_le
      b hbeven hb (nativeCarryCriticalParameter_re time)

end

end CPFormal.Analytic.Cp
