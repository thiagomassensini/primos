import CPFormal.Analytic.CpGenuineTiltQuantitativeDomination

/-!
# Explicit canonical tilt block bounds

The canonical `p = 3` camera has radius one.  This module combines the sharp
symmetric second-difference fencing lemma with the exact derivatives of
`x ↦ x^(-delta)`.  For `-1/2 < delta < 1/2`, `delta ≠ 0`, the absolute local
tilt is trapped between the same positive coefficient at the center and at
the left endpoint:

`|delta(delta+1)| center^(-delta-2) ≤ |Tilt(center)|`

and

`|Tilt(center)| ≤ |delta(delta+1)| (center-1)^(-delta-2)`.

These bounds retain the convex/concave sign and are independent of the phase
height.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-- First derivative of the transverse power profile. -/
def transverseRpowFirstDeriv (delta x : ℝ) : ℝ :=
  (-delta) * x ^ (-delta - 1)

/-- Second derivative of the transverse power profile. -/
def transverseRpowSecondDeriv (delta x : ℝ) : ℝ :=
  (-delta) * ((-delta - 1) * x ^ ((-delta - 1) - 1))

/-- Exact first derivative of `x ↦ x^(-delta)` away from zero. -/
theorem hasDerivAt_transverseRpow
    (delta : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ y ^ (-delta))
      (transverseRpowFirstDeriv delta x) x := by
  simpa [transverseRpowFirstDeriv] using
    (Real.hasDerivAt_rpow_const (x := x) (p := -delta) (Or.inl hx))

/-- Exact derivative of the first-derivative profile away from zero. -/
theorem hasDerivAt_transverseRpowFirstDeriv
    (delta : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (transverseRpowFirstDeriv delta)
      (transverseRpowSecondDeriv delta x) x := by
  simpa [transverseRpowFirstDeriv, transverseRpowSecondDeriv] using
    (Real.hasDerivAt_rpow_const
      (x := x) (p := -delta - 1) (Or.inl hx)).const_mul (-delta)

/-- Algebraic form of the transverse second derivative. -/
theorem transverseRpowSecondDeriv_eq
    (delta x : ℝ) :
    transverseRpowSecondDeriv delta x =
      delta * (delta + 1) * x ^ (-delta - 2) := by
  unfold transverseRpowSecondDeriv
  have hexponent : (-delta - 1) - 1 = -delta - 2 := by ring
  rw [hexponent]
  ring

/-- Convexity gives the midpoint lower estimate for the symmetric pair of
negative powers. -/
theorem two_mul_center_rpow_neg_le_pair
    {beta center t : ℝ}
    (hbeta : 0 < beta) (hcenter : 1 < center)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    2 * center ^ (-beta) ≤
      (center - t) ^ (-beta) + (center + t) ^ (-beta) := by
  have hminus : 0 < center - t := by linarith [ht.2]
  have hplus : 0 < center + t := by linarith [ht.1]
  have hconv :
      ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ ↦ x ^ (-beta)) :=
    (strictConvexOn_rpow_of_neg (by linarith)).1
  have hmid := hconv.2 hminus hplus
    (by norm_num : 0 ≤ (1 / 2 : ℝ))
    (by norm_num : 0 ≤ (1 / 2 : ℝ))
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hcomb :
      (2 : ℝ)⁻¹ * (center - t) +
          (2 : ℝ)⁻¹ * (center + t) = center := by
    ring
  have hmid' :
      center ^ (-beta) ≤
        (2 : ℝ)⁻¹ * (center - t) ^ (-beta) +
          (2 : ℝ)⁻¹ * (center + t) ^ (-beta) := by
    simpa [smul_eq_mul, hcomb] using hmid
  nlinarith [hmid']

/-- Monotonicity gives an endpoint upper estimate for the same symmetric
negative-power pair. -/
theorem pair_rpow_neg_le_two_mul_left
    {beta center t : ℝ}
    (hbeta : 0 < beta) (hcenter : 1 < center)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (center - t) ^ (-beta) + (center + t) ^ (-beta) ≤
      2 * (center - 1) ^ (-beta) := by
  have hleft : 0 < center - 1 := by linarith
  have hminusLe : center - 1 ≤ center - t := by linarith [ht.2]
  have hplusLe : center - 1 ≤ center + t := by linarith [ht.1]
  have hminus := Real.rpow_le_rpow_of_nonpos hleft hminusLe (by linarith)
  have hplus := Real.rpow_le_rpow_of_nonpos hleft hplusLe (by linarith)
  nlinarith

/-- Positive transverse displacement: lower canonical tilt bound. -/
theorem cpTilt_three_lower_of_delta_pos
    {delta center : ℝ} (hdelta : 0 < delta) (hcenter : 1 < center) :
    delta * (delta + 1) * center ^ (-delta - 2) ≤
      cpTilt 3 delta center := by
  have hbound := centeredSecondDifference_ge_of_pair_secondDeriv_ge
    (f := fun x : ℝ ↦ x ^ (-delta))
    (f' := transverseRpowFirstDeriv delta)
    (f'' := transverseRpowSecondDeriv delta)
    (center := center) (radius := (1 : ℝ))
    (C := delta * (delta + 1) * center ^ (-delta - 2))
    (by norm_num)
    (by
      intro t ht
      exact hasDerivAt_transverseRpow delta (by
        have : 0 < center - t := by linarith [ht.2]
        exact this.ne'))
    (by
      intro t ht
      exact hasDerivAt_transverseRpow delta (by
        have : 0 < center + t := by linarith [ht.1]
        exact this.ne'))
    (by
      intro t ht
      exact hasDerivAt_transverseRpowFirstDeriv delta (by
        have : 0 < center - t := by linarith [ht.2]
        exact this.ne'))
    (by
      intro t ht
      exact hasDerivAt_transverseRpowFirstDeriv delta (by
        have : 0 < center + t := by linarith [ht.1]
        exact this.ne'))
    (by
      intro t ht
      rw [transverseRpowSecondDeriv_eq,
        transverseRpowSecondDeriv_eq]
      have hpow := two_mul_center_rpow_neg_le_pair
        (beta := delta + 2) (center := center) (t := t)
        (by linarith) hcenter ht
      have hcoef : 0 ≤ delta * (delta + 1) := by positivity
      have hscaled := mul_le_mul_of_nonneg_left hpow hcoef
      have hexponent : -(delta + 2) = -delta - 2 := by ring
      rw [hexponent] at hscaled
      nlinarith [hscaled])
  rw [cpTilt_three_eq_cpPairTilt_one]
  unfold cpPairTilt
  nlinarith [hbound]

/-- Positive transverse displacement: upper canonical tilt bound. -/
theorem cpTilt_three_upper_of_delta_pos
    {delta center : ℝ} (hdelta : 0 < delta) (hcenter : 1 < center) :
    cpTilt 3 delta center ≤
      delta * (delta + 1) * (center - 1) ^ (-delta - 2) := by
  have hbound := centeredSecondDifference_le_of_pair_secondDeriv_le
    (f := fun x : ℝ ↦ x ^ (-delta))
    (f' := transverseRpowFirstDeriv delta)
    (f'' := transverseRpowSecondDeriv delta)
    (center := center) (radius := (1 : ℝ))
    (C := delta * (delta + 1) * (center - 1) ^ (-delta - 2))
    (by norm_num)
    (by
      intro t ht
      exact hasDerivAt_transverseRpow delta (by
        have : 0 < center - t := by linarith [ht.2]
        exact this.ne'))
    (by
      intro t ht
      exact hasDerivAt_transverseRpow delta (by
        have : 0 < center + t := by linarith [ht.1]
        exact this.ne'))
    (by
      intro t ht
      exact hasDerivAt_transverseRpowFirstDeriv delta (by
        have : 0 < center - t := by linarith [ht.2]
        exact this.ne'))
    (by
      intro t ht
      exact hasDerivAt_transverseRpowFirstDeriv delta (by
        have : 0 < center + t := by linarith [ht.1]
        exact this.ne'))
    (by
      intro t ht
      rw [transverseRpowSecondDeriv_eq,
        transverseRpowSecondDeriv_eq]
      have hpow := pair_rpow_neg_le_two_mul_left
        (beta := delta + 2) (center := center) (t := t)
        (by linarith) hcenter ht
      have hcoef : 0 ≤ delta * (delta + 1) := by positivity
      have hscaled := mul_le_mul_of_nonneg_left hpow hcoef
      have hexponent : -(delta + 2) = -delta - 2 := by ring
      rw [hexponent] at hscaled
      nlinarith [hscaled])
  rw [cpTilt_three_eq_cpPairTilt_one]
  unfold cpPairTilt
  nlinarith [hbound]

/-- Negative transverse displacement: lower signed canonical tilt bound. -/
theorem cpTilt_three_lower_of_delta_neg
    {delta center : ℝ}
    (hdeltaLower : -1 < delta) (hdelta : delta < 0)
    (hcenter : 1 < center) :
    delta * (delta + 1) * (center - 1) ^ (-delta - 2) ≤
      cpTilt 3 delta center := by
  have hbound := centeredSecondDifference_ge_of_pair_secondDeriv_ge
    (f := fun x : ℝ ↦ x ^ (-delta))
    (f' := transverseRpowFirstDeriv delta)
    (f'' := transverseRpowSecondDeriv delta)
    (center := center) (radius := (1 : ℝ))
    (C := delta * (delta + 1) * (center - 1) ^ (-delta - 2))
    (by norm_num)
    (by
      intro t ht
      exact hasDerivAt_transverseRpow delta (by
        have : 0 < center - t := by linarith [ht.2]
        exact this.ne'))
    (by
      intro t ht
      exact hasDerivAt_transverseRpow delta (by
        have : 0 < center + t := by linarith [ht.1]
        exact this.ne'))
    (by
      intro t ht
      exact hasDerivAt_transverseRpowFirstDeriv delta (by
        have : 0 < center - t := by linarith [ht.2]
        exact this.ne'))
    (by
      intro t ht
      exact hasDerivAt_transverseRpowFirstDeriv delta (by
        have : 0 < center + t := by linarith [ht.1]
        exact this.ne'))
    (by
      intro t ht
      rw [transverseRpowSecondDeriv_eq,
        transverseRpowSecondDeriv_eq]
      have hpow := pair_rpow_neg_le_two_mul_left
        (beta := delta + 2) (center := center) (t := t)
        (by linarith) hcenter ht
      have hcoef : delta * (delta + 1) ≤ 0 := by
        exact (mul_nonpos_of_nonpos_of_nonneg hdelta.le (by linarith))
      have hscaled := mul_le_mul_of_nonpos_left hpow hcoef
      have hexponent : -(delta + 2) = -delta - 2 := by ring
      rw [hexponent] at hscaled
      nlinarith [hscaled])
  rw [cpTilt_three_eq_cpPairTilt_one]
  unfold cpPairTilt
  nlinarith [hbound]

/-- Negative transverse displacement: upper signed canonical tilt bound. -/
theorem cpTilt_three_upper_of_delta_neg
    {delta center : ℝ}
    (hdeltaLower : -1 < delta) (hdelta : delta < 0)
    (hcenter : 1 < center) :
    cpTilt 3 delta center ≤
      delta * (delta + 1) * center ^ (-delta - 2) := by
  have hbound := centeredSecondDifference_le_of_pair_secondDeriv_le
    (f := fun x : ℝ ↦ x ^ (-delta))
    (f' := transverseRpowFirstDeriv delta)
    (f'' := transverseRpowSecondDeriv delta)
    (center := center) (radius := (1 : ℝ))
    (C := delta * (delta + 1) * center ^ (-delta - 2))
    (by norm_num)
    (by
      intro t ht
      exact hasDerivAt_transverseRpow delta (by
        have : 0 < center - t := by linarith [ht.2]
        exact this.ne'))
    (by
      intro t ht
      exact hasDerivAt_transverseRpow delta (by
        have : 0 < center + t := by linarith [ht.1]
        exact this.ne'))
    (by
      intro t ht
      exact hasDerivAt_transverseRpowFirstDeriv delta (by
        have : 0 < center - t := by linarith [ht.2]
        exact this.ne'))
    (by
      intro t ht
      exact hasDerivAt_transverseRpowFirstDeriv delta (by
        have : 0 < center + t := by linarith [ht.1]
        exact this.ne'))
    (by
      intro t ht
      rw [transverseRpowSecondDeriv_eq,
        transverseRpowSecondDeriv_eq]
      have hpow := two_mul_center_rpow_neg_le_pair
        (beta := delta + 2) (center := center) (t := t)
        (by linarith) hcenter ht
      have hcoef : delta * (delta + 1) ≤ 0 := by
        exact (mul_nonpos_of_nonpos_of_nonneg hdelta.le (by linarith))
      have hscaled := mul_le_mul_of_nonpos_left hpow hcoef
      have hexponent : -(delta + 2) = -delta - 2 := by ring
      rw [hexponent] at hscaled
      nlinarith [hscaled])
  rw [cpTilt_three_eq_cpPairTilt_one]
  unfold cpPairTilt
  nlinarith [hbound]

/-- Uniform lower absolute bound in the transverse strip. -/
theorem abs_cpTilt_three_lower_bound
    {delta center : ℝ}
    (hdeltaLower : -(1 : ℝ) / 2 < delta)
    (hdeltaUpper : delta < (1 : ℝ) / 2)
    (hdelta : delta ≠ 0) (hcenter : 1 < center) :
    |delta * (delta + 1)| * center ^ (-delta - 2) ≤
      |cpTilt 3 delta center| := by
  rcases lt_or_gt_of_ne hdelta with hneg | hpos
  · have hcoef : delta * (delta + 1) < 0 :=
      mul_neg_of_neg_of_pos hneg (by linarith)
    have htilt : cpTilt 3 delta center < 0 :=
      cpTilt_neg_of_neg_one_lt_delta 3 (by norm_num) (by norm_num)
        (by linarith) hneg (by simpa [CPFormal.Genuine.Cp.halfRange] using hcenter)
    rw [abs_of_neg hcoef, abs_of_neg htilt]
    have hbound := cpTilt_three_upper_of_delta_neg
      (by linarith) hneg hcenter
    nlinarith [hbound]
  · have hcoef : 0 < delta * (delta + 1) := by positivity
    have htilt : 0 < cpTilt 3 delta center :=
      cpTilt_pos_of_delta_pos 3 (by norm_num) (by norm_num)
        hpos (by simpa [CPFormal.Genuine.Cp.halfRange] using hcenter)
    rw [abs_of_pos hcoef, abs_of_pos htilt]
    exact cpTilt_three_lower_of_delta_pos hpos hcenter

/-- Uniform upper absolute bound in the transverse strip. -/
theorem abs_cpTilt_three_upper_bound
    {delta center : ℝ}
    (hdeltaLower : -(1 : ℝ) / 2 < delta)
    (hdeltaUpper : delta < (1 : ℝ) / 2)
    (hdelta : delta ≠ 0) (hcenter : 1 < center) :
    |cpTilt 3 delta center| ≤
      |delta * (delta + 1)| * (center - 1) ^ (-delta - 2) := by
  rcases lt_or_gt_of_ne hdelta with hneg | hpos
  · have hcoef : delta * (delta + 1) < 0 :=
      mul_neg_of_neg_of_pos hneg (by linarith)
    have htilt : cpTilt 3 delta center < 0 :=
      cpTilt_neg_of_neg_one_lt_delta 3 (by norm_num) (by norm_num)
        (by linarith) hneg (by simpa [CPFormal.Genuine.Cp.halfRange] using hcenter)
    rw [abs_of_neg htilt, abs_of_neg hcoef]
    have hbound := cpTilt_three_lower_of_delta_neg
      (by linarith) hneg hcenter
    nlinarith [hbound]
  · have hcoef : 0 < delta * (delta + 1) := by positivity
    have htilt : 0 < cpTilt 3 delta center :=
      cpTilt_pos_of_delta_pos 3 (by norm_num) (by norm_num)
        hpos (by simpa [CPFormal.Genuine.Cp.halfRange] using hcenter)
    rw [abs_of_pos htilt, abs_of_pos hcoef]
    exact cpTilt_three_upper_of_delta_pos hpos hcenter

end

end CPFormal.Analytic.Cp
