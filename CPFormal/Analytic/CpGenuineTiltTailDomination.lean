import CPFormal.Analytic.CpGenuineTiltBlockBounds

/-!
# Tail domination for the phase-bearing Genuine tilt

This module starts the quantitative passage from local convexity/concavity to
the original complex tilt trace.  It records the exact norm of the critical
carrier and transports the sharp real tilt bounds to every canonical complex
block.  The remaining comparison is then a scalar estimate between the
canonical centers `3, 6, 9, ...`.
-/

open scoped BigOperators

namespace CPFormal.Analytic.Cp

noncomputable section

/-- In the critical strip the transverse displacement lies in `(-1/2,1/2)`. -/
theorem criticalDisplacement_mem_openHalf_of_mem_strip
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    -(1 : ℝ) / 2 < criticalDisplacement s.re ∧
      criticalDisplacement s.re < (1 : ℝ) / 2 := by
  constructor <;> unfold criticalDisplacement <;> linarith [hs.1, hs.2]

/-- Off the half-abscissa, the transverse displacement is nonzero. -/
theorem criticalDisplacement_ne_zero_of_re_ne_half
    {s : ℂ} (hoff : s.re ≠ (1 : ℝ) / 2) :
    criticalDisplacement s.re ≠ 0 := by
  intro hzero
  apply hoff
  unfold criticalDisplacement at hzero
  linarith

/-- Exact modulus of the critical carrier: the height contributes only phase. -/
theorem norm_criticalLineDirichletCarrier
    (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖criticalLineDirichletCarrier s x‖ = x ^ (-(1 : ℝ) / 2) := by
  unfold criticalLineDirichletCarrier
  simpa using
    (Complex.norm_cpow_eq_rpow_re_of_pos hx
      (-((1 : ℂ) / 2 + Complex.I * s.im)))

/-- Exact norm of a canonical phase-bearing tilt block. -/
theorem norm_canonicalCriticalWeightedTiltBlock
    (k : ℕ) (s : ℂ) :
    ‖canonicalCriticalWeightedTiltBlock k s‖ =
      (canonicalRealCpCenter k) ^ (-(1 : ℝ) / 2) *
        |cpTilt 3 (criticalDisplacement s.re) (canonicalRealCpCenter k)| := by
  unfold canonicalCriticalWeightedTiltBlock localCriticalLineCarrier
  rw [norm_mul]
  have hcenter : 0 < canonicalRealCpCenter k := by
    unfold canonicalRealCpCenter
    positivity
  rw [norm_criticalLineDirichletCarrier s hcenter]
  simp

/-- Every canonical center lies to the right of the radius-one camera. -/
theorem one_lt_canonicalRealCpCenter (k : ℕ) :
    (1 : ℝ) < canonicalRealCpCenter k := by
  unfold canonicalRealCpCenter
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  nlinarith

/-- Sharp lower norm bound for the first phase-bearing tilt block. -/
theorem canonicalCriticalWeightedTiltBlock_zero_lower_bound
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    (3 : ℝ) ^ (-(1 : ℝ) / 2) *
        (|criticalDisplacement s.re * (criticalDisplacement s.re + 1)| *
          (3 : ℝ) ^ (-criticalDisplacement s.re - 2)) ≤
      ‖canonicalCriticalWeightedTiltBlock 0 s‖ := by
  rw [norm_canonicalCriticalWeightedTiltBlock]
  have hbounds := criticalDisplacement_mem_openHalf_of_mem_strip hs
  have hdelta := criticalDisplacement_ne_zero_of_re_ne_half hoff
  have htilt := abs_cpTilt_three_lower_bound
    hbounds.1 hbounds.2 hdelta (by norm_num : (1 : ℝ) < 3)
  have hscale : 0 ≤ (3 : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg _ _
  have hmul := mul_le_mul_of_nonneg_left htilt hscale
  simpa [canonicalRealCpCenter] using hmul

/-- Sharp upper norm bound for every canonical phase-bearing tilt block. -/
theorem canonicalCriticalWeightedTiltBlock_upper_bound
    (k : ℕ) {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    ‖canonicalCriticalWeightedTiltBlock k s‖ ≤
      (canonicalRealCpCenter k) ^ (-(1 : ℝ) / 2) *
        (|criticalDisplacement s.re * (criticalDisplacement s.re + 1)| *
          (canonicalRealCpCenter k - 1) ^
            (-criticalDisplacement s.re - 2)) := by
  rw [norm_canonicalCriticalWeightedTiltBlock]
  have hbounds := criticalDisplacement_mem_openHalf_of_mem_strip hs
  have hdelta := criticalDisplacement_ne_zero_of_re_ne_half hoff
  have htilt := abs_cpTilt_three_upper_bound
    hbounds.1 hbounds.2 hdelta (one_lt_canonicalRealCpCenter k)
  have hscale :
      0 ≤ (canonicalRealCpCenter k) ^ (-(1 : ℝ) / 2) :=
    Real.rpow_nonneg _ _
  exact mul_le_mul_of_nonneg_left htilt hscale

end

end CPFormal.Analytic.Cp
