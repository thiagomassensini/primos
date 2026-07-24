import CPFormal.Analytic.CpGenuineCompatibility
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Identification of the canonical Genuine continuation with Riemann zeta

The bracketed prime chart agrees on `re(s) > 1` with

`(1 - p^(1-s)) * zeta(s)`.

Both factors are singular at `s = 1`, but their product has a removable
singularity.  We remove it canonically using the divided slope of the camera
factor and Mathlib's entire regularization `riemannZeta₁`.  The identity
principle then identifies the resulting analytic function with the bracketed
chart on the complete half-plane `re(s) > -1`.

Since the camera factor is nonzero in the open critical strip, the canonical
Genuine quotient is literally Mathlib's `riemannZeta` there.  As a first
consequence, a Genuine zero is stable under the reflected parameter
`1 - conj(s)` by the classical functional equation and conjugation symmetry.
-/

open scoped BigOperators Topology

namespace CPFormal.Analytic.Cp

open Set Filter ComplexConjugate

noncomputable section

/-- The original absolutely convergent Genuine Dirichlet series is the Riemann
zeta series. -/
theorem genuineDirichlet_eq_riemannZeta
    {s : ℂ} (hs : 1 < s.re) :
    genuineDirichlet s = riemannZeta s := by
  rw [genuineDirichlet, zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  apply tsum_congr
  intro n
  simp [dirichletTerm, Complex.cpow_neg]

/-- The camera factor has derivative `log(p)` at its removable zero `s = 1`. -/
theorem hasDerivAt_cpChartFactor_one
    (p : ℕ) (hp : Nat.Prime p) :
    HasDerivAt (cpChartFactor p) (Real.log (p : ℝ) : ℂ) 1 := by
  have hpC : (p : ℂ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  have hinner :
      HasDerivAt (fun z : ℂ => 1 - z) (-1) 1 := by
    simpa using
      (hasDerivAt_const (x := (1 : ℂ)) (c := (1 : ℂ))).sub
        (hasDerivAt_id (1 : ℂ))
  have hpow := hinner.const_cpow (c := (p : ℂ)) (Or.inl hpC)
  have hfactor :=
    (hasDerivAt_const (x := (1 : ℂ)) (c := (1 : ℂ))).sub hpow
  simpa [cpChartFactor,
    Complex.ofReal_log (show 0 ≤ (p : ℝ) by positivity)] using hfactor

/-- Canonical divided camera factor, analytically completed at `s = 1`. -/
def cpChartFactorSlope (p : ℕ) : ℂ → ℂ :=
  dslope (cpChartFactor p) 1

/-- Away from `1`, the divided slope is the literal quotient by `s - 1`. -/
theorem cpChartFactorSlope_eq_div
    (p : ℕ) {s : ℂ} (hs : s ≠ 1) :
    cpChartFactorSlope p s = cpChartFactor p s / (s - 1) := by
  rw [cpChartFactorSlope, dslope_of_ne _ hs, slope_def_field]
  simp [cpChartFactor]

/-- At the removable point, the divided camera factor is `log(p)`. -/
@[simp] theorem cpChartFactorSlope_one
    (p : ℕ) (hp : Nat.Prime p) :
    cpChartFactorSlope p 1 = (Real.log (p : ℝ) : ℂ) := by
  rw [cpChartFactorSlope, dslope_same,
    (hasDerivAt_cpChartFactor_one p hp).deriv]

/-- The divided camera factor is entire. -/
theorem differentiable_cpChartFactorSlope
    (p : ℕ) (hp : Nat.Prime p) :
    Differentiable ℂ (cpChartFactorSlope p) := by
  rw [← differentiableOn_univ]
  exact
    (Complex.differentiableOn_dslope
      (f := cpChartFactor p) (a := (1 : ℂ)) (s := Set.univ)
      (by simp : Set.univ ∈ 𝓝 (1 : ℂ))).2
      (differentiable_cpChartFactor p hp).differentiableOn

/-- Entire regularization of the prime chart using Mathlib's `riemannZeta₁`. -/
def riemannCpChart (p : ℕ) (s : ℂ) : ℂ :=
  cpChartFactorSlope p s * riemannZeta₁ s

/-- The regularized chart is entire. -/
theorem differentiable_riemannCpChart
    (p : ℕ) (hp : Nat.Prime p) :
    Differentiable ℂ (riemannCpChart p) :=
  (differentiable_cpChartFactorSlope p hp).mul
    differentiable_riemannZeta₁

/-- Away from the removable point, the regularization is the camera factor
multiplied by Riemann zeta. -/
theorem riemannCpChart_eq_factor_mul_riemannZeta
    (p : ℕ) (hp : Nat.Prime p) {s : ℂ} (hs : s ≠ 1) :
    riemannCpChart p s = cpChartFactor p s * riemannZeta s := by
  rw [riemannCpChart, cpChartFactorSlope_eq_div p hs,
    riemannZeta_eq_inv_sub_mul hs]
  ring

/-- Analyticity of the regularized chart on the bracket half-plane. -/
theorem analyticOnNhd_riemannCpChart_bracketHalfPlane
    (p : ℕ) (hp : Nat.Prime p) :
    AnalyticOnNhd ℂ (riemannCpChart p) bracketHalfPlane :=
  (differentiable_riemannCpChart p hp).differentiableOn.analyticOnNhd
    isOpen_bracketHalfPlane

/-- In the original half-plane of absolute convergence, the regularized chart
is the same Genuine factorization used by the bracket construction. -/
theorem riemannCpChart_eq_factor_mul_genuineDirichlet
    (p : ℕ) (hp : Nat.Prime p) {s : ℂ} (hs : 1 < s.re) :
    riemannCpChart p s =
      (1 - (p : ℂ) ^ (1 - s)) * genuineDirichlet s := by
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs
  rw [riemannCpChart_eq_factor_mul_riemannZeta p hp hs1,
    ← genuineDirichlet_eq_riemannZeta hs]
  rfl

/-- The bracketed chart is exactly the regularized Riemann-zeta camera chart
throughout its analytic half-plane. -/
theorem bracketedDirichletChart_eq_riemannCpChart
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {s : ℂ} (hs : s ∈ bracketHalfPlane) :
    bracketedDirichletChart p s = riemannCpChart p s := by
  have hEq :=
    bracketedDirichletChart_unique_analytic_continuation
      p hp hpodd (riemannCpChart p)
      (analyticOnNhd_riemannCpChart_bracketHalfPlane p hp)
      (fun z hz => riemannCpChart_eq_factor_mul_genuineDirichlet p hp hz)
  exact (hEq hs).symm

/-- Canonical identification on the complete open critical strip. -/
theorem genuineContinuation_eq_riemannZeta
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    genuineContinuation s = riemannZeta s := by
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs
  have hhalfPlane : s ∈ bracketHalfPlane := by
    change -1 < s.re
    linarith [hs.1]
  have hfactor : cpChartFactor 3 s ≠ 0 :=
    cpChartFactor_ne_zero_on_genuineCriticalStrip 3 (by norm_num) hs
  have hmul :
      cpChartFactor 3 s * genuineContinuation s =
        cpChartFactor 3 s * riemannZeta s := by
    calc
      cpChartFactor 3 s * genuineContinuation s =
          bracketedDirichletChart 3 s :=
        (bracketedDirichletChart_eq_cpChartFactor_mul_genuineContinuation
          3 (by norm_num) (by norm_num) hs).symm
      _ = riemannCpChart 3 s :=
        bracketedDirichletChart_eq_riemannCpChart
          3 (by norm_num) (by norm_num) hhalfPlane
      _ = cpChartFactor 3 s * riemannZeta s :=
        riemannCpChart_eq_factor_mul_riemannZeta
          3 (by norm_num) hs1
  exact mul_left_cancel₀ hfactor hmul

/-- Reflection preserves the open critical strip; this local name avoids
colliding with the later Green-budget interface. -/
theorem reflectedParameter_mem_genuineCriticalStrip_zeta
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    reflectedParameter s ∈ genuineCriticalStrip := by
  constructor
  · rw [reflectedParameter_re]
    linarith [hs.2]
  · rw [reflectedParameter_re]
    linarith [hs.1]

/-- A zero of the canonical Genuine continuation is also a zero at the
reflected parameter `1 - conj(s)`. -/
theorem genuineContinuation_reflectedParameter_eq_zero_of_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    genuineContinuation (reflectedParameter s) = 0 := by
  have hzeta : riemannZeta s = 0 := by
    rw [← genuineContinuation_eq_riemannZeta hs]
    exact hzero
  have hconj : riemannZeta (starRingEnd ℂ s) = 0 := by
    rw [riemannZeta_conj, hzeta, map_zero]
  have hnotNeg : ∀ n : ℕ, starRingEnd ℂ s ≠ -n := by
    intro n hneg
    have hre := congrArg Complex.re hneg
    simp at hre
    linarith [hs.1]
  have hnotOne : starRingEnd ℂ s ≠ 1 := by
    intro hone
    have hre := congrArg Complex.re hone
    simp at hre
    linarith [hs.2]
  have hrefZeta : riemannZeta (reflectedParameter s) = 0 := by
    unfold reflectedParameter
    rw [riemannZeta_one_sub hnotNeg hnotOne, hconj]
    ring
  rw [genuineContinuation_eq_riemannZeta
    (reflectedParameter_mem_genuineCriticalStrip_zeta hs)]
  exact hrefZeta

end

end CPFormal.Analytic.Cp
