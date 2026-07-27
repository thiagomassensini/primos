import CPFormal.Analytic.CpNativeCarryRealPrecompressionBoundaryWitness
import CPFormal.Analytic.CpNativeCarryRealPlaneComplexPackaging
import CPFormal.Analytic.CpNativeCarryLogWaveBoundaryEquivalence

/-!
# Genuine closure and native real-plane reconstruction

This module keeps the scalar Genuine operator isolated from the completed
Genuine--Green operator.

It first identifies the primitive real-plane sample at `(sigma, time)` with
the ordinary Dirichlet sample at `sigma + time * I`, after applying the
already audited coordinate packaging `R x R -> C`.  Consequently, closure of
the primitive real camera is exactly closure of the scalar Genuine bracket.

The final theorem then states the reconstruction route in its shortest
pointwise form: if a closing scalar camera lifts to the retained
pre-compression state, its real exponent is forced to be `1 / 2`.  No
completed operator is used.
-/

open scoped Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-- The real rotating sample is exactly the complex Dirichlet sample after
coordinate packaging.  Complex notation contributes no extra operation. -/
theorem nativeCarryRealPlaneComplexPackaging_sampleAt_eq_dirichletTerm
    (sigma time : ℝ) {n : ℤ} (hn : 0 < n) :
    nativeCarryRealPlaneComplexPackaging
        (nativeCarryRealPlaneSampleAt sigma time n) =
      dirichletTerm
        (((sigma : ℂ) + (time : ℂ) * Complex.I)) n := by
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hn)
  have hnCast : (n : ℂ) = ((n : ℝ) : ℂ) := by
    norm_cast
  rw [nativeCarryRealPlaneSampleAt_of_pos sigma time hn]
  unfold dirichletTerm
  rw [Complex.cpow_def_of_ne_zero hnC,
    hnCast,
    ← Complex.ofReal_log hnR.le]
  let z : ℂ :=
    (Real.log (n : ℝ) : ℂ) *
      (-((sigma : ℂ) + (time : ℂ) * Complex.I))
  change
    nativeCarryRealPlaneComplexPackaging
        (((n : ℝ) ^ (-sigma) * Real.cos (-time * Real.log (n : ℝ))),
          ((n : ℝ) ^ (-sigma) * Real.sin (-time * Real.log (n : ℝ)))) =
      Complex.exp z
  have hzre : z.re = -sigma * Real.log (n : ℝ) := by
    simp [z]
    ring
  have hzim : z.im = -time * Real.log (n : ℝ) := by
    simp [z]
    ring
  have hamp :
      (n : ℝ) ^ (-sigma) =
        Real.exp (-sigma * Real.log (n : ℝ)) := by
    rw [Real.rpow_def_of_pos hnR]
    congr 1
    ring
  apply Complex.ext
  · change
      (n : ℝ) ^ (-sigma) *
          Real.cos (-time * Real.log (n : ℝ)) =
        (Complex.exp z).re
    rw [Complex.exp_re, hzre, hzim, hamp]
  · change
      (n : ℝ) ^ (-sigma) *
          Real.sin (-time * Real.log (n : ℝ)) =
        (Complex.exp z).im
    rw [Complex.exp_im, hzre, hzim, hamp]

/-- A finite primitive real camera packages to the literal finite Dirichlet
camera at `sigma + time * I`. -/
theorem nativeCarryRealPlaneComplexPackaging_finiteChartAt_eq_dirichlet
    (M : ℕ) (sigma time : ℝ) :
    nativeCarryRealPlaneComplexPackaging
        (nativeCarryRealPlaneFiniteChartAt 3 M sigma time) =
      CPFormal.Genuine.Cp.finiteChart 3 M
        (dirichletTerm
          (((sigma : ℂ) + (time : ℂ) * Complex.I))) := by
  rw [nativeCarryRealPlaneComplexPackaging_eq_finiteChart
    3 M (by norm_num) (by norm_num) sigma time]
  rw [CPFormal.Genuine.Cp.finiteChart_eq_positiveIntervalSum_sub_p_mul_centerSum
      3 (by norm_num) (by norm_num),
    CPFormal.Genuine.Cp.finiteChart_eq_positiveIntervalSum_sub_p_mul_centerSum
      3 (by norm_num) (by norm_num)]
  congr 1
  · apply Finset.sum_congr rfl
    intro n hnmem
    exact nativeCarryRealPlaneComplexPackaging_sampleAt_eq_dirichletTerm
      sigma time (Finset.mem_Icc.mp hnmem).1
  · congr 1
    apply Finset.sum_congr rfl
    intro k hk
    apply nativeCarryRealPlaneComplexPackaging_sampleAt_eq_dirichletTerm
    unfold CPFormal.Genuine.Cp.alignedCenter
    positivity

/-- Packaging a real-plane sequence tends to zero exactly when the original
real-plane sequence tends to zero. -/
theorem tendsto_nativeCarryRealPlaneComplexPackaging_zero_iff
    (u : ℕ → NativeCarryRealPlane) :
    Tendsto
        (fun M => nativeCarryRealPlaneComplexPackaging (u M))
        atTop (nhds 0) ↔
      Tendsto u atTop (nhds 0) := by
  let unpack : ℂ → NativeCarryRealPlane := fun z => (z.re, z.im)
  have hpackEq :
      (fun v : NativeCarryRealPlane =>
        nativeCarryRealPlaneComplexPackaging v) =
      (fun v : NativeCarryRealPlane =>
        (v.1 : ℂ) + (v.2 : ℂ) * Complex.I) := by
    funext v
    apply Complex.ext <;>
      simp [nativeCarryRealPlaneComplexPackaging]
  have hpack :
      Continuous
        (fun v : NativeCarryRealPlane =>
          nativeCarryRealPlaneComplexPackaging v) := by
    rw [hpackEq]
    fun_prop
  have hunpack : Continuous unpack := by
    fun_prop
  constructor
  · intro h
    have h' := hunpack.continuousAt.tendsto.comp h
    change Tendsto u atTop (nhds ((0, 0) : NativeCarryRealPlane))
    simpa [Function.comp_def, unpack,
      nativeCarryRealPlaneComplexPackaging] using h'
  · intro h
    have h' := hpack.continuousAt.tendsto.comp h
    change
      Tendsto
        (fun M => nativeCarryRealPlaneComplexPackaging (u M))
        atTop (nhds ({ re := 0, im := 0 } : ℂ))
    simpa [Function.comp_def,
      nativeCarryRealPlaneComplexPackaging] using h'

/-- In the open critical strip, closure of the primitive real camera is
exactly zero of the isolated scalar Genuine operator. -/
theorem nativeCarryRealPlaneBoundaryClosesAt_iff_genuineContinuation_zero
    {sigma time : ℝ} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    NativeCarryRealPlaneBoundaryClosesAt sigma time ↔
      genuineContinuation
        (((sigma : ℂ) + (time : ℂ) * Complex.I)) = 0 := by
  let s : ℂ := (sigma : ℂ) + (time : ℂ) * Complex.I
  have hs : s ∈ genuineCriticalStrip := by
    constructor
    · simpa [s] using hsigma0
    · simpa [s] using hsigma1
  have hsMinusOne : -1 < s.re :=
    lt_trans (by norm_num) hs.1
  have hlimit :
      Tendsto
        (fun M : ℕ =>
          CPFormal.Genuine.Cp.finiteChart 3 M (dirichletTerm s))
        atTop (nhds (bracketedDirichletChart 3 s)) :=
    finiteChart_dirichlet_tendsto_bracketedDirichletChart
      3 (by norm_num) (by norm_num) hsMinusOne
  have hzero :
      bracketedDirichletChart 3 s = 0 ↔
        genuineContinuation s = 0 :=
    bracketedDirichletChart_zero_iff_genuineContinuation_zero
      3 (by norm_num) (by norm_num) hs
  constructor
  · intro hclose
    have hpackaged :
        Tendsto
          (fun M : ℕ =>
            nativeCarryRealPlaneComplexPackaging
              (nativeCarryRealPlaneFiniteChartAt 3 M sigma time))
          atTop (nhds 0) :=
      (tendsto_nativeCarryRealPlaneComplexPackaging_zero_iff
        (fun M : ℕ =>
          nativeCarryRealPlaneFiniteChartAt 3 M sigma time)).2 hclose
    have hdirichlet :
        Tendsto
          (fun M : ℕ =>
            CPFormal.Genuine.Cp.finiteChart 3 M (dirichletTerm s))
          atTop (nhds 0) := by
      simpa only [s,
        nativeCarryRealPlaneComplexPackaging_finiteChartAt_eq_dirichlet]
        using hpackaged
    exact hzero.1 (tendsto_nhds_unique hlimit hdirichlet)
  · intro hgenuine
    have hchart : bracketedDirichletChart 3 s = 0 :=
      hzero.2 (by simpa [s] using hgenuine)
    have hdirichlet :
        Tendsto
          (fun M : ℕ =>
            CPFormal.Genuine.Cp.finiteChart 3 M (dirichletTerm s))
          atTop (nhds 0) := by
      simpa [hchart] using hlimit
    have hpackaged :
        Tendsto
          (fun M : ℕ =>
            nativeCarryRealPlaneComplexPackaging
              (nativeCarryRealPlaneFiniteChartAt 3 M sigma time))
          atTop (nhds 0) := by
      simpa only [s,
        nativeCarryRealPlaneComplexPackaging_finiteChartAt_eq_dirichlet]
        using hdirichlet
    exact
      (tendsto_nativeCarryRealPlaneComplexPackaging_zero_iff
        (fun M : ℕ =>
          nativeCarryRealPlaneFiniteChartAt 3 M sigma time)).1 hpackaged

/-- Clean reconstruction theorem for the isolated Genuine operator: a scalar
zero cannot occur off the critical line when its native real camera closure
reconstructs the retained pre-compression state. -/
theorem genuineContinuation_ne_zero_off_critical_of_precompression_reconstruction
    {sigma time : ℝ}
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hoff : sigma ≠ (1 : ℝ) / 2)
    (hreconstruct :
      NativeCarryRealPlaneBoundaryClosesAt sigma time →
        NativeCarryRealPlaneBoundaryClosureHasPrecompressionLift sigma time) :
    genuineContinuation
        (((sigma : ℂ) + (time : ℂ) * Complex.I)) ≠ 0 := by
  intro hzero
  have hclose :
      NativeCarryRealPlaneBoundaryClosesAt sigma time :=
    (nativeCarryRealPlaneBoundaryClosesAt_iff_genuineContinuation_zero
      hsigma0 hsigma1).2 hzero
  have hmass : NativeCarryRealPlaneMassCompatible sigma time :=
    boundaryClosurePrecompressionLift_massCompatible
      (hreconstruct hclose)
  exact hoff
    ((nativeCarryRealPlaneMassCompatible_iff sigma time).1 hmass)

end

end CPFormal.Analytic.Cp
