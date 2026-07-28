import CPFormal.Analytic.CpGenuineCompatibility
import CPFormal.Analytic.CpNativeCarryRealOperatorConfinement
import CPFormal.Analytic.CpNativeCarryRealPlaneComplexPackaging

/-!
# Genuine zero to the primitive real boundary

This module connects the scalar Genuine chart to the primitive camera before
any quadratic-domain conclusion is used.

For `s = sigma + time * I`, the complex packaging of the real rotating sample
at `(sigma,time)` is exactly the Dirichlet monomial `n^(-s)`.  Additive
naturality then identifies every finite primitive resultant with the finite
Genuine chart.  Passing to the limit proves that every Genuine zero in the
open strip closes the raw primitive real boundary.

No Riemann zeta identification, Green relation, Cayley transform or mass
compatibility premise occurs in this crosswalk.
-/

open scoped BigOperators Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-- The parameter with real radial exponent `sigma` and real phase time
`time`. -/
def nativeCarryRealPlaneParameter (sigma time : ℝ) : ℂ :=
  ⟨sigma, time⟩

@[simp] theorem nativeCarryRealPlaneParameter_re (sigma time : ℝ) :
    (nativeCarryRealPlaneParameter sigma time).re = sigma := rfl

@[simp] theorem nativeCarryRealPlaneParameter_im (sigma time : ℝ) :
    (nativeCarryRealPlaneParameter sigma time).im = time := rfl

/-- Packaging the primitive real sample does not change the Dirichlet
monomial; it only stores its two real coordinates in `ℂ`. -/
theorem nativeCarryRealPlaneComplexPackaging_sampleAt_eq_dirichletTerm
    (sigma time : ℝ) {n : ℤ} (hn : 0 < n) :
    nativeCarryRealPlaneComplexPackaging
        (nativeCarryRealPlaneSampleAt sigma time n) =
      dirichletTerm (nativeCarryRealPlaneParameter sigma time) n := by
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hn)
  have hlog :
      Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) :=
    (Complex.ofReal_log hnR.le).symm
  rw [nativeCarryRealPlaneSampleAt_of_pos sigma time hn]
  unfold nativeCarryRealPlaneComplexPackaging dirichletTerm
    nativeCarryRealPlaneParameter
  rw [Complex.cpow_def_of_ne_zero hnC, hlog]
  apply Complex.ext
  · rw [Complex.exp_re]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.neg_re,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
    rw [← Real.rpow_def_of_pos hnR]
    congr 1
    ring
  · rw [Complex.exp_im]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.neg_re,
      Complex.ofReal_im, mul_zero, zero_mul, add_zero]
    rw [← Real.rpow_def_of_pos hnR]
    congr 1
    ring

/-- The packaged finite primitive resultant is the finite Dirichlet Genuine
chart at the same `(sigma,time)` parameter. -/
theorem nativeCarryRealPlaneComplexPackaging_finiteChartAt_eq_dirichlet
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (sigma time : ℝ) :
    nativeCarryRealPlaneComplexPackaging
        (nativeCarryRealPlaneFiniteChartAt p M sigma time) =
      CPFormal.Genuine.Cp.finiteChart p M
        (dirichletTerm (nativeCarryRealPlaneParameter sigma time)) := by
  calc
    nativeCarryRealPlaneComplexPackaging
          (nativeCarryRealPlaneFiniteChartAt p M sigma time) =
        CPFormal.Genuine.Cp.finiteChart p M
          (fun n =>
            nativeCarryRealPlaneComplexPackaging
              (nativeCarryRealPlaneSampleAt sigma time n)) :=
      nativeCarryRealPlaneComplexPackaging_eq_finiteChart
        p M hp hpodd sigma time
    _ = CPFormal.Genuine.Cp.finiteChart p M
          (dirichletTerm
            (nativeCarryRealPlaneParameter sigma time)) := by
      rw [
        CPFormal.Genuine.Cp.finiteChart_eq_positiveIntervalSum_sub_p_mul_centerSum
          p hp hpodd,
        CPFormal.Genuine.Cp.finiteChart_eq_positiveIntervalSum_sub_p_mul_centerSum
          p hp hpodd]
      have hprefix :
          (∑ n ∈ Finset.Icc (1 : ℤ)
              ((p : ℤ) * (M : ℤ) +
                (CPFormal.Genuine.Cp.halfRange p : ℤ)),
              nativeCarryRealPlaneComplexPackaging
                (nativeCarryRealPlaneSampleAt sigma time n)) =
            ∑ n ∈ Finset.Icc (1 : ℤ)
              ((p : ℤ) * (M : ℤ) +
                (CPFormal.Genuine.Cp.halfRange p : ℤ)),
              dirichletTerm
                (nativeCarryRealPlaneParameter sigma time) n := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnpos : 0 < n := by
          have hnleft := (Finset.mem_Icc.mp hn).1
          omega
        exact
          nativeCarryRealPlaneComplexPackaging_sampleAt_eq_dirichletTerm
            sigma time hnpos
      have hcenters :
          (∑ k ∈ Finset.range M,
              nativeCarryRealPlaneComplexPackaging
                (nativeCarryRealPlaneSampleAt sigma time
                  (CPFormal.Genuine.Cp.alignedCenter p k))) =
            ∑ k ∈ Finset.range M,
              dirichletTerm
                (nativeCarryRealPlaneParameter sigma time)
                (CPFormal.Genuine.Cp.alignedCenter p k) := by
        apply Finset.sum_congr rfl
        intro k _hk
        apply
          nativeCarryRealPlaneComplexPackaging_sampleAt_eq_dirichletTerm
        unfold CPFormal.Genuine.Cp.alignedCenter
        have hpZ : (0 : ℤ) < (p : ℤ) := by
          exact_mod_cast hp.pos
        have hkZ : (0 : ℤ) < ((k + 1 : ℕ) : ℤ) := by
          exact_mod_cast Nat.succ_pos k
        exact mul_pos hpZ hkZ
      rw [hprefix, hcenters]

/-- A Genuine zero closes the raw primitive real camera at the same radial
and phase coordinates. -/
theorem genuineContinuation_zero_to_nativeCarryRealBoundaryClosure
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    NativeCarryRealOperatorBoundaryClosesAt 3 s.re s.im := by
  have hhalf : -1 < s.re := by
    linarith [hs.1]
  have hcomplex :
      Tendsto
        (fun M : ℕ =>
          CPFormal.Genuine.Cp.finiteChart 3 M (dirichletTerm s))
        atTop (nhds 0) := by
    have hlimit :=
      finiteChart_dirichlet_tendsto_bracketedDirichletChart
        3 (by norm_num) (by norm_num) hhalf
    have hchart :
        bracketedDirichletChart 3 s = 0 :=
      (bracketedDirichletChart_zero_iff_genuineContinuation_zero
        3 (by norm_num) (by norm_num) hs).2 hzero
    simpa [hchart] using hlimit
  have hpackaged :
      Tendsto
        (fun M : ℕ =>
          nativeCarryRealPlaneComplexPackaging
            (nativeCarryRealPlaneFiniteChartAt 3 M s.re s.im))
        atTop (nhds 0) := by
    have hfinite :
        (fun M : ℕ =>
          nativeCarryRealPlaneComplexPackaging
            (nativeCarryRealPlaneFiniteChartAt 3 M s.re s.im)) =
          (fun M : ℕ =>
            CPFormal.Genuine.Cp.finiteChart 3 M (dirichletTerm s)) := by
      funext M
      simpa [nativeCarryRealPlaneParameter] using
        (nativeCarryRealPlaneComplexPackaging_finiteChartAt_eq_dirichlet
          3 M (by norm_num) (by norm_num) s.re s.im)
    rw [hfinite]
    exact hcomplex
  have hre :
      Tendsto
        (fun M : ℕ =>
          (nativeCarryRealPlaneFiniteChartAt 3 M s.re s.im).1)
        atTop (nhds 0) := by
    simpa using
      Complex.continuous_re.continuousAt.tendsto.comp hpackaged
  have him :
      Tendsto
        (fun M : ℕ =>
          (nativeCarryRealPlaneFiniteChartAt 3 M s.re s.im).2)
        atTop (nhds 0) := by
    simpa using
      Complex.continuous_im.continuousAt.tendsto.comp hpackaged
  unfold NativeCarryRealOperatorBoundaryClosesAt
  exact hre.prodMk_nhds him

end

end CPFormal.Analytic.Cp
