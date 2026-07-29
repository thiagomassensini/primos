import CPFormal.Analytic.CpPrimitiveGenuineZetaZeroSet
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Promotion to Mathlib's Riemann-hypothesis proposition

This module compares the native real-plane zero-rigidity target with
Mathlib's official proposition `RiemannHypothesis`.

The first step is classical bookkeeping: a nontrivial Riemann-zeta zero lies
in the open critical strip.  The right half-plane follows from Mathlib's
nonvanishing theorem; the left half-plane follows from the functional equation
and the classification of the zeros of the complex cosine factor.

The second step reuses the already kernel-checked primitive/Genuine/zeta
zero-set identity.
-/

namespace CPFormal.Analytic.Cp

open Complex

noncomputable section

/-- Every zero quantified by Mathlib's `RiemannHypothesis` proposition lies
in the open critical strip. -/
theorem nontrivialRiemannZetaZero_mem_genuineCriticalStrip
    {s : ℂ}
    (hzero : riemannZeta s = 0)
    (htrivial : ¬ ∃ n : ℕ, s = -2 * (n + 1))
    (hone : s ≠ 1) :
    s ∈ genuineCriticalStrip := by
  constructor
  · by_contra hnot
    have hre : s.re ≤ 0 := le_of_not_gt hnot
    have hs_ne_zero : s ≠ 0 := by
      intro hs
      rw [hs, riemannZeta_zero] at hzero
      norm_num at hzero
    have hu_not_neg_nat : ∀ n : ℕ, 1 - s ≠ -n := by
      intro n hu
      have hure := congrArg Complex.re hu
      simp at hure
      linarith [Nat.cast_nonneg n]
    have hu_ne_one : 1 - s ≠ 1 := by
      intro hu
      apply hs_ne_zero
      linear_combination -hu
    have hfe := riemannZeta_one_sub
      (s := 1 - s) hu_not_neg_nat hu_ne_one
    have hfe' :
        riemannZeta s =
          2 * (2 * π) ^ (-(1 - s)) * Gamma (1 - s) *
            cos (π * (1 - s) / 2) * riemannZeta (1 - s) := by
      simpa using hfe
    have href_re : 1 ≤ (1 - s).re := by
      simp
      linarith
    have href_ne_zero : riemannZeta (1 - s) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re href_re
    have hgamma : Gamma (1 - s) ≠ 0 := by
      apply Complex.Gamma_ne_zero_of_re_pos
      simp
      linarith
    have hpi : (π : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    have hbase : (2 * π : ℂ) ≠ 0 :=
      mul_ne_zero (by norm_num) hpi
    have hpow : (2 * π : ℂ) ^ (-(1 - s)) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hbase)
    have hproduct :
        2 * (2 * π) ^ (-(1 - s)) * Gamma (1 - s) *
            cos (π * (1 - s) / 2) * riemannZeta (1 - s) = 0 :=
      hfe'.symm.trans hzero
    have hprefix :
        2 * (2 * π) ^ (-(1 - s)) * Gamma (1 - s) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hpow) hgamma
    have hcos_product :
        2 * (2 * π) ^ (-(1 - s)) * Gamma (1 - s) *
            cos (π * (1 - s) / 2) = 0 :=
      (mul_eq_zero.mp hproduct).resolve_right href_ne_zero
    have hcos : cos (π * (1 - s) / 2) = 0 :=
      (mul_eq_zero.mp hcos_product).resolve_left hprefix
    obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos
    have hk_scaled :
        (π : ℂ) * (1 - s) =
          (((2 * k + 1 : ℤ) : ℂ) * π) := by
      linear_combination 2 * hk
    have harg :
        1 - s = ((2 * k + 1 : ℤ) : ℂ) := by
      apply mul_left_cancel₀ hpi
      calc
        (π : ℂ) * (1 - s) =
            (((2 * k + 1 : ℤ) : ℂ) * π) := hk_scaled
        _ = (π : ℂ) * ((2 * k + 1 : ℤ) : ℂ) := by ring
    have hs_k : s = -2 * (k : ℂ) := by
      linear_combination -harg
    have hs_k_re := congrArg Complex.re hs_k
    simp at hs_k_re
    have hk_nonneg_real : 0 ≤ (k : ℝ) := by
      linarith
    have hk_nonneg : 0 ≤ k := by
      exact_mod_cast hk_nonneg_real
    have hk_ne_zero : k ≠ 0 := by
      intro hkzero
      apply hs_ne_zero
      rw [hs_k, hkzero]
      norm_num
    have hk_pos : 0 < k :=
      lt_of_le_of_ne hk_nonneg (Ne.symm hk_ne_zero)
    have hk_toNat_pos : 0 < k.toNat :=
      Int.toNat_pos.mpr hk_pos
    obtain ⟨n, hn⟩ :=
      Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk_toNat_pos)
    have hk_int : (k.toNat : ℤ) = k :=
      Int.toNat_of_nonneg hk_nonneg
    have hk_complex : (k.toNat : ℂ) = (k : ℂ) := by
      exact_mod_cast hk_int
    apply htrivial
    refine ⟨n, ?_⟩
    calc
      s = -2 * (k : ℂ) := hs_k
      _ = -2 * (k.toNat : ℂ) := by rw [hk_complex]
      _ = -2 * ((n + 1 : ℕ) : ℂ) := by rw [hn]
  · by_contra hnot
    have hre : 1 ≤ s.re := le_of_not_gt hnot
    exact (riemannZeta_ne_zero_of_one_le_re hre) hzero

/-- Mathlib's plane-wide formulation of RH is equivalent to confinement on
the open critical strip, since its hypotheses exclude exactly the trivial
zeros outside that strip. -/
theorem mathlibRiemannHypothesis_iff_openCriticalStripConfinement :
    RiemannHypothesis ↔
      RiemannZetaZeroConfinementOnOpenCriticalStrip := by
  constructor
  · intro hRH s hs hzero
    apply hRH s hzero
    · rintro ⟨n, hn⟩
      have hre := congrArg Complex.re hn
      simp at hre
      linarith [hs.1]
    · intro hsone
      have hre := congrArg Complex.re hsone
      norm_num at hre
      linarith [hs.2]
  · intro hstrip
    intro s hzero htrivial hone
    exact hstrip
      (nontrivialRiemannZetaZero_mem_genuineCriticalStrip
        hzero htrivial hone)
      hzero

/-- Exact comparison of the repository's raw native zero-rigidity target with
Mathlib's official Riemann-hypothesis proposition. -/
theorem nativeCarryRealPlaneZeroRigidity_iff_mathlibRiemannHypothesis :
    NativeCarryRealPlaneZeroRigidity ↔ RiemannHypothesis :=
  nativeCarryRealPlaneZeroRigidity_iff_riemannZeta.trans
    mathlibRiemannHypothesis_iff_openCriticalStripConfinement.symm

end

end CPFormal.Analytic.Cp
