import CPFormal.Analytic.CpGenuineGprePrimeMomentCrosswalk
import CPFormal.Analytic.CpFiniteTfvdLogJetResidualCutoff

/-!
# Log-jet commutator readout of the prime Green bulk

The phase-normalized log-jet commutator wedge is already known blockwise to be
`-log(p)` times the oriented Green edge.  This module uses the existing
complete block trace, divides by the nonzero prime logarithm, and inserts the
critical carry amplitude `p^(-1/2)`.

The result is an exact finite readout of
`primeCarryGreenBulkCutoffProfile`, first from the canonical trace and then
directly from the enriched TFVD coordinates whose three provenance legs are
preserved until after the wedge is formed.
-/

open scoped BigOperators

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Normalize the existing complete log-jet commutator trace in `ℂ` before
reading its real Green bulk component.  The trace of `M` complete angular
blocks contains the first `3M` Green edges. -/
def finiteNativeGpreLogJetGreenBulkReadout
    (p : Nat.Primes) (M : ℕ) (s : ℂ) : ℝ :=
  ((-(((primeCarryAmplitudeRatio p : ℝ) : ℂ) /
      ((Real.log (p : ℝ) : ℝ) : ℂ))) *
    finiteCanonicalCpLogJetCommutatorWedgeTrace (p : ℕ) M s).re

/-- Before taking the real part, logarithmic normalization leaves the critical
carry amplitude multiplying the oriented Green flux. -/
theorem finiteNativeGpreLogJetGreenBulkReadout_complex_eq
    (p : Nat.Primes) (M : ℕ) (s : ℂ) :
    (-(((primeCarryAmplitudeRatio p : ℝ) : ℂ) /
        ((Real.log (p : ℝ) : ℝ) : ℂ))) *
        finiteCanonicalCpLogJetCommutatorWedgeTrace (p : ℕ) M s =
      ((primeCarryAmplitudeRatio p : ℝ) : ℂ) *
        finiteOrientedCpGreenFlux (p : ℕ) (3 * M) s := by
  have hpgt : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast p.prop.one_lt
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos hpgt)
  have hlogC : ((Real.log (p : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hlog
  rw [finiteCanonicalCpLogJetCommutatorWedgeTrace_eq_neg_log_mul_green
    (p : ℕ) p.prop M s]
  field_simp [hlogC]
  ring

/-- Exact finite crosswalk from the normalized log-jet wedge trace to the
centered prime Green bulk. -/
theorem finiteNativeGpreLogJetGreenBulkReadout_eq
    (p : Nat.Primes) (M : ℕ) (s : ℂ) :
    finiteNativeGpreLogJetGreenBulkReadout p M s =
      primeCarryGreenBulkCutoffProfile (3 * M) s p := by
  unfold finiteNativeGpreLogJetGreenBulkReadout
  rw [finiteNativeGpreLogJetGreenBulkReadout_complex_eq]
  rw [finiteOrientedCpGreenFlux_eq_radialDifference_mul_pairing
    (p : ℕ) (3 * M) p.prop s]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [primeCarryGreenBulkCutoffProfile_eq]
  unfold primeCarryGreenRadialProfile
  ring

/-- Trace formed directly from the enriched TFVD commutator coordinates, with
the two visible legs and the dormant third leg retained block by block. -/
def finiteEnrichedTfvdCpLogJetCommutatorWedgeTrace
    (p M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.range M,
    TfvdWedgeTriple.total
      (canonicalEnrichedTfvdCpLogJetCommutatorWedgeTriple
        p kappa omega m s)

/-- Decoding the enriched coordinates reproduces the existing canonical
complete-block commutator trace. -/
theorem finiteEnrichedTfvdCpLogJetCommutatorWedgeTrace_eq_canonical
    (p M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    finiteEnrichedTfvdCpLogJetCommutatorWedgeTrace
        p M kappa omega s =
      finiteCanonicalCpLogJetCommutatorWedgeTrace p M s := by
  unfold finiteEnrichedTfvdCpLogJetCommutatorWedgeTrace
    finiteCanonicalCpLogJetCommutatorWedgeTrace
  apply Finset.sum_congr rfl
  intro m hm
  rw [canonicalEnrichedTfvdCpLogJetCommutatorWedgeTriple_eq_canonical
    p hkappa omega m (homega m) s]

/-- The normalized readout formed directly from enriched TFVD–`G_pre` data. -/
def finiteEnrichedNativeGpreLogJetGreenBulkReadout
    (p : Nat.Primes) (M : ℕ)
    (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) : ℝ :=
  ((-(((primeCarryAmplitudeRatio p : ℝ) : ℂ) /
      ((Real.log (p : ℝ) : ℝ) : ℂ))) *
    finiteEnrichedTfvdCpLogJetCommutatorWedgeTrace
      (p : ℕ) M kappa omega s).re

/-- Final enriched finite crosswalk: the provenance-preserving log-jet
commutator readout is exactly the centered Green bulk at cutoff `3M`. -/
theorem finiteEnrichedNativeGpreLogJetGreenBulkReadout_eq
    (p : Nat.Primes) (M : ℕ)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    finiteEnrichedNativeGpreLogJetGreenBulkReadout
        p M kappa omega s =
      primeCarryGreenBulkCutoffProfile (3 * M) s p := by
  unfold finiteEnrichedNativeGpreLogJetGreenBulkReadout
  rw [finiteEnrichedTfvdCpLogJetCommutatorWedgeTrace_eq_canonical
    (p : ℕ) M hkappa omega homega s]
  exact finiteNativeGpreLogJetGreenBulkReadout_eq p M s

end

end CPFormal.Analytic.Cp
