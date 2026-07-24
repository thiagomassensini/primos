import CPFormal.Analytic.CpGenuineGprePrimeMomentCrosswalk
import CPFormal.Analytic.CpFiniteTfvdLogJetResidualCutoff

/-!
# Log-jet commutator readout of the prime Green bulk

The phase-normalized log-jet commutator wedge is already known blockwise to be
`-log(p)` times the oriented Green edge.  This module sums that identity,
divides by the nonzero prime logarithm, and inserts the critical carry
amplitude `p^(-1/2)`.

The result is an exact finite readout of
`primeCarryGreenBulkCutoffProfile`, first from the canonical edge trace and
then directly from the enriched TFVD coordinates whose three provenance legs
are preserved until after the wedge is formed.
-/

open scoped BigOperators

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Consecutive trace of the reflected, phase-normalized log-jet commutator
wedges. -/
def finiteCanonicalCpLogJetCommutatorWedgeTrace
    (p M : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range M,
    canonicalReflectedCpLogJetCommutatorWedge p n s

/-- Summing the local commutator identity gives `-log(p)` times the complete
oriented Green flux at the same cutoff. -/
theorem finiteCanonicalCpLogJetCommutatorWedgeTrace_eq_greenFlux
    (p M : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    finiteCanonicalCpLogJetCommutatorWedgeTrace p M s =
      -(Real.log (p : ℝ) : ℂ) * finiteOrientedCpGreenFlux p M s := by
  unfold finiteCanonicalCpLogJetCommutatorWedgeTrace
  simp_rw [canonicalReflectedCpLogJetCommutatorWedge_eq_neg_log_mul_green
    p hp]
  rw [← Finset.mul_sum,
    sum_range_canonicalOrientedCpGreenEdge_eq_finiteOrientedCpGreenFlux]

/-- Real part of the same exact trace identity. -/
theorem finiteCanonicalCpLogJetCommutatorWedgeTrace_re_eq
    (p M : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    (finiteCanonicalCpLogJetCommutatorWedgeTrace p M s).re =
      -Real.log (p : ℝ) * (finiteOrientedCpGreenFlux p M s).re := by
  rw [finiteCanonicalCpLogJetCommutatorWedgeTrace_eq_greenFlux p M hp s]
  simp [Complex.mul_re]

/-- Normalize the log-jet commutator trace by the native logarithmic generator
and dress it with the first-layer critical carry amplitude. -/
def finiteNativeGpreLogJetGreenBulkReadout
    (p : Nat.Primes) (M : ℕ) (s : ℂ) : ℝ :=
  -(primeCarryAmplitudeRatio p / Real.log (p : ℝ)) *
    (finiteCanonicalCpLogJetCommutatorWedgeTrace (p : ℕ) M s).re

/-- Exact finite crosswalk from the normalized log-jet wedge trace to the
centered prime Green bulk. -/
theorem finiteNativeGpreLogJetGreenBulkReadout_eq
    (p : Nat.Primes) (M : ℕ) (s : ℂ) :
    finiteNativeGpreLogJetGreenBulkReadout p M s =
      primeCarryGreenBulkCutoffProfile M s p := by
  have hpgt : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast p.prop.one_lt
  have hlogpos : 0 < Real.log (p : ℝ) := Real.log_pos hpgt
  have hlog : Real.log (p : ℝ) ≠ 0 := ne_of_gt hlogpos
  unfold finiteNativeGpreLogJetGreenBulkReadout
  rw [finiteCanonicalCpLogJetCommutatorWedgeTrace_re_eq
    (p : ℕ) M p.prop s]
  have hflux := congrArg Complex.re
    (finiteOrientedCpGreenFlux_eq_radialDifference_mul_pairing
      (p : ℕ) M p.prop s)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hflux
  rw [hflux, primeCarryGreenBulkCutoffProfile_eq]
  unfold primeCarryGreenRadialProfile
  field_simp [hlog]
  ring

/-- Trace formed directly from the enriched TFVD commutator coordinates, with
the two visible legs and the dormant third leg retained block by block. -/
def finiteEnrichedTfvdCpLogJetCommutatorWedgeTrace
    (p M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.range M,
    TfvdWedgeTriple.total
      (canonicalEnrichedTfvdCpLogJetCommutatorWedgeTriple
        p kappa omega m s)

/-- Decoding the enriched coordinates reproduces the consecutive canonical
commutator trace on the first `3M` edges. -/
theorem finiteEnrichedTfvdCpLogJetCommutatorWedgeTrace_eq_canonical
    (p M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    finiteEnrichedTfvdCpLogJetCommutatorWedgeTrace
        p M kappa omega s =
      finiteCanonicalCpLogJetCommutatorWedgeTrace p (3 * M) s := by
  unfold finiteEnrichedTfvdCpLogJetCommutatorWedgeTrace
  calc
    (∑ m ∈ Finset.range M,
        TfvdWedgeTriple.total
          (canonicalEnrichedTfvdCpLogJetCommutatorWedgeTriple
            p kappa omega m s)) =
      ∑ m ∈ Finset.range M,
        TfvdWedgeTriple.total
          (canonicalReflectedCpLogJetCommutatorWedgeTriple p m s) := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [canonicalEnrichedTfvdCpLogJetCommutatorWedgeTriple_eq_canonical
              p hkappa omega m (homega m) s]
    _ = ∑ n ∈ Finset.range (3 * M),
          canonicalReflectedCpLogJetCommutatorWedge p n s := by
            unfold TfvdWedgeTriple.total
              canonicalReflectedCpLogJetCommutatorWedgeTriple
            exact sum_range_threeBlocks_eq_range
              (fun n ↦ canonicalReflectedCpLogJetCommutatorWedge p n s) M
    _ = finiteCanonicalCpLogJetCommutatorWedgeTrace p (3 * M) s := rfl

/-- The normalized readout formed directly from enriched TFVD–`G_pre` data. -/
def finiteEnrichedNativeGpreLogJetGreenBulkReadout
    (p : Nat.Primes) (M : ℕ)
    (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) : ℝ :=
  -(primeCarryAmplitudeRatio p / Real.log (p : ℝ)) *
    (finiteEnrichedTfvdCpLogJetCommutatorWedgeTrace
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
  exact finiteNativeGpreLogJetGreenBulkReadout_eq p (3 * M) s

end

end CPFormal.Analytic.Cp
