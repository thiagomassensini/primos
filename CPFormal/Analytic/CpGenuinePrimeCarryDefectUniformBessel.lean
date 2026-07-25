import CPFormal.Analytic.CpGenuinePrimeCarryDefectUniformBound
import CPFormal.Analytic.CpGenuineGprePrimeVerticalTraceDualTest

/-!
# Explicit unweighted Bessel bound from one global centered-carry state

The previous module proves that one global centered-carry realization controls
every finite provenance atlas.  Here the same statement is written directly in
the scalar-test language used by the final target.

If `x` realizes all enriched prime Green readouts, then for every finite prime
atlas `S` and every real coefficient family `c`,

`|sum_p c_p R_p|^2 <= ||x||^2 sum_p c_p^2`.

Thus the norm of the single global state is an explicit atlas-independent
Bessel constant.  No Genuine zero is used to manufacture `x`; the zero-to-state
construction remains the only missing implication.
-/

open scoped BigOperators ENNReal

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Explicit unweighted Bessel estimate produced by a single global
centered-carry realization. -/
theorem canonicalEnrichedGpreLogJetGreenScalarTest_sq_le_of_global_realization
    (M : ℕ) (s : ℂ)
    (x : PrimeCarryDefectGlobalHilbert)
    (hrealizes :
      IsCanonicalEnrichedPrimeCarryDefectReadoutRealization M s x)
    (S : Finset Nat.Primes) (coeff : Nat.Primes → ℝ) :
    (canonicalEnrichedGpreLogJetGreenScalarTest M s S coeff) ^ 2 ≤
      ‖x‖ ^ 2 * ∑ p ∈ S, (coeff p) ^ 2 := by
  let readout : Nat.Primes → ℝ := fun p =>
    finiteEnrichedNativeGpreLogJetGreenBulkReadout
      p M 1 (fun _ => 1) s
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq S coeff readout
  have hreadout :
      (∑ p ∈ S, (readout p) ^ 2) ≤ ‖x‖ ^ 2 := by
    calc
      (∑ p ∈ S, (readout p) ^ 2) =
          ∑ p ∈ S,
            (inner ℝ (primeCriticalCenteredCarryGlobalAxis p) x) ^ 2 := by
              apply Finset.sum_congr rfl
              intro p hp
              rw [hrealizes p]
      _ ≤ ‖x‖ ^ 2 :=
        sum_sq_inner_primeCriticalCenteredCarryGlobalAxis_le_norm_sq S x
  have hcoeff0 : 0 ≤ ∑ p ∈ S, (coeff p) ^ 2 :=
    Finset.sum_nonneg fun p hp => sq_nonneg _
  unfold canonicalEnrichedGpreLogJetGreenScalarTest
  change (∑ p ∈ S, coeff p * readout p) ^ 2 ≤ _
  calc
    (∑ p ∈ S, coeff p * readout p) ^ 2 ≤
        (∑ p ∈ S, coeff p ^ 2) *
          ∑ p ∈ S, readout p ^ 2 := hCS
    _ ≤ (∑ p ∈ S, coeff p ^ 2) * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hreadout hcoeff0
    _ = ‖x‖ ^ 2 * ∑ p ∈ S, coeff p ^ 2 := by ring

/-- Bundled scalar-test formulation with the explicit constant `||x||^2`. -/
theorem canonicalScalarTestsBounded_of_globalCarryDefectReadoutRealization
    (M : ℕ) (s : ℂ)
    {x : PrimeCarryDefectGlobalHilbert}
    (hrealizes :
      IsCanonicalEnrichedPrimeCarryDefectReadoutRealization M s x) :
    CanonicalEnrichedGpreLogJetGreenScalarTestsBounded M s := by
  refine ⟨‖x‖ ^ 2, sq_nonneg ‖x‖, ?_⟩
  intro S coeff
  exact
    canonicalEnrichedGpreLogJetGreenScalarTest_sq_le_of_global_realization
      M s x hrealizes S coeff

/-- Once a global centered-carry state has been constructed, its explicit
Bessel bound forces critical localization.  No zero hypothesis is needed at
this stage; the zero is needed only to construct the state. -/
theorem criticalDisplacement_eq_zero_of_globalCarryState
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (x : PrimeCarryDefectGlobalHilbert)
    (hrealizes :
      IsCanonicalEnrichedPrimeCarryDefectReadoutRealization 1 s x) :
    criticalDisplacement s.re = 0 := by
  have htests :=
    canonicalScalarTestsBounded_of_globalCarryDefectReadoutRealization
      1 s hrealizes
  exact
    (canonicalEnrichedGpreLogJetGreenScalarTestsBounded_iff
      1 (by norm_num) hs).1 htests

end

end CPFormal.Analytic.Cp
