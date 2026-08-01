import CPFormal.Analytic.CpTfvdSeededFiniteBesselConservation
import CPFormal.Analytic.CpNativeGprePrimeCarryContraction

/-!
# Native G_pre moment contraction for the seeded TFVD Bessel ledger

The seeded TFVD reconstruction identifies the active finite-camera energy
exactly.  Independently, the native `G_pre` first-time tower lift turns one
source state into a common global centered-carry realization with the strict
contraction factor `11/12`.

This module composes those two already-proved layers.  It does not postulate a
source state from a Genuine zero.  Instead it records the exact payoff of the
remaining constructive step: once the reconstructed TFVD--`G_pre` data are
shown to provide the native prime moments, every finite atlas is bounded by the
same source norm and critical localization follows automatically.
-/

open scoped BigOperators Topology ENNReal

namespace CPFormal.Analytic.Cp

noncomputable section

/-- A native first-time moment realization bounds the exact seeded TFVD Bessel
energy on every finite prime atlas by the same strictly contracted source
energy. -/
theorem finiteSeededTfvdBesselEnergy_le_of_nativeMomentRealization
    (M : ℕ) (s : ℂ) (x : NativeGpreTowerHilbert)
    (hx : IsNativeGprePrimeMomentRealizationAt 1 (3 * M) s x)
    (S : Finset Nat.Primes) :
    finiteSeededTfvdBesselEnergy M s S ≤
      (11 / 12 : ℝ) * ‖x‖ ^ 2 := by
  calc
    finiteSeededTfvdBesselEnergy M s S =
        ‖canonicalEnrichedPrimeCarryDefectProvenanceState M s S‖ ^ 2 :=
      (canonicalEnrichedPrimeCarryDefectProvenanceState_norm_sq_eq_finiteSeededTfvdBesselEnergy
        M s S).symm
    _ ≤ (11 / 12 : ℝ) * ‖x‖ ^ 2 :=
      canonicalProvenanceState_norm_sq_le_of_nativeMomentRealization
        M s x hx S

/-- The same source gives the atlas-independent boundedness predicate used by
the exact TFVD--Bessel criticality theorem. -/
theorem seededTfvdFiniteBesselEnergiesBounded_of_nativeMomentRealization
    (M : ℕ) (s : ℂ) (x : NativeGpreTowerHilbert)
    (hx : IsNativeGprePrimeMomentRealizationAt 1 (3 * M) s x) :
    SeededTfvdFiniteBesselEnergiesBounded M s := by
  refine ⟨(11 / 12 : ℝ) * ‖x‖ ^ 2, ?_⟩
  intro S
  exact finiteSeededTfvdBesselEnergy_le_of_nativeMomentRealization
    M s x hx S

/-- Constructive endpoint of the composed route: a single native tower source
whose fixed-time moments are the reconstructed Green readouts forces zero
transverse carry displacement. -/
theorem criticalDisplacement_eq_zero_of_seededTfvd_nativeMomentRealization
    (M : ℕ) (hM : 0 < M) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (x : NativeGpreTowerHilbert)
    (hx : IsNativeGprePrimeMomentRealizationAt 1 (3 * M) s x) :
    criticalDisplacement s.re = 0 := by
  exact
    (seededTfvdFiniteBesselEnergiesBounded_iff_criticalDisplacement_eq_zero
      M hM hs).1
      (seededTfvdFiniteBesselEnergiesBounded_of_nativeMomentRealization
        M s x hx)

/-- The same endpoint in the original radial coordinate. -/
theorem re_eq_half_of_seededTfvd_nativeMomentRealization
    (M : ℕ) (hM : 0 < M) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (x : NativeGpreTowerHilbert)
    (hx : IsNativeGprePrimeMomentRealizationAt 1 (3 * M) s x) :
    s.re = (1 : ℝ) / 2 := by
  exact
    (seededTfvdFiniteBesselEnergiesBounded_iff_re_eq_half
      M hM hs).1
      (seededTfvdFiniteBesselEnergiesBounded_of_nativeMomentRealization
        M s x hx)

end

end CPFormal.Analytic.Cp
