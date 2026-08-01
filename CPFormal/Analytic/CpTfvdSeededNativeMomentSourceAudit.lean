import CPFormal.Analytic.CpTfvdSeededNativeMomentContraction
import CPFormal.Analytic.CpGenuineGprePrimeMomentCrosswalk

/-!
# Audit of the seeded TFVD native moment source gate

The exact finite TFVD--Bessel identities and the native `G_pre` contraction
reduce the proposed final bridge to one construction: a tower state whose
fixed-time moments recover every prime Green bulk.

This module records the logical strength of that construction.  At a nonempty
cutoff, existence of such a state is already equivalent to the critical
half-abscissa.  Consequently a constructor valid at every raw Genuine zero is
not a consequence of the abstract TFVD reconstruction alone; it has exactly
the strength of strong Genuine nonvanishing off the half-abscissa.

No axiom, `sorry`, `admit`, choice from the target conclusion, or renamed
confinement hypothesis is used.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Once critical displacement is known, the canonical fixed-time moment
source is the zero tower state. -/
def seededTfvdNativeMomentSourceOfCritical
    (_M : ℕ) (s : ℂ)
    (_hcritical : criticalDisplacement s.re = 0) :
    NativeGpreTowerHilbert :=
  0

/-- The critical zero source realizes every fixed-time native prime moment at
the cutoff aligned with the three-edge TFVD blocks. -/
theorem seededTfvdNativeMomentSourceOfCritical_realizes
    (M : ℕ) {s : ℂ}
    (hcritical : criticalDisplacement s.re = 0) :
    IsNativeGprePrimeMomentRealizationAt 1 (3 * M) s
      (seededTfvdNativeMomentSourceOfCritical M s hcritical) := by
  intro p
  rw [seededTfvdNativeMomentSourceOfCritical, inner_zero_right,
    primeCarryGreenBulkCutoffProfile_eq]
  simp [hcritical, primeCarryGreenRadialProfile, cpRadialDifference]

/-- At every nonempty seeded cutoff, existence of the proposed native moment
source is already equivalent to the critical half-abscissa. -/
theorem exists_seededTfvdNativeMomentSource_iff_re_eq_half
    (M : ℕ) (hM : 0 < M) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip) :
    (∃ x : NativeGpreTowerHilbert,
      IsNativeGprePrimeMomentRealizationAt 1 (3 * M) s x) ↔
      s.re = (1 : ℝ) / 2 := by
  rw [exists_isNativeGprePrimeMomentRealizationAt_iff
    1 (by norm_num) (3 * M) (by omega) hs]
  unfold criticalDisplacement
  constructor <;> intro h <;> linarith

/-- Exact global contract of the proposed `Collapse_Gpre` constructor. -/
def GenuineZerosAdmitSeededTfvdNativeMomentSources : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    genuineContinuation s = 0 →
    ∀ M : ℕ, 0 < M →
      ∃ x : NativeGpreTowerHilbert,
        IsNativeGprePrimeMomentRealizationAt 1 (3 * M) s x

/-- Constructing fixed-time native moment sources from every raw Genuine zero
has exactly the strength of strong off-critical nonvanishing. -/
theorem genuineZerosAdmitSeededTfvdNativeMomentSources_iff_strongNonvanishing :
    GenuineZerosAdmitSeededTfvdNativeMomentSources ↔
      GenuineStrongNonvanishingInStrip := by
  constructor
  · intro hsources s hs hoff hzero
    have hsource := hsources hs hzero 1 (by norm_num)
    have hhalf :=
      (exists_seededTfvdNativeMomentSource_iff_re_eq_half
        1 (by norm_num) hs).1 hsource
    exact hoff hhalf
  · intro hstrong s hs hzero M hM
    apply
      (exists_seededTfvdNativeMomentSource_iff_re_eq_half M hM hs).2
    by_contra hoff
    exact (hstrong hs hoff) hzero

end

end CPFormal.Analytic.Cp
