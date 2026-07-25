import CPFormal.Analytic.CpNativeCarrySelfAdjointBoundaryPencil
import CPFormal.Analytic.CpGenuineBoundaryPencil
import CPFormal.Analytic.CpCarryWeightedVerticalBoundaryPencil

/-!
# Native carry complex time as slope of a self-adjoint boundary relation

This module states the target directly at the boundary-relation level.  A
self-adjoint linear relation `R ⊆ B × B` satisfies the Green identity.  If it
contains a nonzero direction `(u, z u)`, applying that identity to the same
direction forces `z = conj z`, hence `Im z = 0`.

Thus the exact native construction target is a fixed boundary pencil whose
value--flux relation is self-adjoint and whose slopes are precisely the native
carry complex-time resonances.  In this formulation `z`, not the scalar readout
`G(z)`, is the characteristic parameter.

The final block also records a scope guard: the free vertical TFVD relation is
the whole boundary plane and is not self-adjoint.  The required relation must
therefore arise only after a genuine restriction/gluing of the free carry
boundary by the bracket and provenance channels.
-/

open scoped ComplexConjugate

namespace CPFormal.Analytic.Cp

noncomputable section

namespace Submodule

variable {B : Type*}
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

/-- A characteristic slope of a boundary relation is a nonzero direction
`(u, z u)` contained in the relation. -/
def HasCharacteristicSlope (R : Submodule ℂ (B × B)) (z : ℂ) : Prop :=
  ∃ u : B, u ≠ 0 ∧ (u, z • u) ∈ R

/-- A boundary relation is self-adjoint when it equals its symplectic adjoint. -/
def IsSelfAdjointRelation (R : Submodule ℂ (B × B)) : Prop :=
  R.adjoint = R

/-- Every characteristic slope of a self-adjoint boundary relation is real.
This is the boundary Green identity with the characteristic direction paired
against itself. -/
theorem characteristicSlope_im_eq_zero_of_isSelfAdjointRelation
    {R : Submodule ℂ (B × B)}
    (hR : R.IsSelfAdjointRelation)
    {z : ℂ} (hz : R.HasCharacteristicSlope z) :
    z.im = 0 := by
  rcases hz with ⟨u, hu, hmem⟩
  have hadj : (u, z • u) ∈ R.adjoint := by
    rw [hR]
    exact hmem
  have hgreen :=
    (Submodule.mem_adjoint_iff R (u, z • u)).1 hadj u (z • u) hmem
  have hsym :
      inner ℂ (z • u) u = inner ℂ u (z • u) :=
    sub_eq_zero.mp hgreen
  rw [inner_smul_left, inner_smul_right,
    inner_self_eq_norm_sq_to_K] at hsym
  have hnormPos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hnormNe : ((‖u‖ : ℂ) ^ 2) ≠ 0 := by
    exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt hnormPos))
  have hconj : (starRingEnd ℂ) z = z :=
    mul_right_cancel₀ hnormNe hsym
  have him := congrArg Complex.im hconj
  simp only [Complex.conj_im] at him
  linarith

/-- The full scalar boundary plane is not a self-adjoint relation.  Its
symplectic adjoint cannot contain even the direction `(1,0)` while the full
plane itself does. -/
theorem complex_top_not_isSelfAdjointRelation :
    ¬ IsSelfAdjointRelation (⊤ : Submodule ℂ (ℂ × ℂ)) := by
  intro htop
  have hadj : ((1 : ℂ), 0) ∈ (⊤ : Submodule ℂ (ℂ × ℂ)).adjoint := by
    rw [htop]
    simp
  have hgreen :=
    (Submodule.mem_adjoint_iff (⊤ : Submodule ℂ (ℂ × ℂ)) ((1 : ℂ), 0)).1
      hadj 0 1 (by simp)
  norm_num at hgreen

end Submodule

namespace LinearBoundaryPencil

variable {X B : Type*}
  [AddCommGroup X] [Module ℂ X]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

/-- A slope of a self-adjoint value--flux relation must be real. -/
theorem relationHasSlope_im_eq_zero_of_relation_isSelfAdjoint
    (P : LinearBoundaryPencil X B)
    (hP : P.relation.IsSelfAdjointRelation)
    {z : ℂ} (hz : P.RelationHasSlope z) :
    z.im = 0 := by
  apply Submodule.characteristicSlope_im_eq_zero_of_isSelfAdjointRelation hP
  exact hz

end LinearBoundaryPencil

/-- The free carry boundary relation cannot be the desired spectral relation:
it is the whole boundary plane, so every complex slope is allowed and the
relation is not self-adjoint. -/
theorem carryWeightedVerticalBoundaryRelation_not_isSelfAdjoint
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    ¬ (carryWeightedVerticalBoundaryPencil q).relation.IsSelfAdjointRelation := by
  rw [carryWeightedVerticalBoundaryRelation_eq_top q hqpos hq1]
  exact Submodule.complex_top_not_isSelfAdjointRelation

/-- Exact boundary-relation realization target for the native carry spectrum.
The pencil is fixed and independent of `z`; a complex time is a resonance iff
it is the slope of the same self-adjoint relation. -/
structure NativeCarrySelfAdjointBoundaryRelationRealization
    (X B : Type*)
    [AddCommGroup X] [Module ℂ X]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B] where
  pencil : LinearBoundaryPencil X B
  relation_isSelfAdjoint : pencil.relation.IsSelfAdjointRelation
  resonance_iff_relationHasSlope :
    ∀ {z : ℂ}, carryComplexTimeParameter z ∈ genuineCriticalStrip →
      (IsNativeCarryComplexTimeResonance z ↔ pencil.RelationHasSlope z)

namespace NativeCarrySelfAdjointBoundaryRelationRealization

variable {X B : Type*}
  [AddCommGroup X] [Module ℂ X]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

/-- A self-adjoint native boundary relation forces complex-time zero rigidity. -/
theorem complexTimeZeroRigidity
    (R : NativeCarrySelfAdjointBoundaryRelationRealization X B) :
    NativeCarryComplexTimeZeroRigidity := by
  intro z hz hres
  apply R.pencil.relationHasSlope_im_eq_zero_of_relation_isSelfAdjoint
    R.relation_isSelfAdjoint
  exact (R.resonance_iff_relationHasSlope hz).1 hres

/-- The relation-level construction forces preservation of the critical carry
amplitude at every scalar resonance. -/
theorem zeroPreservesCriticalAmplitude
    (R : NativeCarrySelfAdjointBoundaryRelationRealization X B) :
    NativeCarryComplexTimeZeroPreservesCriticalAmplitude :=
  (nativeCarryComplexTimeZeroPreservesCriticalAmplitude_iff_zeroRigidity).2
    R.complexTimeZeroRigidity

/-- The real native spectrum exhausts the continued zero set. -/
theorem spectrumExhaustsGenuine
    (R : NativeCarrySelfAdjointBoundaryRelationRealization X B) :
    NativeCarrySpectrumExhaustsGenuine :=
  (nativeCarrySpectrumExhaustsGenuine_iff_complexTimeZeroRigidity).2
    R.complexTimeZeroRigidity

/-- The boundary-relation construction closes the strong scalar theorem. -/
theorem strongNonvanishing
    (R : NativeCarrySelfAdjointBoundaryRelationRealization X B) :
    GenuineStrongNonvanishingInStrip :=
  (nativeCarryComplexTimeZeroRigidity_iff_strongNonvanishing).1
    R.complexTimeZeroRigidity

end NativeCarrySelfAdjointBoundaryRelationRealization

end

end CPFormal.Analytic.Cp
