import CPFormal.Analytic.CpNativeCarrySelfAdjointBoundaryPencil
import CPFormal.Analytic.CpGenuineBoundaryPencil
import CPFormal.Analytic.CpCarryWeightedVerticalBoundaryPencil

/-!
# Native carry complex time as slope of a self-adjoint boundary relation

This module states the target directly at the boundary-relation level.  A
symmetric linear relation `R ⊆ B × B` satisfies the Green identity on its own
directions.  If it contains a nonzero direction `(u, z u)`, applying that
identity to the same direction forces `z = conj z`, hence `Im z = 0`.
Self-adjointness adds the maximality condition `R† = R`, but symmetry already
contains the exact reality mechanism.

Thus the native construction target is a fixed boundary pencil whose
value--flux relation is symmetric (ultimately self-adjoint) and whose slopes are
precisely the native carry complex-time resonances.  In this formulation `z`,
not the scalar readout `G(z)`, is the characteristic parameter.

The final block also records a scope guard: the free vertical TFVD relation is
the whole boundary plane and is not even symmetric.  The required relation must
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

/-- A boundary relation is symmetric when every one of its directions belongs
to its symplectic adjoint. -/
def IsSymmetricRelation (R : Submodule ℂ (B × B)) : Prop :=
  R ≤ R.adjoint

/-- A boundary relation is self-adjoint when it equals its symplectic adjoint. -/
def IsSelfAdjointRelation (R : Submodule ℂ (B × B)) : Prop :=
  R.adjoint = R

/-- A self-adjoint relation is symmetric. -/
theorem IsSelfAdjointRelation.isSymmetric
    {R : Submodule ℂ (B × B)}
    (hR : R.IsSelfAdjointRelation) :
    R.IsSymmetricRelation := by
  intro x hx
  rw [hR]
  exact hx

/-- Every characteristic slope of a symmetric boundary relation is real.  This
is the boundary Green identity with the characteristic direction paired
against itself. -/
theorem characteristicSlope_im_eq_zero_of_isSymmetricRelation
    {R : Submodule ℂ (B × B)}
    (hR : R.IsSymmetricRelation)
    {z : ℂ} (hz : R.HasCharacteristicSlope z) :
    z.im = 0 := by
  rcases hz with ⟨u, hu, hmem⟩
  have hadj : (u, z • u) ∈ R.adjoint := hR hmem
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

/-- Self-adjointness supplies the preceding symmetry gate automatically. -/
theorem characteristicSlope_im_eq_zero_of_isSelfAdjointRelation
    {R : Submodule ℂ (B × B)}
    (hR : R.IsSelfAdjointRelation)
    {z : ℂ} (hz : R.HasCharacteristicSlope z) :
    z.im = 0 :=
  characteristicSlope_im_eq_zero_of_isSymmetricRelation hR.isSymmetric hz

/-- The full scalar boundary plane is not a symmetric relation.  Its symplectic
adjoint cannot contain even the direction `(1,0)` while the full plane itself
does. -/
theorem complex_top_not_isSymmetricRelation :
    ¬ IsSymmetricRelation (⊤ : Submodule ℂ (ℂ × ℂ)) := by
  intro htop
  have hadj : ((1 : ℂ), 0) ∈ (⊤ : Submodule ℂ (ℂ × ℂ)).adjoint :=
    htop (by simp)
  have hgreen :=
    (Submodule.mem_adjoint_iff (⊤ : Submodule ℂ (ℂ × ℂ)) ((1 : ℂ), 0)).1
      hadj 0 1 (by simp)
  norm_num at hgreen

/-- In particular, the full boundary plane is not self-adjoint. -/
theorem complex_top_not_isSelfAdjointRelation :
    ¬ IsSelfAdjointRelation (⊤ : Submodule ℂ (ℂ × ℂ)) := by
  intro htop
  exact complex_top_not_isSymmetricRelation htop.isSymmetric

end Submodule

namespace LinearBoundaryPencil

variable {X B : Type*}
  [AddCommGroup X] [Module ℂ X]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

/-- A slope of a symmetric value--flux relation must be real. -/
theorem relationHasSlope_im_eq_zero_of_relation_isSymmetric
    (P : LinearBoundaryPencil X B)
    (hP : P.relation.IsSymmetricRelation)
    {z : ℂ} (hz : P.RelationHasSlope z) :
    z.im = 0 := by
  apply Submodule.characteristicSlope_im_eq_zero_of_isSymmetricRelation hP
  exact hz

/-- The self-adjoint version of the same boundary-slope theorem. -/
theorem relationHasSlope_im_eq_zero_of_relation_isSelfAdjoint
    (P : LinearBoundaryPencil X B)
    (hP : P.relation.IsSelfAdjointRelation)
    {z : ℂ} (hz : P.RelationHasSlope z) :
    z.im = 0 :=
  P.relationHasSlope_im_eq_zero_of_relation_isSymmetric hP.isSymmetric hz

end LinearBoundaryPencil

/-- The free carry boundary relation cannot be the desired spectral relation:
it is the whole boundary plane, so every complex slope is allowed and the
relation is not even symmetric. -/
theorem carryWeightedVerticalBoundaryRelation_not_isSymmetric
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    ¬ (carryWeightedVerticalBoundaryPencil q).relation.IsSymmetricRelation := by
  rw [carryWeightedVerticalBoundaryRelation_eq_top q hqpos hq1]
  exact Submodule.complex_top_not_isSymmetricRelation

/-- Consequently the free carry boundary relation is not self-adjoint either. -/
theorem carryWeightedVerticalBoundaryRelation_not_isSelfAdjoint
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    ¬ (carryWeightedVerticalBoundaryPencil q).relation.IsSelfAdjointRelation := by
  intro hself
  exact carryWeightedVerticalBoundaryRelation_not_isSymmetric q hqpos hq1
    hself.isSymmetric

/-- Exact symmetric boundary-relation realization target for the native carry
spectrum.  Symmetry is the minimal Green-identity hypothesis needed to force
reality of characteristic slopes. -/
structure NativeCarrySymmetricBoundaryRelationRealization
    (X B : Type*)
    [AddCommGroup X] [Module ℂ X]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B] where
  pencil : LinearBoundaryPencil X B
  relation_isSymmetric : pencil.relation.IsSymmetricRelation
  resonance_iff_relationHasSlope :
    ∀ {z : ℂ}, carryComplexTimeParameter z ∈ genuineCriticalStrip →
      (IsNativeCarryComplexTimeResonance z ↔ pencil.RelationHasSlope z)

namespace NativeCarrySymmetricBoundaryRelationRealization

variable {X B : Type*}
  [AddCommGroup X] [Module ℂ X]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

/-- A symmetric native boundary relation already forces complex-time zero
rigidity. -/
theorem complexTimeZeroRigidity
    (R : NativeCarrySymmetricBoundaryRelationRealization X B) :
    NativeCarryComplexTimeZeroRigidity := by
  intro z hz hres
  apply R.pencil.relationHasSlope_im_eq_zero_of_relation_isSymmetric
    R.relation_isSymmetric
  exact (R.resonance_iff_relationHasSlope hz).1 hres

/-- Symmetry forces preservation of the critical carry amplitude. -/
theorem zeroPreservesCriticalAmplitude
    (R : NativeCarrySymmetricBoundaryRelationRealization X B) :
    NativeCarryComplexTimeZeroPreservesCriticalAmplitude :=
  (nativeCarryComplexTimeZeroPreservesCriticalAmplitude_iff_zeroRigidity).2
    R.complexTimeZeroRigidity

/-- Symmetry makes the real native spectrum exhaustive. -/
theorem spectrumExhaustsGenuine
    (R : NativeCarrySymmetricBoundaryRelationRealization X B) :
    NativeCarrySpectrumExhaustsGenuine :=
  (nativeCarrySpectrumExhaustsGenuine_iff_complexTimeZeroRigidity).2
    R.complexTimeZeroRigidity

/-- Symmetry closes the strong scalar theorem. -/
theorem strongNonvanishing
    (R : NativeCarrySymmetricBoundaryRelationRealization X B) :
    GenuineStrongNonvanishingInStrip :=
  (nativeCarryComplexTimeZeroRigidity_iff_strongNonvanishing).1
    R.complexTimeZeroRigidity

end NativeCarrySymmetricBoundaryRelationRealization

/-- Exact self-adjoint boundary-relation realization target for the native carry
spectrum.  The pencil is fixed and independent of `z`; a complex time is a
resonance iff it is the slope of the same maximal symmetric relation. -/
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

/-- Forgetting maximality gives the exact symmetric gate above. -/
def toSymmetric
    (R : NativeCarrySelfAdjointBoundaryRelationRealization X B) :
    NativeCarrySymmetricBoundaryRelationRealization X B where
  pencil := R.pencil
  relation_isSymmetric := R.relation_isSelfAdjoint.isSymmetric
  resonance_iff_relationHasSlope := R.resonance_iff_relationHasSlope

/-- A self-adjoint native boundary relation forces complex-time zero rigidity. -/
theorem complexTimeZeroRigidity
    (R : NativeCarrySelfAdjointBoundaryRelationRealization X B) :
    NativeCarryComplexTimeZeroRigidity :=
  R.toSymmetric.complexTimeZeroRigidity

/-- The relation-level construction forces preservation of the critical carry
amplitude at every scalar resonance. -/
theorem zeroPreservesCriticalAmplitude
    (R : NativeCarrySelfAdjointBoundaryRelationRealization X B) :
    NativeCarryComplexTimeZeroPreservesCriticalAmplitude :=
  R.toSymmetric.zeroPreservesCriticalAmplitude

/-- The real native spectrum exhausts the continued zero set. -/
theorem spectrumExhaustsGenuine
    (R : NativeCarrySelfAdjointBoundaryRelationRealization X B) :
    NativeCarrySpectrumExhaustsGenuine :=
  R.toSymmetric.spectrumExhaustsGenuine

/-- The boundary-relation construction closes the strong scalar theorem. -/
theorem strongNonvanishing
    (R : NativeCarrySelfAdjointBoundaryRelationRealization X B) :
    GenuineStrongNonvanishingInStrip :=
  R.toSymmetric.strongNonvanishing

end NativeCarrySelfAdjointBoundaryRelationRealization

end

end CPFormal.Analytic.Cp
