import CPFormal.Analytic.CpNativeCarrySelfAdjointBoundaryPencil
import CPFormal.Analytic.CpGenuineBoundaryPencil
import CPFormal.Analytic.CpCarryWeightedVerticalBoundaryPencil

/-!
# Native carry complex time as slope of a self-adjoint boundary relation

A symmetric linear relation `R ⊆ B × B` satisfies the Green identity on its own
directions.  If it contains a nonzero direction `(u, z u)`, applying that
identity to the same direction forces `z = conj z`, hence `Im z = 0`.
Self-adjointness adds maximality, but symmetry already contains the exact
reality mechanism.

The free vertical TFVD relation is the whole boundary plane and is not even
symmetric.  The required spectral relation must therefore arise only after a
genuine restriction/gluing of the free carry boundary by bracket and
provenance.
-/

open scoped ComplexConjugate

namespace CPFormal.Analytic.Cp

noncomputable section

/-- A characteristic slope is a nonzero direction `(u, z u)` in a boundary
relation. -/
def NativeBoundaryRelationHasCharacteristicSlope
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    (R : Submodule ℂ (B × B)) (z : ℂ) : Prop :=
  ∃ u : B, u ≠ 0 ∧ (u, z • u) ∈ R

/-- Symmetry means that every relation direction belongs to the symplectic
adjoint relation. -/
def NativeBoundaryRelationIsSymmetric
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    (R : Submodule ℂ (B × B)) : Prop :=
  R ≤ R.adjoint

/-- Self-adjointness is equality with the symplectic adjoint. -/
def NativeBoundaryRelationIsSelfAdjoint
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    (R : Submodule ℂ (B × B)) : Prop :=
  R.adjoint = R

/-- A self-adjoint relation is symmetric. -/
theorem nativeBoundaryRelation_isSymmetric_of_isSelfAdjoint
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    {R : Submodule ℂ (B × B)}
    (hR : NativeBoundaryRelationIsSelfAdjoint R) :
    NativeBoundaryRelationIsSymmetric R := by
  intro x hx
  rw [hR]
  exact hx

/-- Every characteristic slope of a symmetric boundary relation is real. -/
theorem nativeBoundaryCharacteristicSlope_im_eq_zero_of_symmetric
    {B : Type*}
    [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    {R : Submodule ℂ (B × B)}
    (hR : NativeBoundaryRelationIsSymmetric R)
    {z : ℂ} (hz : NativeBoundaryRelationHasCharacteristicSlope R z) :
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

/-- Self-adjointness supplies the preceding symmetry gate. -/
theorem nativeBoundaryCharacteristicSlope_im_eq_zero_of_selfAdjoint
    {B : Type*}
    [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    {R : Submodule ℂ (B × B)}
    (hR : NativeBoundaryRelationIsSelfAdjoint R)
    {z : ℂ} (hz : NativeBoundaryRelationHasCharacteristicSlope R z) :
    z.im = 0 :=
  nativeBoundaryCharacteristicSlope_im_eq_zero_of_symmetric
    (nativeBoundaryRelation_isSymmetric_of_isSelfAdjoint hR) hz

/-- The whole scalar boundary plane is not symmetric. -/
theorem complex_top_not_nativeBoundaryRelationIsSymmetric :
    ¬ NativeBoundaryRelationIsSymmetric
      (⊤ : Submodule ℂ (ℂ × ℂ)) := by
  intro htop
  have hadj : ((1 : ℂ), 0) ∈
      (⊤ : Submodule ℂ (ℂ × ℂ)).adjoint :=
    htop (by simp)
  have hgreen :=
    (Submodule.mem_adjoint_iff
      (⊤ : Submodule ℂ (ℂ × ℂ)) ((1 : ℂ), 0)).1
      hadj 0 1 (by simp)
  norm_num at hgreen

/-- Hence the whole boundary plane is not self-adjoint. -/
theorem complex_top_not_nativeBoundaryRelationIsSelfAdjoint :
    ¬ NativeBoundaryRelationIsSelfAdjoint
      (⊤ : Submodule ℂ (ℂ × ℂ)) := by
  intro htop
  exact complex_top_not_nativeBoundaryRelationIsSymmetric
    (nativeBoundaryRelation_isSymmetric_of_isSelfAdjoint htop)

namespace LinearBoundaryPencil

variable {X B : Type*}
  [AddCommGroup X] [Module ℂ X]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B]

/-- A relation slope of a symmetric value--flux pencil is real. -/
theorem relationHasSlope_im_eq_zero_of_nativeRelationSymmetric
    (P : LinearBoundaryPencil X B)
    (hP : NativeBoundaryRelationIsSymmetric P.relation)
    {z : ℂ} (hz : P.RelationHasSlope z) :
    z.im = 0 := by
  apply nativeBoundaryCharacteristicSlope_im_eq_zero_of_symmetric hP
  exact hz

/-- The self-adjoint version of the same result. -/
theorem relationHasSlope_im_eq_zero_of_nativeRelationSelfAdjoint
    (P : LinearBoundaryPencil X B)
    (hP : NativeBoundaryRelationIsSelfAdjoint P.relation)
    {z : ℂ} (hz : P.RelationHasSlope z) :
    z.im = 0 :=
  P.relationHasSlope_im_eq_zero_of_nativeRelationSymmetric
    (nativeBoundaryRelation_isSymmetric_of_isSelfAdjoint hP) hz

end LinearBoundaryPencil

/-- The free carry boundary relation is not symmetric: it is the whole boundary
plane and permits every complex slope. -/
theorem carryWeightedVerticalBoundaryRelation_not_symmetric
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    ¬ NativeBoundaryRelationIsSymmetric
      (carryWeightedVerticalBoundaryPencil q).relation := by
  rw [carryWeightedVerticalBoundaryRelation_eq_top q hqpos hq1]
  exact complex_top_not_nativeBoundaryRelationIsSymmetric

/-- Consequently the free relation is not self-adjoint either. -/
theorem carryWeightedVerticalBoundaryRelation_not_selfAdjoint
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    ¬ NativeBoundaryRelationIsSelfAdjoint
      (carryWeightedVerticalBoundaryPencil q).relation := by
  intro hself
  exact carryWeightedVerticalBoundaryRelation_not_symmetric q hqpos hq1
    (nativeBoundaryRelation_isSymmetric_of_isSelfAdjoint hself)

/-- Minimal symmetric boundary-relation realization target. -/
structure NativeCarrySymmetricBoundaryRelationRealization
    (X B : Type*)
    [AddCommGroup X] [Module ℂ X]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] where
  pencil : LinearBoundaryPencil X B
  relation_isSymmetric : NativeBoundaryRelationIsSymmetric pencil.relation
  resonance_iff_relationHasSlope :
    ∀ {z : ℂ}, carryComplexTimeParameter z ∈ genuineCriticalStrip →
      (IsNativeCarryComplexTimeResonance z ↔ pencil.RelationHasSlope z)

namespace NativeCarrySymmetricBoundaryRelationRealization

variable {X B : Type*}
  [AddCommGroup X] [Module ℂ X]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B]

/-- Symmetry forces complex-time zero rigidity. -/
theorem complexTimeZeroRigidity
    (R : NativeCarrySymmetricBoundaryRelationRealization X B) :
    NativeCarryComplexTimeZeroRigidity := by
  intro z hz hres
  apply R.pencil.relationHasSlope_im_eq_zero_of_nativeRelationSymmetric
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

/-- Maximal self-adjoint boundary-relation realization target. -/
structure NativeCarrySelfAdjointBoundaryRelationRealization
    (X B : Type*)
    [AddCommGroup X] [Module ℂ X]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] where
  pencil : LinearBoundaryPencil X B
  relation_isSelfAdjoint : NativeBoundaryRelationIsSelfAdjoint pencil.relation
  resonance_iff_relationHasSlope :
    ∀ {z : ℂ}, carryComplexTimeParameter z ∈ genuineCriticalStrip →
      (IsNativeCarryComplexTimeResonance z ↔ pencil.RelationHasSlope z)

namespace NativeCarrySelfAdjointBoundaryRelationRealization

variable {X B : Type*}
  [AddCommGroup X] [Module ℂ X]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B]

/-- Forgetting maximality yields the symmetric realization. -/
def toSymmetric
    (R : NativeCarrySelfAdjointBoundaryRelationRealization X B) :
    NativeCarrySymmetricBoundaryRelationRealization X B where
  pencil := R.pencil
  relation_isSymmetric :=
    nativeBoundaryRelation_isSymmetric_of_isSelfAdjoint
      R.relation_isSelfAdjoint
  resonance_iff_relationHasSlope := R.resonance_iff_relationHasSlope

/-- Self-adjointness forces complex-time zero rigidity. -/
theorem complexTimeZeroRigidity
    (R : NativeCarrySelfAdjointBoundaryRelationRealization X B) :
    NativeCarryComplexTimeZeroRigidity :=
  R.toSymmetric.complexTimeZeroRigidity

/-- Self-adjointness forces preservation of critical amplitude. -/
theorem zeroPreservesCriticalAmplitude
    (R : NativeCarrySelfAdjointBoundaryRelationRealization X B) :
    NativeCarryComplexTimeZeroPreservesCriticalAmplitude :=
  R.toSymmetric.zeroPreservesCriticalAmplitude

/-- The real native spectrum exhausts the continuation. -/
theorem spectrumExhaustsGenuine
    (R : NativeCarrySelfAdjointBoundaryRelationRealization X B) :
    NativeCarrySpectrumExhaustsGenuine :=
  R.toSymmetric.spectrumExhaustsGenuine

/-- The self-adjoint realization closes strong nonvanishing. -/
theorem strongNonvanishing
    (R : NativeCarrySelfAdjointBoundaryRelationRealization X B) :
    GenuineStrongNonvanishingInStrip :=
  R.toSymmetric.strongNonvanishing

end NativeCarrySelfAdjointBoundaryRelationRealization

end

end CPFormal.Analytic.Cp
