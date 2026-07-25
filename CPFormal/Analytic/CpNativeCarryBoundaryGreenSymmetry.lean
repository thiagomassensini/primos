import CPFormal.Analytic.CpNativeCarrySelfAdjointBoundaryRelation

/-!
# Green symmetry identity for the native carry boundary pencil

The relation-level gate can be checked before computing any adjoint.  For a
value--flux pencil `P`, symmetry of its range is equivalent to the two-state
Green identity

`<Gamma_1 y, Gamma_0 x> = <Gamma_0 y, Gamma_1 x>`.

This module packages that identity as the concrete next proof obligation for a
pencil assembled from bracket, trace, and provenance.  Once the identity holds
and native resonances are its characteristic slopes, the complex-time
parameter is automatically real.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

namespace LinearBoundaryPencil

variable {X B : Type*}
  [AddCommGroup X] [Module ℂ X]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

/-- The exact Green symmetry identity for the value and flux traces. -/
def SatisfiesGreenSymmetry (P : LinearBoundaryPencil X B) : Prop :=
  ∀ x y : X,
    inner ℂ (P.fluxTrace y) (P.valueTrace x) =
      inner ℂ (P.valueTrace y) (P.fluxTrace x)

/-- The two-state Green identity makes the boundary range a symmetric linear
relation. -/
theorem relation_isSymmetric_of_satisfiesGreenSymmetry
    (P : LinearBoundaryPencil X B)
    (hP : P.SatisfiesGreenSymmetry) :
    P.relation.IsSymmetricRelation := by
  intro boundary hboundary
  change boundary ∈ LinearMap.range (P.valueTrace.prod P.fluxTrace) at hboundary
  rcases hboundary with ⟨x, rfl⟩
  rw [Submodule.mem_adjoint_iff]
  intro a b hab
  change (a, b) ∈ LinearMap.range (P.valueTrace.prod P.fluxTrace) at hab
  rcases hab with ⟨y, hy⟩
  have ha := congrArg Prod.fst hy
  have hb := congrArg Prod.snd hy
  change P.valueTrace y = a at ha
  change P.fluxTrace y = b at hb
  rw [← ha, ← hb]
  exact sub_eq_zero.mpr (hP x y)

/-- Conversely, symmetry of the range recovers the exact Green identity on the
underlying states. -/
theorem satisfiesGreenSymmetry_of_relation_isSymmetric
    (P : LinearBoundaryPencil X B)
    (hP : P.relation.IsSymmetricRelation) :
    P.SatisfiesGreenSymmetry := by
  intro x y
  have hxmem : (P.valueTrace x, P.fluxTrace x) ∈ P.relation := by
    exact ⟨x, rfl⟩
  have hxadj := hP hxmem
  have hyMem : (P.valueTrace y, P.fluxTrace y) ∈ P.relation := by
    exact ⟨y, rfl⟩
  have hgreen :=
    (Submodule.mem_adjoint_iff P.relation
      (P.valueTrace x, P.fluxTrace x)).1
      hxadj (P.valueTrace y) (P.fluxTrace y) hyMem
  exact sub_eq_zero.mp hgreen

/-- Green symmetry and symmetry of the boundary relation are the same
condition. -/
theorem satisfiesGreenSymmetry_iff_relation_isSymmetric
    (P : LinearBoundaryPencil X B) :
    P.SatisfiesGreenSymmetry ↔ P.relation.IsSymmetricRelation := by
  constructor
  · exact P.relation_isSymmetric_of_satisfiesGreenSymmetry
  · exact P.satisfiesGreenSymmetry_of_relation_isSymmetric

/-- A characteristic slope of a Green-symmetric pencil is real. -/
theorem relationHasSlope_im_eq_zero_of_satisfiesGreenSymmetry
    (P : LinearBoundaryPencil X B)
    (hP : P.SatisfiesGreenSymmetry)
    {z : ℂ} (hz : P.RelationHasSlope z) :
    z.im = 0 :=
  P.relationHasSlope_im_eq_zero_of_relation_isSymmetric
    (P.relation_isSymmetric_of_satisfiesGreenSymmetry hP) hz

end LinearBoundaryPencil

/-- Concrete Green-identity realization target.  This is weaker to construct
than a maximal self-adjoint relation but already sufficient for reality of the
native characteristic parameter. -/
structure NativeCarryGreenSymmetricBoundaryPencilRealization
    (X B : Type*)
    [AddCommGroup X] [Module ℂ X]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B] where
  pencil : LinearBoundaryPencil X B
  green_symmetry : pencil.SatisfiesGreenSymmetry
  resonance_iff_relationHasSlope :
    ∀ {z : ℂ}, carryComplexTimeParameter z ∈ genuineCriticalStrip →
      (IsNativeCarryComplexTimeResonance z ↔ pencil.RelationHasSlope z)

namespace NativeCarryGreenSymmetricBoundaryPencilRealization

variable {X B : Type*}
  [AddCommGroup X] [Module ℂ X]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

/-- The Green identity forces complex-time zero rigidity. -/
theorem complexTimeZeroRigidity
    (R : NativeCarryGreenSymmetricBoundaryPencilRealization X B) :
    NativeCarryComplexTimeZeroRigidity := by
  intro z hz hres
  apply R.pencil.relationHasSlope_im_eq_zero_of_satisfiesGreenSymmetry
    R.green_symmetry
  exact (R.resonance_iff_relationHasSlope hz).1 hres

/-- The Green-identity realization preserves the critical carry amplitude at
every zero. -/
theorem zeroPreservesCriticalAmplitude
    (R : NativeCarryGreenSymmetricBoundaryPencilRealization X B) :
    NativeCarryComplexTimeZeroPreservesCriticalAmplitude :=
  (nativeCarryComplexTimeZeroPreservesCriticalAmplitude_iff_zeroRigidity).2
    R.complexTimeZeroRigidity

/-- The Green-identity realization makes the real native spectrum exhaustive. -/
theorem spectrumExhaustsGenuine
    (R : NativeCarryGreenSymmetricBoundaryPencilRealization X B) :
    NativeCarrySpectrumExhaustsGenuine :=
  (nativeCarrySpectrumExhaustsGenuine_iff_complexTimeZeroRigidity).2
    R.complexTimeZeroRigidity

/-- The same realization closes strong off-critical nonvanishing. -/
theorem strongNonvanishing
    (R : NativeCarryGreenSymmetricBoundaryPencilRealization X B) :
    GenuineStrongNonvanishingInStrip :=
  (nativeCarryComplexTimeZeroRigidity_iff_strongNonvanishing).1
    R.complexTimeZeroRigidity

end NativeCarryGreenSymmetricBoundaryPencilRealization

end

end CPFormal.Analytic.Cp
