import CPFormal.Analytic.CpNativeCarrySpectrumExhaustion
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Self-adjoint boundary-pencil gate for the native carry spectrum

The native carry construction fixes the amplitude before the complex-time
continuation is introduced.  The remaining scalar target says that a resonance
of the continued readout can occur only at real carry time.

This module records the operator-theoretic root of that statement.  A fixed
self-adjoint partially defined operator has only real characteristic values.
Consequently, if the native bracket/Genuine resonance condition is realized as
a nontrivial kernel of the fixed pencil

`A - z I`,

then complex-time zero rigidity, preservation of the critical carry amplitude,
spectral exhaustion, and strong off-critical nonvanishing all follow
immediately.

The relation is the graph of `A`; self-adjointness of the operator makes this a
self-adjoint linear relation.  No instance of the realization is declared here.
The remaining constructive target is to build `A` from the native
bracket--trace--provenance data, independently of the zero set, and prove the
resonance/characteristic-value equivalence.
-/

open scoped ComplexConjugate

namespace CPFormal.Analytic.Cp

noncomputable section

namespace LinearPMap

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The fixed spectral pencil `A - z I`, with `z` itself as the characteristic
parameter.  Its domain is the fixed domain of `A`. -/
def spectralPencilOperator (A : H →ₗ.[ℂ] H) (z : ℂ) :
    A.domain →ₗ[ℂ] H :=
  A.toFun - z • A.domain.subtype

@[simp] theorem spectralPencilOperator_apply
    (A : H →ₗ.[ℂ] H) (z : ℂ) (x : A.domain) :
    A.spectralPencilOperator z x = A x - z • (x : H) := by
  rfl

/-- `z` is a characteristic value when `A - z I` has one nontrivial kernel
vector.  Unlike the older scalar Genuine pencil, the parameter is `z`, not the
readout value. -/
def IsCharacteristicValue (A : H →ₗ.[ℂ] H) (z : ℂ) : Prop :=
  ∃ x : A.domain, (x : H) ≠ 0 ∧ A.spectralPencilOperator z x = 0

/-- Characteristic values are equivalently ordinary eigenpairs in the fixed
operator domain. -/
theorem isCharacteristicValue_iff_eigenpair
    (A : H →ₗ.[ℂ] H) (z : ℂ) :
    A.IsCharacteristicValue z ↔
      ∃ x : A.domain, (x : H) ≠ 0 ∧ A x = z • (x : H) := by
  constructor
  · rintro ⟨x, hx, hzero⟩
    refine ⟨x, hx, ?_⟩
    rw [spectralPencilOperator_apply] at hzero
    exact sub_eq_zero.mp hzero
  · rintro ⟨x, hx, heigen⟩
    refine ⟨x, hx, ?_⟩
    rw [spectralPencilOperator_apply, heigen, sub_self]

/-- The spectral boundary relation associated with a partially defined
operator is its graph in `H × H`. -/
def spectralRelation (A : H →ₗ.[ℂ] H) : Submodule ℂ (H × H) :=
  A.graph

/-- Self-adjointness of the operator is exactly self-adjointness of its graph
as a linear relation. -/
theorem spectralRelation_isSelfAdjoint
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
    (A.spectralRelation).adjoint = A.spectralRelation := by
  unfold spectralRelation
  calc
    A.graph.adjoint = A.adjoint.graph :=
      (LinearPMap.adjoint_graph_eq_graph_adjoint hA.dense_domain).symm
    _ = A.graph :=
      congrArg LinearPMap.graph (LinearPMap.isSelfAdjoint_def.mp hA)

/-- Every characteristic value of a self-adjoint partially defined operator is
real.  The proof uses only the defining Green/symmetry identity on one
characteristic vector. -/
theorem characteristicValue_im_eq_zero_of_isSelfAdjoint
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {z : ℂ} (hz : A.IsCharacteristicValue z) :
    z.im = 0 := by
  rcases (A.isCharacteristicValue_iff_eigenpair z).1 hz with ⟨x, hx, hAx⟩
  have hformal : A.IsFormalAdjoint A := by
    have h := LinearPMap.adjoint_isFormalAdjoint hA.dense_domain
    rw [LinearPMap.isSelfAdjoint_def.mp hA] at h
    exact h
  have hsym := hformal x x
  rw [hAx, inner_smul_left, inner_smul_right,
    inner_self_eq_norm_sq_to_K] at hsym
  have hnormPos : 0 < ‖(x : H)‖ := norm_pos_iff.mpr hx
  have hnormNe : ((‖(x : H)‖ : ℂ) ^ 2) ≠ 0 := by
    exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt hnormPos))
  have hconj : (starRingEnd ℂ) z = z :=
    mul_right_cancel₀ hnormNe hsym
  have him := congrArg Complex.im hconj
  simp only [map_neg, Complex.conj_im] at him
  linarith

end LinearPMap

/-- A genuine self-adjoint realization of the native carry boundary pencil.

The operator is fixed: it does not depend on `z`.  The last field states that
native complex-time resonances are exactly the characteristic parameters of
`operator - z I`.  This is the non-tautological construction target for the
bracket--trace--provenance program. -/
structure NativeCarrySelfAdjointBoundaryPencilRealization
    (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  operator : H →ₗ.[ℂ] H
  operator_isSelfAdjoint : IsSelfAdjoint operator
  resonance_iff_characteristic :
    ∀ {z : ℂ}, carryComplexTimeParameter z ∈ genuineCriticalStrip →
      (IsNativeCarryComplexTimeResonance z ↔
        operator.IsCharacteristicValue z)

namespace NativeCarrySelfAdjointBoundaryPencilRealization

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The boundary relation of a native realization. -/
def relation (R : NativeCarrySelfAdjointBoundaryPencilRealization H) :
    Submodule ℂ (H × H) :=
  R.operator.spectralRelation

/-- The realized boundary relation is self-adjoint. -/
theorem relation_isSelfAdjoint
    (R : NativeCarrySelfAdjointBoundaryPencilRealization H) :
    R.relation.adjoint = R.relation :=
  LinearPMap.spectralRelation_isSelfAdjoint R.operator_isSelfAdjoint

/-- A self-adjoint boundary realization forces every native resonance to have
real carry time. -/
theorem complexTimeZeroRigidity
    (R : NativeCarrySelfAdjointBoundaryPencilRealization H) :
    NativeCarryComplexTimeZeroRigidity := by
  intro z hz hres
  apply LinearPMap.characteristicValue_im_eq_zero_of_isSelfAdjoint
    R.operator_isSelfAdjoint
  exact (R.resonance_iff_characteristic hz).1 hres

/-- Operator-theoretic reality of the characteristic parameter is exactly
preservation of the critical mass-to-amplitude normalization. -/
theorem zeroPreservesCriticalAmplitude
    (R : NativeCarrySelfAdjointBoundaryPencilRealization H) :
    NativeCarryComplexTimeZeroPreservesCriticalAmplitude :=
  (nativeCarryComplexTimeZeroPreservesCriticalAmplitude_iff_zeroRigidity).2
    R.complexTimeZeroRigidity

/-- A self-adjoint native boundary realization proves that the real carry
spectrum exhausts the continued Genuine zero set. -/
theorem spectrumExhaustsGenuine
    (R : NativeCarrySelfAdjointBoundaryPencilRealization H) :
    NativeCarrySpectrumExhaustsGenuine :=
  (nativeCarrySpectrumExhaustsGenuine_iff_complexTimeZeroRigidity).2
    R.complexTimeZeroRigidity

/-- The same construction closes the strong scalar nonvanishing theorem in the
open strip, without invoking the later zeta identification. -/
theorem strongNonvanishing
    (R : NativeCarrySelfAdjointBoundaryPencilRealization H) :
    GenuineStrongNonvanishingInStrip :=
  (nativeCarryComplexTimeZeroRigidity_iff_strongNonvanishing).1
    R.complexTimeZeroRigidity

end NativeCarrySelfAdjointBoundaryPencilRealization

end

end CPFormal.Analytic.Cp
