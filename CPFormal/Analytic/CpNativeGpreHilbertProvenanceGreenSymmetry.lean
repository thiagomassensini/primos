import CPFormal.Analytic.CpNativeGpreFiniteProvenanceGreenSymmetry
import CPFormal.Analytic.CpNativeGpreTfvdAnalysis

/-!
# Green symmetry of G_pre provenance on the full vertical Hilbert space

The finite provenance atlas is not restricted to the finitely supported edge
core.  Its value and number-flux roles already extend continuously to the full
vertical carry Hilbert space `ell^2(N,C)`.

This module places those continuous coordinates in the canonical finite `L2`
atlas and proves the same exact Green symmetry there.  Thus provenance is not
the source of the boundary defect even after completion; the only remaining
finite-atlas defect is the vertical Wronskian.
-/

open scoped InnerProduct

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Continuous value provenance readout in the finite `L2` atlas. -/
noncomputable def nativeGpreHilbertBoundaryValueLift
    (S : Finset NativeGpreBoundaryContext) :
    CarryVerticalL2 →ₗ[ℂ] NativeGpreFiniteHilbertBoundaryCarrier S where
  toFun x := WithLp.toLp 2 fun c =>
    nativeGpreFiniteContinuousBoundaryValueLift S x c
  map_add' x y := by
    ext c
    simp
  map_smul' a x := by
    ext c
    simp

/-- Continuous number-flux provenance readout in the same finite `L2` atlas. -/
noncomputable def nativeGpreHilbertBoundaryNumberFluxLift
    (S : Finset NativeGpreBoundaryContext) :
    CarryVerticalL2 →ₗ[ℂ] NativeGpreFiniteHilbertBoundaryCarrier S where
  toFun x := WithLp.toLp 2 fun c =>
    nativeGpreFiniteContinuousBoundaryNumberFluxLift S x c
  map_add' x y := by
    ext c
    simp
  map_smul' a x := by
    ext c
    simp

@[simp] theorem nativeGpreHilbertBoundaryValueLift_apply
    (S : Finset NativeGpreBoundaryContext)
    (x : CarryVerticalL2) (c : ↥S) :
    nativeGpreHilbertBoundaryValueLift S x c =
      nativeGpreFiniteContinuousBoundaryValueLift S x c := rfl

@[simp] theorem nativeGpreHilbertBoundaryNumberFluxLift_apply
    (S : Finset NativeGpreBoundaryContext)
    (x : CarryVerticalL2) (c : ↥S) :
    nativeGpreHilbertBoundaryNumberFluxLift S x c =
      nativeGpreFiniteContinuousBoundaryNumberFluxLift S x c := rfl

/-- On the full Hilbert space the number flux is still the real tower level
multiplied by the value coordinate. -/
theorem nativeGpreHilbertBoundaryNumberFlux_eq_level_mul_value
    (S : Finset NativeGpreBoundaryContext)
    (x : CarryVerticalL2) (c : ↥S) :
    nativeGpreHilbertBoundaryNumberFluxLift S x c =
      (c.1.towerLevel.val : ℂ) * nativeGpreHilbertBoundaryValueLift S x c := by
  rw [nativeGpreHilbertBoundaryNumberFluxLift_apply,
    nativeGpreHilbertBoundaryValueLift_apply,
    nativeGpreFiniteContinuousBoundaryRoleLift_apply,
    nativeGpreFiniteContinuousBoundaryRoleLift_apply,
    nativeGpreBoundary_numberFluxCoefficient_eq_level_mul_value]
  push_cast
  ring

/-- Provenance-only pencil acting on the full vertical carry Hilbert space. -/
def nativeGpreHilbertProvenanceBoundaryPencil
    (S : Finset NativeGpreBoundaryContext) :
    LinearBoundaryPencil CarryVerticalL2
      (NativeGpreFiniteHilbertBoundaryCarrier S) where
  valueTrace := nativeGpreHilbertBoundaryValueLift S
  fluxTrace := nativeGpreHilbertBoundaryNumberFluxLift S

/-- The completed finite provenance atlas satisfies the exact Green identity. -/
theorem nativeGpreHilbertProvenanceBoundaryPencil_greenSymmetry
    (S : Finset NativeGpreBoundaryContext) :
    LinearBoundaryPencil.SatisfiesGreenSymmetry
      (nativeGpreHilbertProvenanceBoundaryPencil S) := by
  intro x y
  rw [PiLp.inner_apply, PiLp.inner_apply]
  change
    (∑ c : ↥S,
      inner ℂ
        (nativeGpreFiniteContinuousBoundaryNumberFluxLift S y c)
        (nativeGpreFiniteContinuousBoundaryValueLift S x c)) =
      ∑ c : ↥S,
        inner ℂ
          (nativeGpreFiniteContinuousBoundaryValueLift S y c)
          (nativeGpreFiniteContinuousBoundaryNumberFluxLift S x c)
  apply Finset.sum_congr rfl
  intro c hc
  change
    inner ℂ
        (nativeGpreHilbertBoundaryNumberFluxLift S y c)
        (nativeGpreHilbertBoundaryValueLift S x c) =
      inner ℂ
        (nativeGpreHilbertBoundaryValueLift S y c)
        (nativeGpreHilbertBoundaryNumberFluxLift S x c)
  rw [nativeGpreHilbertBoundaryNumberFlux_eq_level_mul_value,
    nativeGpreHilbertBoundaryNumberFlux_eq_level_mul_value]
  simp [RCLike.inner_apply, mul_assoc, mul_left_comm, mul_comm]

/-- The provenance relation remains symmetric after extension to all vertical
Hilbert states. -/
theorem nativeGpreHilbertProvenanceBoundaryRelation_isSymmetric
    (S : Finset NativeGpreBoundaryContext) :
    NativeBoundaryRelationIsSymmetric
      (nativeGpreHilbertProvenanceBoundaryPencil S).relation :=
  LinearBoundaryPencil.relation_isSymmetric_of_satisfiesGreenSymmetry
    (nativeGpreHilbertProvenanceBoundaryPencil S)
    (nativeGpreHilbertProvenanceBoundaryPencil_greenSymmetry S)

end

end CPFormal.Analytic.Cp
