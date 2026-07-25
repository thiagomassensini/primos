import CPFormal.Analytic.CpNativeCarryBoundaryGreenSymmetry
import CPFormal.Analytic.CpNativeGpreTfvdFiniteClosedRelation
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Green symmetry of the finite native G_pre provenance leg

The native provenance lift keeps every finite atlas coordinate separate.  Its
number-flux coordinate is the corresponding material tower level times the
value coordinate.  Since every tower level is real, the finite provenance
pencil is Green-symmetric in the canonical `L2` Hilbert structure.

This closes one genuine piece of the concrete carry boundary pencil.  It also
localizes the remaining obstruction: the free vertical value--flux plane is not
symmetric, whereas the provenance leg already is.  Thus the missing restriction
must be supplied by the interior bracket/Green boundary condition, not by
altering or summing away the provenance coordinates.
-/

open scoped InnerProduct

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Canonical finite-dimensional Hilbert realization of one provenance atlas. -/
abbrev NativeGpreFiniteHilbertBoundaryCarrier
    (S : Finset NativeGpreBoundaryContext) :=
  EuclideanSpace ℂ (↥S)

/-- Value lift into the canonical `L2` realization of the finite atlas. -/
noncomputable def nativeGpreFiniteHilbertBoundaryValueLift
    (S : Finset NativeGpreBoundaryContext) :
    NativeGpreComplexEdgeCore →ₗ[ℂ] NativeGpreFiniteHilbertBoundaryCarrier S where
  toFun x := WithLp.toLp 2 fun c => nativeGpreFiniteBoundaryValueLift S x c
  map_add' x y := by
    ext c
    simpa using congrArg (fun f => f c)
      ((nativeGpreFiniteBoundaryValueLift S).map_add x y)
  map_smul' a x := by
    ext c
    simpa using congrArg (fun f => f c)
      ((nativeGpreFiniteBoundaryValueLift S).map_smul a x)

/-- Number-flux lift into the same finite Hilbert atlas. -/
noncomputable def nativeGpreFiniteHilbertBoundaryNumberFluxLift
    (S : Finset NativeGpreBoundaryContext) :
    NativeGpreComplexEdgeCore →ₗ[ℂ] NativeGpreFiniteHilbertBoundaryCarrier S where
  toFun x := WithLp.toLp 2 fun c => nativeGpreFiniteBoundaryNumberFluxLift S x c
  map_add' x y := by
    ext c
    simpa using congrArg (fun f => f c)
      ((nativeGpreFiniteBoundaryNumberFluxLift S).map_add x y)
  map_smul' a x := by
    ext c
    simpa using congrArg (fun f => f c)
      ((nativeGpreFiniteBoundaryNumberFluxLift S).map_smul a x)

@[simp] theorem nativeGpreFiniteHilbertBoundaryValueLift_apply
    (S : Finset NativeGpreBoundaryContext)
    (x : NativeGpreComplexEdgeCore) (c : ↥S) :
    nativeGpreFiniteHilbertBoundaryValueLift S x c =
      nativeGpreFiniteBoundaryValueLift S x c := rfl

@[simp] theorem nativeGpreFiniteHilbertBoundaryNumberFluxLift_apply
    (S : Finset NativeGpreBoundaryContext)
    (x : NativeGpreComplexEdgeCore) (c : ↥S) :
    nativeGpreFiniteHilbertBoundaryNumberFluxLift S x c =
      nativeGpreFiniteBoundaryNumberFluxLift S x c := rfl

/-- The finite number flux is coordinatewise a real diagonal multiplier. -/
theorem nativeGpreFiniteHilbertBoundaryNumberFlux_eq_level_mul_value
    (S : Finset NativeGpreBoundaryContext)
    (x : NativeGpreComplexEdgeCore) (c : ↥S) :
    nativeGpreFiniteHilbertBoundaryNumberFluxLift S x c =
      (c.1.towerLevel.val : ℂ) *
        nativeGpreFiniteHilbertBoundaryValueLift S x c := by
  exact nativeGpreFiniteBoundaryNumberFlux_eq_level_mul_value S x c

/-- The provenance-only pencil in its canonical finite Hilbert realization. -/
def nativeGpreFiniteHilbertProvenanceBoundaryPencil
    (S : Finset NativeGpreBoundaryContext) :
    LinearBoundaryPencil NativeGpreComplexEdgeCore
      (NativeGpreFiniteHilbertBoundaryCarrier S) where
  valueTrace := nativeGpreFiniteHilbertBoundaryValueLift S
  fluxTrace := nativeGpreFiniteHilbertBoundaryNumberFluxLift S

/-- The real tower-level multiplier satisfies the exact two-state Green identity. -/
theorem nativeGpreFiniteHilbertProvenanceBoundaryPencil_greenSymmetry
    (S : Finset NativeGpreBoundaryContext) :
    LinearBoundaryPencil.SatisfiesGreenSymmetry
      (nativeGpreFiniteHilbertProvenanceBoundaryPencil S) := by
  intro x y
  rw [PiLp.inner_apply, PiLp.inner_apply]
  change
    (∑ c : ↥S,
      inner ℂ
        (nativeGpreFiniteBoundaryNumberFluxLift S y c)
        (nativeGpreFiniteBoundaryValueLift S x c)) =
      ∑ c : ↥S,
        inner ℂ
          (nativeGpreFiniteBoundaryValueLift S y c)
          (nativeGpreFiniteBoundaryNumberFluxLift S x c)
  apply Finset.sum_congr rfl
  intro c hc
  rw [nativeGpreFiniteBoundaryNumberFlux_eq_level_mul_value,
    nativeGpreFiniteBoundaryNumberFlux_eq_level_mul_value]
  simp [RCLike.inner_apply, mul_left_comm, mul_comm]

/-- Hence every finite provenance relation is symmetric. -/
theorem nativeGpreFiniteHilbertProvenanceBoundaryRelation_isSymmetric
    (S : Finset NativeGpreBoundaryContext) :
    NativeBoundaryRelationIsSymmetric
      (nativeGpreFiniteHilbertProvenanceBoundaryPencil S).relation :=
  LinearBoundaryPencil.relation_isSymmetric_of_satisfiesGreenSymmetry
    (nativeGpreFiniteHilbertProvenanceBoundaryPencil S)
    (nativeGpreFiniteHilbertProvenanceBoundaryPencil_greenSymmetry S)

/-- Any characteristic slope seen by the finite provenance leg is real. -/
theorem nativeGpreFiniteHilbertProvenanceSlope_im_eq_zero
    (S : Finset NativeGpreBoundaryContext) {z : ℂ}
    (hz : (nativeGpreFiniteHilbertProvenanceBoundaryPencil S).RelationHasSlope z) :
    z.im = 0 :=
  LinearBoundaryPencil.relationHasSlope_im_eq_zero_of_satisfiesGreenSymmetry
    (nativeGpreFiniteHilbertProvenanceBoundaryPencil S)
    (nativeGpreFiniteHilbertProvenanceBoundaryPencil_greenSymmetry S) hz

end

end CPFormal.Analytic.Cp
