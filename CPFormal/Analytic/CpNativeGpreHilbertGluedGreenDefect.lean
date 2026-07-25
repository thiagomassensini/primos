import CPFormal.Analytic.CpCarryVerticalBoundaryGreenDefect
import CPFormal.Analytic.CpNativeGpreHilbertProvenanceGreenSymmetry
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Full Hilbert TFVD--G_pre boundary gluing

This is the operator-level finite-atlas boundary carrier.  Both traces act on
the complete vertical carry Hilbert space:

`Gamma_0 x = (x 0, provenanceValue x)`,
`Gamma_1 x = (q^(-1) x 1 - x 0, provenanceNumberFlux x)`.

The provenance coordinates are orthogonal and Green-symmetric.  Hence the
complete glued Green defect is exactly the initial vertical Wronskian.  A
submodule is therefore an admissible symmetric operator domain precisely when
that Wronskian vanishes pairwise on it.
-/

open scoped ComplexConjugate InnerProduct

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Full finite-atlas Hilbert boundary: vertical scalar plus provenance. -/
abbrev NativeGpreHilbertGluedBoundary
    (S : Finset NativeGpreBoundaryContext) :=
  WithLp 2 (ℂ × NativeGpreFiniteHilbertBoundaryCarrier S)

/-- Product-valued full-Hilbert value trace. -/
def nativeGpreHilbertGluedValueTraceProduct
    (q : ℝ) (S : Finset NativeGpreBoundaryContext) :
    CarryVerticalL2 →ₗ[ℂ]
      (ℂ × NativeGpreFiniteHilbertBoundaryCarrier S) :=
  (carryWeightedVerticalBoundaryPencil q).valueTrace.prod
    (nativeGpreHilbertBoundaryValueLift S)

/-- Product-valued full-Hilbert flux trace. -/
def nativeGpreHilbertGluedFluxTraceProduct
    (q : ℝ) (S : Finset NativeGpreBoundaryContext) :
    CarryVerticalL2 →ₗ[ℂ]
      (ℂ × NativeGpreFiniteHilbertBoundaryCarrier S) :=
  (carryWeightedVerticalBoundaryPencil q).fluxTrace.prod
    (nativeGpreHilbertBoundaryNumberFluxLift S)

/-- Full-Hilbert value trace in the orthogonal boundary carrier. -/
noncomputable def nativeGpreHilbertGluedValueTrace
    (q : ℝ) (S : Finset NativeGpreBoundaryContext) :
    CarryVerticalL2 →ₗ[ℂ] NativeGpreHilbertGluedBoundary S :=
  (WithLp.linearEquiv 2 ℂ
      (ℂ × NativeGpreFiniteHilbertBoundaryCarrier S)).symm.toLinearMap.comp
    (nativeGpreHilbertGluedValueTraceProduct q S)

/-- Full-Hilbert flux trace in the same orthogonal carrier. -/
noncomputable def nativeGpreHilbertGluedFluxTrace
    (q : ℝ) (S : Finset NativeGpreBoundaryContext) :
    CarryVerticalL2 →ₗ[ℂ] NativeGpreHilbertGluedBoundary S :=
  (WithLp.linearEquiv 2 ℂ
      (ℂ × NativeGpreFiniteHilbertBoundaryCarrier S)).symm.toLinearMap.comp
    (nativeGpreHilbertGluedFluxTraceProduct q S)

@[simp] theorem nativeGpreHilbertGluedValueTrace_ofLp
    (q : ℝ) (S : Finset NativeGpreBoundaryContext) (x : CarryVerticalL2) :
    WithLp.ofLp (nativeGpreHilbertGluedValueTrace q S x) =
      (x 0, nativeGpreHilbertBoundaryValueLift S x) := by
  rfl

@[simp] theorem nativeGpreHilbertGluedFluxTrace_ofLp
    (q : ℝ) (S : Finset NativeGpreBoundaryContext) (x : CarryVerticalL2) :
    WithLp.ofLp (nativeGpreHilbertGluedFluxTrace q S x) =
      ((q : ℂ)⁻¹ * x 1 - x 0,
        nativeGpreHilbertBoundaryNumberFluxLift S x) := by
  rfl

/-- Fixed full-Hilbert finite-atlas carry boundary pencil. -/
def nativeGpreHilbertGluedBoundaryPencil
    (q : ℝ) (S : Finset NativeGpreBoundaryContext) :
    LinearBoundaryPencil CarryVerticalL2
      (NativeGpreHilbertGluedBoundary S) where
  valueTrace := nativeGpreHilbertGluedValueTrace q S
  fluxTrace := nativeGpreHilbertGluedFluxTrace q S

/-- Exact full-Hilbert identity: the glued defect is the initial vertical
Wronskian, with all provenance terms cancelling before scalar compression. -/
theorem nativeGpreHilbertGluedGreenDefect_eq_verticalWronskian
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (x y : CarryVerticalL2) :
    inner ℂ
        ((nativeGpreHilbertGluedBoundaryPencil q S).fluxTrace y)
        ((nativeGpreHilbertGluedBoundaryPencil q S).valueTrace x) -
      inner ℂ
        ((nativeGpreHilbertGluedBoundaryPencil q S).valueTrace y)
        ((nativeGpreHilbertGluedBoundaryPencil q S).fluxTrace x) =
      carryWeightedVerticalBoundaryWronskian q x y := by
  have hvertical :=
    carryWeightedVerticalBoundaryGreenDefect_eq_wronskian q x y
  have hprovenance :=
    nativeGpreHilbertProvenanceBoundaryPencil_greenSymmetry S x y
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  change
    (inner ℂ
        ((carryWeightedVerticalBoundaryPencil q).fluxTrace y)
        ((carryWeightedVerticalBoundaryPencil q).valueTrace x) +
      inner ℂ
        (nativeGpreHilbertBoundaryNumberFluxLift S y)
        (nativeGpreHilbertBoundaryValueLift S x)) -
    (inner ℂ
        ((carryWeightedVerticalBoundaryPencil q).valueTrace y)
        ((carryWeightedVerticalBoundaryPencil q).fluxTrace x) +
      inner ℂ
        (nativeGpreHilbertBoundaryValueLift S y)
        (nativeGpreHilbertBoundaryNumberFluxLift S x)) = _
  rw [hprovenance]
  linear_combination hvertical

/-- Restriction of the full-Hilbert native pencil to a proposed operator
domain. -/
def nativeGpreHilbertGluedBoundaryPencilOn
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (D : Submodule ℂ CarryVerticalL2) :
    LinearBoundaryPencil D (NativeGpreHilbertGluedBoundary S) :=
  (nativeGpreHilbertGluedBoundaryPencil q S).pullback D.subtype

/-- Exact characterization of symmetric full-Hilbert domains. -/
theorem nativeGpreHilbertGluedBoundaryPencilOn_greenSymmetry_iff
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (D : Submodule ℂ CarryVerticalL2) :
    LinearBoundaryPencil.SatisfiesGreenSymmetry
        (nativeGpreHilbertGluedBoundaryPencilOn q S D) ↔
      CarryVerticalBoundaryIsotropic q D := by
  constructor
  · intro hgreen x y
    have hxy := hgreen x y
    have hdefect :=
      nativeGpreHilbertGluedGreenDefect_eq_verticalWronskian
        q S (x : CarryVerticalL2) (y : CarryVerticalL2)
    change
      inner ℂ
          ((nativeGpreHilbertGluedBoundaryPencil q S).fluxTrace
            (y : CarryVerticalL2))
          ((nativeGpreHilbertGluedBoundaryPencil q S).valueTrace
            (x : CarryVerticalL2)) =
        inner ℂ
          ((nativeGpreHilbertGluedBoundaryPencil q S).valueTrace
            (y : CarryVerticalL2))
          ((nativeGpreHilbertGluedBoundaryPencil q S).fluxTrace
            (x : CarryVerticalL2))
      at hxy
    rw [hxy, sub_self] at hdefect
    exact hdefect.symm
  · intro hisotropic x y
    have hw := hisotropic x y
    have hdefect :=
      nativeGpreHilbertGluedGreenDefect_eq_verticalWronskian
        q S (x : CarryVerticalL2) (y : CarryVerticalL2)
    rw [hw] at hdefect
    exact sub_eq_zero.mp hdefect

/-- Every Wronskian-isotropic full-Hilbert domain gives a symmetric native
boundary relation. -/
theorem nativeGpreHilbertGluedBoundaryRelation_isSymmetric
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (D : Submodule ℂ CarryVerticalL2)
    (hD : CarryVerticalBoundaryIsotropic q D) :
    NativeBoundaryRelationIsSymmetric
      (nativeGpreHilbertGluedBoundaryPencilOn q S D).relation :=
  LinearBoundaryPencil.relation_isSymmetric_of_satisfiesGreenSymmetry
    (nativeGpreHilbertGluedBoundaryPencilOn q S D)
    ((nativeGpreHilbertGluedBoundaryPencilOn_greenSymmetry_iff
      q S D).2 hD)

end

end CPFormal.Analytic.Cp
