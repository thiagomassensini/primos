import CPFormal.Analytic.CpCarryVerticalBoundaryGreenDefect
import CPFormal.Analytic.CpNativeGpreFiniteProvenanceGreenSymmetry
import CPFormal.Analytic.CpNativeGpreTfvdCanonicalGluing
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Green defect of the finite TFVD--G_pre Hilbert gluing

The finite native boundary is the `L2` product of

* the scalar vertical value--flux boundary;
* the finite provenance atlas with its real number flux.

The provenance leg is already Green-symmetric.  Therefore the exact Green
defect of the whole glued pencil is only the initial vertical Wronskian.  This
module proves that identity before imposing any spectral or zero condition.

It follows that a restriction of the edge core gives a symmetric native
boundary relation exactly when its canonical vertical realization is
Wronskian-isotropic.  This isolates the concrete job of the interior
bracket/Green boundary condition: it must select that isotropic domain while
preserving the provenance leg.
-/

open scoped ComplexConjugate InnerProduct

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Finite native Hilbert boundary: one vertical scalar plus the orthogonal
provenance atlas. -/
abbrev NativeGpreFiniteGluedHilbertBoundary
    (S : Finset NativeGpreBoundaryContext) :=
  WithLp 2 (ℂ × NativeGpreFiniteHilbertBoundaryCarrier S)

/-- Underlying product-valued trace of the finite native gluing. -/
def nativeGpreFiniteGluedHilbertValueTraceProduct
    (q : ℝ) (S : Finset NativeGpreBoundaryContext) :
    NativeGpreComplexEdgeCore →ₗ[ℂ]
      (ℂ × NativeGpreFiniteHilbertBoundaryCarrier S) :=
  ((carryWeightedVerticalBoundaryPencil q).valueTrace.comp
      nativeGpreCanonicalVerticalRealization).prod
    (nativeGpreFiniteHilbertBoundaryValueLift S)

/-- Underlying product-valued flux of the finite native gluing. -/
def nativeGpreFiniteGluedHilbertFluxTraceProduct
    (q : ℝ) (S : Finset NativeGpreBoundaryContext) :
    NativeGpreComplexEdgeCore →ₗ[ℂ]
      (ℂ × NativeGpreFiniteHilbertBoundaryCarrier S) :=
  ((carryWeightedVerticalBoundaryPencil q).fluxTrace.comp
      nativeGpreCanonicalVerticalRealization).prod
    (nativeGpreFiniteHilbertBoundaryNumberFluxLift S)

/-- Value trace placed in the `L2` product Hilbert boundary. -/
noncomputable def nativeGpreFiniteGluedHilbertValueTrace
    (q : ℝ) (S : Finset NativeGpreBoundaryContext) :
    NativeGpreComplexEdgeCore →ₗ[ℂ]
      NativeGpreFiniteGluedHilbertBoundary S :=
  (WithLp.linearEquiv 2 ℂ
      (ℂ × NativeGpreFiniteHilbertBoundaryCarrier S)).symm.toLinearMap.comp
    (nativeGpreFiniteGluedHilbertValueTraceProduct q S)

/-- Flux trace placed in the same `L2` product Hilbert boundary. -/
noncomputable def nativeGpreFiniteGluedHilbertFluxTrace
    (q : ℝ) (S : Finset NativeGpreBoundaryContext) :
    NativeGpreComplexEdgeCore →ₗ[ℂ]
      NativeGpreFiniteGluedHilbertBoundary S :=
  (WithLp.linearEquiv 2 ℂ
      (ℂ × NativeGpreFiniteHilbertBoundaryCarrier S)).symm.toLinearMap.comp
    (nativeGpreFiniteGluedHilbertFluxTraceProduct q S)

@[simp] theorem nativeGpreFiniteGluedHilbertValueTrace_ofLp
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (x : NativeGpreComplexEdgeCore) :
    WithLp.ofLp (nativeGpreFiniteGluedHilbertValueTrace q S x) =
      (x 0, nativeGpreFiniteHilbertBoundaryValueLift S x) := by
  rfl

@[simp] theorem nativeGpreFiniteGluedHilbertFluxTrace_ofLp
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (x : NativeGpreComplexEdgeCore) :
    WithLp.ofLp (nativeGpreFiniteGluedHilbertFluxTrace q S x) =
      ((q : ℂ)⁻¹ * x 1 - x 0,
        nativeGpreFiniteHilbertBoundaryNumberFluxLift S x) := by
  rfl

/-- The fixed finite TFVD--G_pre pencil in the natural orthogonal boundary
carrier. -/
def nativeGpreFiniteGluedHilbertBoundaryPencil
    (q : ℝ) (S : Finset NativeGpreBoundaryContext) :
    LinearBoundaryPencil NativeGpreComplexEdgeCore
      (NativeGpreFiniteGluedHilbertBoundary S) where
  valueTrace := nativeGpreFiniteGluedHilbertValueTrace q S
  fluxTrace := nativeGpreFiniteGluedHilbertFluxTrace q S

/-- Exact computation: provenance contributes zero Green defect, hence the
whole finite glued defect is the vertical Wronskian. -/
theorem nativeGpreFiniteGluedHilbertGreenDefect_eq_verticalWronskian
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (x y : NativeGpreComplexEdgeCore) :
    inner ℂ
        ((nativeGpreFiniteGluedHilbertBoundaryPencil q S).fluxTrace y)
        ((nativeGpreFiniteGluedHilbertBoundaryPencil q S).valueTrace x) -
      inner ℂ
        ((nativeGpreFiniteGluedHilbertBoundaryPencil q S).valueTrace y)
        ((nativeGpreFiniteGluedHilbertBoundaryPencil q S).fluxTrace x) =
      carryWeightedVerticalBoundaryWronskian q
        (nativeGpreCanonicalVerticalRealization x)
        (nativeGpreCanonicalVerticalRealization y) := by
  have hvertical :=
    carryWeightedVerticalBoundaryGreenDefect_eq_wronskian q
      (nativeGpreCanonicalVerticalRealization x)
      (nativeGpreCanonicalVerticalRealization y)
  have hprovenance :=
    nativeGpreFiniteHilbertProvenanceBoundaryPencil_greenSymmetry S x y
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  simp only [nativeGpreFiniteGluedHilbertValueTrace_ofLp,
    nativeGpreFiniteGluedHilbertFluxTrace_ofLp, Prod.fst, Prod.snd]
  change
    (inner ℂ
        ((carryWeightedVerticalBoundaryPencil q).fluxTrace
          (nativeGpreCanonicalVerticalRealization y))
        ((carryWeightedVerticalBoundaryPencil q).valueTrace
          (nativeGpreCanonicalVerticalRealization x)) +
      inner ℂ
        (nativeGpreFiniteHilbertBoundaryNumberFluxLift S y)
        (nativeGpreFiniteHilbertBoundaryValueLift S x)) -
    (inner ℂ
        ((carryWeightedVerticalBoundaryPencil q).valueTrace
          (nativeGpreCanonicalVerticalRealization y))
        ((carryWeightedVerticalBoundaryPencil q).fluxTrace
          (nativeGpreCanonicalVerticalRealization x)) +
      inner ℂ
        (nativeGpreFiniteHilbertBoundaryValueLift S y)
        (nativeGpreFiniteHilbertBoundaryNumberFluxLift S x)) = _
  rw [hprovenance]
  linarith

/-- A subspace of native edge states is boundary-isotropic when the canonical
vertical realizations have pairwise zero Wronskian. -/
def NativeGpreFiniteGluedBoundaryIsotropic
    (q : ℝ) (D : Submodule ℂ NativeGpreComplexEdgeCore) : Prop :=
  ∀ x y : D,
    carryWeightedVerticalBoundaryWronskian q
      (nativeGpreCanonicalVerticalRealization x)
      (nativeGpreCanonicalVerticalRealization y) = 0

/-- Restrict the finite native pencil to one admitted edge-state domain. -/
def nativeGpreFiniteGluedHilbertBoundaryPencilOn
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (D : Submodule ℂ NativeGpreComplexEdgeCore) :
    LinearBoundaryPencil D (NativeGpreFiniteGluedHilbertBoundary S) :=
  (nativeGpreFiniteGluedHilbertBoundaryPencil q S).pullback D.subtype

/-- Exact domain criterion: the restricted finite gluing is Green-symmetric iff
its vertical boundary data are Wronskian-isotropic. -/
theorem nativeGpreFiniteGluedHilbertBoundaryPencilOn_greenSymmetry_iff
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (D : Submodule ℂ NativeGpreComplexEdgeCore) :
    LinearBoundaryPencil.SatisfiesGreenSymmetry
        (nativeGpreFiniteGluedHilbertBoundaryPencilOn q S D) ↔
      NativeGpreFiniteGluedBoundaryIsotropic q D := by
  constructor
  · intro hgreen x y
    have hxy := hgreen x y
    have hdefect :=
      nativeGpreFiniteGluedHilbertGreenDefect_eq_verticalWronskian
        q S (x : NativeGpreComplexEdgeCore) (y : NativeGpreComplexEdgeCore)
    change
      inner ℂ
          ((nativeGpreFiniteGluedHilbertBoundaryPencil q S).fluxTrace
            (y : NativeGpreComplexEdgeCore))
          ((nativeGpreFiniteGluedHilbertBoundaryPencil q S).valueTrace
            (x : NativeGpreComplexEdgeCore)) =
        inner ℂ
          ((nativeGpreFiniteGluedHilbertBoundaryPencil q S).valueTrace
            (y : NativeGpreComplexEdgeCore))
          ((nativeGpreFiniteGluedHilbertBoundaryPencil q S).fluxTrace
            (x : NativeGpreComplexEdgeCore))
      at hxy
    rw [hxy, sub_self] at hdefect
    exact hdefect.symm
  · intro hisotropic x y
    have hw := hisotropic x y
    have hdefect :=
      nativeGpreFiniteGluedHilbertGreenDefect_eq_verticalWronskian
        q S (x : NativeGpreComplexEdgeCore) (y : NativeGpreComplexEdgeCore)
    rw [hw] at hdefect
    exact sub_eq_zero.mp hdefect

/-- Every isotropic finite native domain produces a symmetric boundary
relation, with no scalar compression of the provenance atlas. -/
theorem nativeGpreFiniteGluedHilbertBoundaryRelation_isSymmetric
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (D : Submodule ℂ NativeGpreComplexEdgeCore)
    (hD : NativeGpreFiniteGluedBoundaryIsotropic q D) :
    NativeBoundaryRelationIsSymmetric
      (nativeGpreFiniteGluedHilbertBoundaryPencilOn q S D).relation :=
  LinearBoundaryPencil.relation_isSymmetric_of_satisfiesGreenSymmetry
    (nativeGpreFiniteGluedHilbertBoundaryPencilOn q S D)
    ((nativeGpreFiniteGluedHilbertBoundaryPencilOn_greenSymmetry_iff
      q S D).2 hD)

end

end CPFormal.Analytic.Cp
