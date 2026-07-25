import CPFormal.Analytic.CpNativeCarryBoundaryGreenSymmetry
import CPFormal.Analytic.CpCarryWeightedVerticalBoundaryPencil

/-!
# Exact Green defect of the free vertical carry boundary

The free weighted TFVD boundary has value and flux

`Gamma_0 x = x 0`,
`Gamma_1 x = q^(-1) x 1 - x 0`.

Its failure of Green symmetry is not mysterious: it is exactly the initial
Wronskian

`q^(-1) * (conj (y 1) * x 0 - conj (y 0) * x 1)`.

Consequently, restricting the vertical states to a submodule is Green-symmetric
if and only if that submodule is isotropic for this Wronskian.  This gives the
precise domain condition that the bracket/Green/provenance gluing must supply.
-/

open scoped ComplexConjugate InnerProduct

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Initial Wronskian in the amplitude coordinates of the weighted carry
boundary. -/
def carryWeightedVerticalBoundaryWronskian
    (q : ℝ) (x y : CarryVerticalL2) : ℂ :=
  (q : ℂ)⁻¹ *
    ((starRingEnd ℂ) (y 1) * x 0 -
      (starRingEnd ℂ) (y 0) * x 1)

/-- The two-state Green defect of the free boundary pencil is exactly the
initial Wronskian. -/
theorem carryWeightedVerticalBoundaryGreenDefect_eq_wronskian
    (q : ℝ) (x y : CarryVerticalL2) :
    inner ℂ
        ((carryWeightedVerticalBoundaryPencil q).fluxTrace y)
        ((carryWeightedVerticalBoundaryPencil q).valueTrace x) -
      inner ℂ
        ((carryWeightedVerticalBoundaryPencil q).valueTrace y)
        ((carryWeightedVerticalBoundaryPencil q).fluxTrace x) =
      carryWeightedVerticalBoundaryWronskian q x y := by
  rw [carryWeightedVerticalBoundaryPencil_valueTrace_apply,
    carryWeightedVerticalBoundaryPencil_fluxTrace_apply,
    carryWeightedVerticalBoundaryPencil_valueTrace_apply,
    carryWeightedVerticalBoundaryPencil_fluxTrace_apply]
  simp [carryWeightedVerticalBoundaryWronskian, RCLike.inner_apply]
  ring

/-- A vertical domain is admissible for Green symmetry when its initial
Wronskian vanishes pairwise. -/
def CarryVerticalBoundaryIsotropic
    (q : ℝ) (D : Submodule ℂ CarryVerticalL2) : Prop :=
  ∀ x y : D,
    carryWeightedVerticalBoundaryWronskian q (x : CarryVerticalL2)
      (y : CarryVerticalL2) = 0

/-- Restriction of the free vertical boundary pencil to an admitted domain. -/
def carryWeightedVerticalBoundaryPencilOn
    (q : ℝ) (D : Submodule ℂ CarryVerticalL2) :
    LinearBoundaryPencil D ℂ where
  valueTrace :=
    (carryWeightedVerticalBoundaryPencil q).valueTrace.comp D.subtype
  fluxTrace :=
    (carryWeightedVerticalBoundaryPencil q).fluxTrace.comp D.subtype

@[simp] theorem carryWeightedVerticalBoundaryPencilOn_valueTrace_apply
    (q : ℝ) (D : Submodule ℂ CarryVerticalL2) (x : D) :
    (carryWeightedVerticalBoundaryPencilOn q D).valueTrace x = x.1 0 := by
  rfl

@[simp] theorem carryWeightedVerticalBoundaryPencilOn_fluxTrace_apply
    (q : ℝ) (D : Submodule ℂ CarryVerticalL2) (x : D) :
    (carryWeightedVerticalBoundaryPencilOn q D).fluxTrace x =
      (q : ℂ)⁻¹ * x.1 1 - x.1 0 := by
  rfl

/-- Exact characterization: the restricted vertical pencil is Green-symmetric
precisely on Wronskian-isotropic domains. -/
theorem carryWeightedVerticalBoundaryPencilOn_satisfiesGreenSymmetry_iff
    (q : ℝ) (D : Submodule ℂ CarryVerticalL2) :
    LinearBoundaryPencil.SatisfiesGreenSymmetry
        (carryWeightedVerticalBoundaryPencilOn q D) ↔
      CarryVerticalBoundaryIsotropic q D := by
  constructor
  · intro hgreen x y
    have hxy := hgreen x y
    have hdefect :=
      carryWeightedVerticalBoundaryGreenDefect_eq_wronskian
        q (x : CarryVerticalL2) (y : CarryVerticalL2)
    change
      inner ℂ
          ((carryWeightedVerticalBoundaryPencil q).fluxTrace (y : CarryVerticalL2))
          ((carryWeightedVerticalBoundaryPencil q).valueTrace (x : CarryVerticalL2)) =
        inner ℂ
          ((carryWeightedVerticalBoundaryPencil q).valueTrace (y : CarryVerticalL2))
          ((carryWeightedVerticalBoundaryPencil q).fluxTrace (x : CarryVerticalL2))
      at hxy
    rw [hxy, sub_self] at hdefect
    exact hdefect.symm
  · intro hisotropic x y
    have hw := hisotropic x y
    have hdefect :=
      carryWeightedVerticalBoundaryGreenDefect_eq_wronskian
        q (x : CarryVerticalL2) (y : CarryVerticalL2)
    rw [hw] at hdefect
    exact sub_eq_zero.mp hdefect

/-- Any Wronskian-isotropic domain gives a symmetric boundary relation. -/
theorem carryWeightedVerticalBoundaryPencilOn_relation_isSymmetric
    (q : ℝ) (D : Submodule ℂ CarryVerticalL2)
    (hD : CarryVerticalBoundaryIsotropic q D) :
    NativeBoundaryRelationIsSymmetric
      (carryWeightedVerticalBoundaryPencilOn q D).relation :=
  LinearBoundaryPencil.relation_isSymmetric_of_satisfiesGreenSymmetry
    (carryWeightedVerticalBoundaryPencilOn q D)
    ((carryWeightedVerticalBoundaryPencilOn_satisfiesGreenSymmetry_iff q D).2 hD)

end

end CPFormal.Analytic.Cp
