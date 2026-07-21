import CPFormal.Analytic.CpNativeGpreTfvdCanonicalGluing
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Relacao fechada TFVD--G_pre em todo atlas finito de proveniencia

A colagem canonica anterior ainda usava o carrier integral de todos os
contextos. Este modulo fixa um atlas finito `S` de contextos de proveniencia e
restringe os tracos `G_pre` a `C^S`.

O bordo conjunto e entao

`C x C^S`,

e a relacao valor--fluxo vive em

`(C x C^S) x (C x C^S)`.

Esse espaco e finito-dimensional. Portanto o kernel prova que a relacao de
cada cutoff e fechada, sem usar uma cota uniforme e sem antecipar a completion
infinita. Os teoremas de firewall permanecem validos: cada coordenada ativa
forca `lambda=j`, e dois niveis distintos impedem um fechamento escalar comum.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Carrier de proveniencia restrito a um atlas finito. -/
abbrev NativeGpreFiniteBoundaryCarrier
    (S : Finset NativeGpreBoundaryContext) :=
  (c : ↥S) → ℂ

/-- Traco de valor `G_pre` restrito ao atlas `S`. -/
def nativeGpreFiniteBoundaryValueLift
    (S : Finset NativeGpreBoundaryContext) :
    NativeGpreComplexEdgeCore →ₗ[ℂ] NativeGpreFiniteBoundaryCarrier S where
  toFun x c := nativeGpreBoundaryValueLift x c.1
  map_add' x y := by
    funext c
    simp
  map_smul' a x := by
    funext c
    simp

/-- Traco de fluxo numero restrito ao mesmo atlas. -/
def nativeGpreFiniteBoundaryNumberFluxLift
    (S : Finset NativeGpreBoundaryContext) :
    NativeGpreComplexEdgeCore →ₗ[ℂ] NativeGpreFiniteBoundaryCarrier S where
  toFun x c := nativeGpreBoundaryNumberFluxLift x c.1
  map_add' x y := by
    funext c
    simp
  map_smul' a x := by
    funext c
    simp

@[simp] theorem nativeGpreFiniteBoundaryValueLift_apply
    (S : Finset NativeGpreBoundaryContext)
    (x : NativeGpreComplexEdgeCore) (c : ↥S) :
    nativeGpreFiniteBoundaryValueLift S x c =
      nativeGpreBoundaryValueLift x c.1 := rfl

@[simp] theorem nativeGpreFiniteBoundaryNumberFluxLift_apply
    (S : Finset NativeGpreBoundaryContext)
    (x : NativeGpreComplexEdgeCore) (c : ↥S) :
    nativeGpreFiniteBoundaryNumberFluxLift S x c =
      nativeGpreBoundaryNumberFluxLift x c.1 := rfl

/-- Lei numero no atlas finito. -/
theorem nativeGpreFiniteBoundaryNumberFlux_eq_level_mul_value
    (S : Finset NativeGpreBoundaryContext)
    (x : NativeGpreComplexEdgeCore) (c : ↥S) :
    nativeGpreFiniteBoundaryNumberFluxLift S x c =
      (c.1.towerLevel.val : ℂ) *
        nativeGpreFiniteBoundaryValueLift S x c := by
  exact nativeGpreBoundaryNumberFluxLift_apply_eq_level_mul_value x c.1

/-- Pencil aritmetico restrito ao atlas finito. -/
def nativeGpreFiniteProvenanceBoundaryPencil
    (S : Finset NativeGpreBoundaryContext) :
    LinearBoundaryPencil NativeGpreComplexEdgeCore
      (NativeGpreFiniteBoundaryCarrier S) where
  valueTrace := nativeGpreFiniteBoundaryValueLift S
  fluxTrace := nativeGpreFiniteBoundaryNumberFluxLift S

@[simp] theorem nativeGpreFiniteProvenanceBoundaryPencil_operator_apply
    (S : Finset NativeGpreBoundaryContext)
    (lambda : ℂ) (x : NativeGpreComplexEdgeCore) (c : ↥S) :
    (nativeGpreFiniteProvenanceBoundaryPencil S).operator lambda x c =
      ((c.1.towerLevel.val : ℂ) - lambda) *
        nativeGpreFiniteBoundaryValueLift S x c := by
  change nativeGpreFiniteBoundaryNumberFluxLift S x c -
      lambda * nativeGpreFiniteBoundaryValueLift S x c = _
  rw [nativeGpreFiniteBoundaryNumberFlux_eq_level_mul_value]
  ring

/-- Toda relacao aritmetica de cutoff e fechada. -/
theorem nativeGpreFiniteProvenanceBoundaryRelation_isClosed
    (S : Finset NativeGpreBoundaryContext) :
    IsClosed
      ((nativeGpreFiniteProvenanceBoundaryPencil S).relation :
        Set (NativeGpreFiniteBoundaryCarrier S ×
          NativeGpreFiniteBoundaryCarrier S)) := by
  exact Submodule.closed_of_finiteDimensional _

/-- Uma coordenada ativa do atlas finito fixa o nivel caracteristico. -/
theorem nativeGpreFiniteProvenance_operator_eq_zero_forces_level
    (S : Finset NativeGpreBoundaryContext)
    (lambda : ℂ) (x : NativeGpreComplexEdgeCore)
    (hzero :
      (nativeGpreFiniteProvenanceBoundaryPencil S).operator lambda x = 0)
    (c : ↥S)
    (hactive : nativeGpreFiniteBoundaryValueLift S x c ≠ 0) :
    lambda = (c.1.towerLevel.val : ℂ) := by
  have hcoord := congrFun hzero c
  have hmul :
      ((c.1.towerLevel.val : ℂ) - lambda) *
        nativeGpreFiniteBoundaryValueLift S x c = 0 := by
    simpa using hcoord
  have hfactor : (c.1.towerLevel.val : ℂ) - lambda = 0 :=
    (mul_eq_zero.mp hmul).resolve_right hactive
  exact (sub_eq_zero.mp hfactor).symm

/-- Bordo conjunto finito. -/
abbrev NativeGpreFiniteTfvdBoundary
    (S : Finset NativeGpreBoundaryContext) :=
  ℂ × NativeGpreFiniteBoundaryCarrier S

/-- Traco conjunto de valor no mesmo vetor de arestas. -/
def nativeGpreFiniteCanonicalTfvdValueTrace
    (q : ℝ) (S : Finset NativeGpreBoundaryContext) :
    NativeGpreComplexEdgeCore →ₗ[ℂ] NativeGpreFiniteTfvdBoundary S :=
  (((carryWeightedVerticalBoundaryPencil q).valueTrace.comp
      nativeGpreCanonicalVerticalRealization).prod
    (nativeGpreFiniteBoundaryValueLift S))

/-- Traco conjunto de fluxo no mesmo vetor de arestas. -/
def nativeGpreFiniteCanonicalTfvdFluxTrace
    (q : ℝ) (S : Finset NativeGpreBoundaryContext) :
    NativeGpreComplexEdgeCore →ₗ[ℂ] NativeGpreFiniteTfvdBoundary S :=
  (((carryWeightedVerticalBoundaryPencil q).fluxTrace.comp
      nativeGpreCanonicalVerticalRealization).prod
    (nativeGpreFiniteBoundaryNumberFluxLift S))

/-- Pencil canonico enriquecido em um cutoff finito de proveniencia. -/
def nativeGpreFiniteCanonicalTfvdBoundaryPencil
    (q : ℝ) (S : Finset NativeGpreBoundaryContext) :
    LinearBoundaryPencil NativeGpreComplexEdgeCore
      (NativeGpreFiniteTfvdBoundary S) where
  valueTrace := nativeGpreFiniteCanonicalTfvdValueTrace q S
  fluxTrace := nativeGpreFiniteCanonicalTfvdFluxTrace q S

@[simp] theorem nativeGpreFiniteCanonicalTfvdBoundaryPencil_valueTrace_apply
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (x : NativeGpreComplexEdgeCore) :
    (nativeGpreFiniteCanonicalTfvdBoundaryPencil q S).valueTrace x =
      (x 0, nativeGpreFiniteBoundaryValueLift S x) := by
  rfl

@[simp] theorem nativeGpreFiniteCanonicalTfvdBoundaryPencil_fluxTrace_apply
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (x : NativeGpreComplexEdgeCore) :
    (nativeGpreFiniteCanonicalTfvdBoundaryPencil q S).fluxTrace x =
      ((q : ℂ)⁻¹ * x 1 - x 0,
        nativeGpreFiniteBoundaryNumberFluxLift S x) := by
  rfl

/-- A projecao TFVD do operador finito continua livre. -/
@[simp] theorem nativeGpreFiniteCanonicalTfvdBoundaryPencil_operator_fst
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (lambda : ℂ) (x : NativeGpreComplexEdgeCore) :
    ((nativeGpreFiniteCanonicalTfvdBoundaryPencil q S).operator lambda x).1 =
      (carryWeightedVerticalBoundaryPencil q).operator lambda
        (nativeGpreCanonicalVerticalRealization x) := by
  rfl

/-- A projecao de proveniencia e exatamente o pencil finito `G_pre`. -/
@[simp] theorem nativeGpreFiniteCanonicalTfvdBoundaryPencil_operator_snd
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (lambda : ℂ) (x : NativeGpreComplexEdgeCore) :
    ((nativeGpreFiniteCanonicalTfvdBoundaryPencil q S).operator lambda x).2 =
      (nativeGpreFiniteProvenanceBoundaryPencil S).operator lambda x := by
  rfl

/-- Resultado topologico central: toda relacao enriquecida de cutoff e
fechada. -/
theorem nativeGpreFiniteCanonicalTfvdBoundaryRelation_isClosed
    (q : ℝ) (S : Finset NativeGpreBoundaryContext) :
    IsClosed
      ((nativeGpreFiniteCanonicalTfvdBoundaryPencil q S).relation :
        Set (NativeGpreFiniteTfvdBoundary S ×
          NativeGpreFiniteTfvdBoundary S)) := by
  exact Submodule.closed_of_finiteDimensional _

/-- Esquecer a proveniencia recupera uma relacao da valvula vertical livre. -/
theorem nativeGpreFiniteCanonicalTfvdRelation_vertical_projection
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    {boundary : NativeGpreFiniteTfvdBoundary S ×
      NativeGpreFiniteTfvdBoundary S}
    (hboundary : boundary ∈
      (nativeGpreFiniteCanonicalTfvdBoundaryPencil q S).relation) :
    (boundary.1.1, boundary.2.1) ∈
      (carryWeightedVerticalBoundaryPencil q).relation := by
  change boundary ∈ LinearMap.range
    ((nativeGpreFiniteCanonicalTfvdBoundaryPencil q S).valueTrace.prod
      (nativeGpreFiniteCanonicalTfvdBoundaryPencil q S).fluxTrace) at hboundary
  rcases hboundary with ⟨x, rfl⟩
  change
    ((carryWeightedVerticalBoundaryPencil q).valueTrace
        (nativeGpreCanonicalVerticalRealization x),
      (carryWeightedVerticalBoundaryPencil q).fluxTrace
        (nativeGpreCanonicalVerticalRealization x)) ∈
      LinearMap.range
        ((carryWeightedVerticalBoundaryPencil q).valueTrace.prod
          (carryWeightedVerticalBoundaryPencil q).fluxTrace)
  exact ⟨nativeGpreCanonicalVerticalRealization x, rfl⟩

/-- Esquecer a perna vertical recupera a relacao aritmetica finita. -/
theorem nativeGpreFiniteCanonicalTfvdRelation_provenance_projection
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    {boundary : NativeGpreFiniteTfvdBoundary S ×
      NativeGpreFiniteTfvdBoundary S}
    (hboundary : boundary ∈
      (nativeGpreFiniteCanonicalTfvdBoundaryPencil q S).relation) :
    (boundary.1.2, boundary.2.2) ∈
      (nativeGpreFiniteProvenanceBoundaryPencil S).relation := by
  change boundary ∈ LinearMap.range
    ((nativeGpreFiniteCanonicalTfvdBoundaryPencil q S).valueTrace.prod
      (nativeGpreFiniteCanonicalTfvdBoundaryPencil q S).fluxTrace) at hboundary
  rcases hboundary with ⟨x, rfl⟩
  change
    (nativeGpreFiniteBoundaryValueLift S x,
      nativeGpreFiniteBoundaryNumberFluxLift S x) ∈
      LinearMap.range
        ((nativeGpreFiniteBoundaryValueLift S).prod
          (nativeGpreFiniteBoundaryNumberFluxLift S))
  exact ⟨x, rfl⟩

/-- Uma coordenada ativa no cutoff ainda fixa `lambda=j`. -/
theorem nativeGpreFiniteCanonicalTfvd_operator_eq_zero_forces_level
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (lambda : ℂ) (x : NativeGpreComplexEdgeCore)
    (hzero :
      (nativeGpreFiniteCanonicalTfvdBoundaryPencil q S).operator lambda x = 0)
    (c : ↥S)
    (hactive : nativeGpreFiniteBoundaryValueLift S x c ≠ 0) :
    lambda = (c.1.towerLevel.val : ℂ) := by
  have hsnd := congrArg Prod.snd hzero
  have hgpre :
      (nativeGpreFiniteProvenanceBoundaryPencil S).operator lambda x = 0 := by
    change nativeGpreFiniteBoundaryNumberFluxLift S x -
      lambda • nativeGpreFiniteBoundaryValueLift S x = 0
    exact hsnd
  exact nativeGpreFiniteProvenance_operator_eq_zero_forces_level
    S lambda x hgpre c hactive

/-- Dois niveis ativos distintos impedem um zero do pencil enriquecido
finito. -/
theorem nativeGpreFiniteCanonicalTfvd_no_zero_on_two_distinct_levels
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (lambda : ℂ) (x : NativeGpreComplexEdgeCore)
    (c d : ↥S)
    (hc : nativeGpreFiniteBoundaryValueLift S x c ≠ 0)
    (hd : nativeGpreFiniteBoundaryValueLift S x d ≠ 0)
    (hlevels : c.1.towerLevel.val ≠ d.1.towerLevel.val) :
    (nativeGpreFiniteCanonicalTfvdBoundaryPencil q S).operator lambda x ≠ 0 := by
  intro hzero
  have hcLevel := nativeGpreFiniteCanonicalTfvd_operator_eq_zero_forces_level
    q S lambda x hzero c hc
  have hdLevel := nativeGpreFiniteCanonicalTfvd_operator_eq_zero_forces_level
    q S lambda x hzero d hd
  have hcast : (c.1.towerLevel.val : ℂ) = (d.1.towerLevel.val : ℂ) :=
    hcLevel.symm.trans hdLevel
  apply hlevels
  exact_mod_cast hcast

end

end CPFormal.Analytic.Cp
