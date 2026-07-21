import CPFormal.Analytic.CpNativeGpreBoundaryPencil
import Mathlib.LinearAlgebra.Prod

/-!
# Colagem tipada entre o TFVD vertical e a proveniencia G_pre

O TFVD vestido fornece a relacao livre do bordo. O lift `G_pre` fornece uma
relacao aritmetica contida no grafo do operador numero. Este modulo coloca as
duas pernas num mesmo pencil de produto sem identificar seus eixos.

A colagem concreta e parametrizada por uma realizacao vertical linear do core
de arestas. O mesmo vetor de arestas alimenta simultaneamente:

* o estado vertical em `ell^2`, onde atuam bracket, Green, traco e retorno;
* o carrier `G_pre`, onde permanecem primo, tempo aritmetico, divisor Jordan,
  celula, canto, orientacao, perna e nivel da torre.

O kernel prova que qualquer pencil assim colado e um pullback da relacao de
produto e que uma coordenada `G_pre` ativa ainda força o valor caracteristico
a coincidir com seu nivel `j`. Portanto a realizacao vertical, sozinha, nao
pode converter `j` no parametro real de fase `t`; essa seta devera vir de uma
lei Genuine adicional e explicitamente tipada.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

namespace LinearBoundaryPencil

variable {X B Z : Type*}
  [AddCommGroup X] [Module ℂ X]
  [AddCommGroup B] [Module ℂ B]
  [AddCommGroup Z] [Module ℂ Z]

/-- Pullback de um pencil ao longo de uma realizacao linear de estados. -/
def pullback (P : LinearBoundaryPencil X B) (f : Z →ₗ[ℂ] X) :
    LinearBoundaryPencil Z B where
  valueTrace := P.valueTrace.comp f
  fluxTrace := P.fluxTrace.comp f

@[simp] theorem pullback_valueTrace_apply
    (P : LinearBoundaryPencil X B) (f : Z →ₗ[ℂ] X) (z : Z) :
    (P.pullback f).valueTrace z = P.valueTrace (f z) := rfl

@[simp] theorem pullback_fluxTrace_apply
    (P : LinearBoundaryPencil X B) (f : Z →ₗ[ℂ] X) (z : Z) :
    (P.pullback f).fluxTrace z = P.fluxTrace (f z) := rfl

@[simp] theorem pullback_operator_apply
    (P : LinearBoundaryPencil X B) (f : Z →ₗ[ℂ] X)
    (lambda : ℂ) (z : Z) :
    (P.pullback f).operator lambda z = P.operator lambda (f z) := rfl

/-- A relacao de um pullback fica contida na relacao original. -/
theorem pullback_relation_le
    (P : LinearBoundaryPencil X B) (f : Z →ₗ[ℂ] X) :
    (P.pullback f).relation ≤ P.relation := by
  intro boundary hboundary
  change boundary ∈ LinearMap.range
    ((P.valueTrace.comp f).prod (P.fluxTrace.comp f)) at hboundary
  rcases hboundary with ⟨z, rfl⟩
  change (P.valueTrace (f z), P.fluxTrace (f z)) ∈
    LinearMap.range (P.valueTrace.prod P.fluxTrace)
  exact ⟨f z, rfl⟩

end LinearBoundaryPencil

/-- Estado antes da imposicao da colagem: perna vertical e perna aritmetica. -/
abbrev NativeGpreTfvdProductState :=
  CarryVerticalL2 × NativeGpreComplexEdgeCore

/-- Bordo enriquecido: dois escalares TFVD e o carrier integral de proveniencia. -/
abbrev NativeGpreTfvdProductBoundary :=
  ℂ × NativeGpreBoundaryCarrier

/-- Traco de valor do produto livre. -/
def nativeGpreTfvdProductValueTrace (q : ℝ) :
    NativeGpreTfvdProductState →ₗ[ℂ] NativeGpreTfvdProductBoundary :=
  (((carryWeightedVerticalBoundaryPencil q).valueTrace.comp
      (LinearMap.fst ℂ CarryVerticalL2 NativeGpreComplexEdgeCore)).prod
    (nativeGpreProvenanceBoundaryPencil.valueTrace.comp
      (LinearMap.snd ℂ CarryVerticalL2 NativeGpreComplexEdgeCore)))

/-- Traco de fluxo do produto livre. -/
def nativeGpreTfvdProductFluxTrace (q : ℝ) :
    NativeGpreTfvdProductState →ₗ[ℂ] NativeGpreTfvdProductBoundary :=
  (((carryWeightedVerticalBoundaryPencil q).fluxTrace.comp
      (LinearMap.fst ℂ CarryVerticalL2 NativeGpreComplexEdgeCore)).prod
    (nativeGpreProvenanceBoundaryPencil.fluxTrace.comp
      (LinearMap.snd ℂ CarryVerticalL2 NativeGpreComplexEdgeCore)))

/-- Pencil de produto anterior a qualquer identificacao entre as duas pernas. -/
def nativeGpreTfvdProductBoundaryPencil (q : ℝ) :
    LinearBoundaryPencil
      NativeGpreTfvdProductState NativeGpreTfvdProductBoundary where
  valueTrace := nativeGpreTfvdProductValueTrace q
  fluxTrace := nativeGpreTfvdProductFluxTrace q

@[simp] theorem nativeGpreTfvdProductBoundaryPencil_valueTrace_apply
    (q : ℝ) (state : NativeGpreTfvdProductState) :
    (nativeGpreTfvdProductBoundaryPencil q).valueTrace state =
      ((carryWeightedVerticalBoundaryPencil q).valueTrace state.1,
        nativeGpreBoundaryValueLift state.2) := by
  rfl

@[simp] theorem nativeGpreTfvdProductBoundaryPencil_fluxTrace_apply
    (q : ℝ) (state : NativeGpreTfvdProductState) :
    (nativeGpreTfvdProductBoundaryPencil q).fluxTrace state =
      ((carryWeightedVerticalBoundaryPencil q).fluxTrace state.1,
        nativeGpreBoundaryNumberFluxLift state.2) := by
  rfl

/-- A projecao escalar do operador de produto e o operador TFVD livre. -/
@[simp] theorem nativeGpreTfvdProductBoundaryPencil_operator_fst
    (q : ℝ) (lambda : ℂ) (state : NativeGpreTfvdProductState) :
    (nativeGpreTfvdProductBoundaryPencil q).operator lambda state |>.1 =
      (carryWeightedVerticalBoundaryPencil q).operator lambda state.1 := by
  rfl

/-- A projecao de proveniencia e o operador do pencil `G_pre`. -/
@[simp] theorem nativeGpreTfvdProductBoundaryPencil_operator_snd
    (q : ℝ) (lambda : ℂ) (state : NativeGpreTfvdProductState) :
    (nativeGpreTfvdProductBoundaryPencil q).operator lambda state |>.2 =
      nativeGpreProvenanceBoundaryPencil.operator lambda state.2 := by
  rfl

/-- A relacao de produto projeta a uma relacao vertical livre. -/
theorem nativeGpreTfvdProductRelation_vertical_projection
    (q : ℝ) {boundary : NativeGpreTfvdProductBoundary ×
      NativeGpreTfvdProductBoundary}
    (hboundary : boundary ∈ (nativeGpreTfvdProductBoundaryPencil q).relation) :
    (boundary.1.1, boundary.2.1) ∈
      (carryWeightedVerticalBoundaryPencil q).relation := by
  change boundary ∈ LinearMap.range
    ((nativeGpreTfvdProductBoundaryPencil q).valueTrace.prod
      (nativeGpreTfvdProductBoundaryPencil q).fluxTrace) at hboundary
  rcases hboundary with ⟨state, rfl⟩
  change
    ((carryWeightedVerticalBoundaryPencil q).valueTrace state.1,
      (carryWeightedVerticalBoundaryPencil q).fluxTrace state.1) ∈
        LinearMap.range
          ((carryWeightedVerticalBoundaryPencil q).valueTrace.prod
            (carryWeightedVerticalBoundaryPencil q).fluxTrace)
  exact ⟨state.1, rfl⟩

/-- A mesma relacao projeta a relacao aritmetica `G_pre`. -/
theorem nativeGpreTfvdProductRelation_provenance_projection
    (q : ℝ) {boundary : NativeGpreTfvdProductBoundary ×
      NativeGpreTfvdProductBoundary}
    (hboundary : boundary ∈ (nativeGpreTfvdProductBoundaryPencil q).relation) :
    (boundary.1.2, boundary.2.2) ∈
      nativeGpreProvenanceBoundaryPencil.relation := by
  change boundary ∈ LinearMap.range
    ((nativeGpreTfvdProductBoundaryPencil q).valueTrace.prod
      (nativeGpreTfvdProductBoundaryPencil q).fluxTrace) at hboundary
  rcases hboundary with ⟨state, rfl⟩
  change
    (nativeGpreBoundaryValueLift state.2,
      nativeGpreBoundaryNumberFluxLift state.2) ∈
        LinearMap.range
          (nativeGpreBoundaryValueLift.prod nativeGpreBoundaryNumberFluxLift)
  exact ⟨state.2, rfl⟩

/-- Uma coordenada de proveniencia ativa continua impondo `lambda=j` no
pencil de produto. -/
theorem nativeGpreTfvdProduct_operator_eq_zero_forces_level
    (q : ℝ) (lambda : ℂ) (state : NativeGpreTfvdProductState)
    (hzero : (nativeGpreTfvdProductBoundaryPencil q).operator lambda state = 0)
    (c : NativeGpreBoundaryContext)
    (hactive : nativeGpreBoundaryValueLift state.2 c ≠ 0) :
    lambda = (c.towerLevel.val : ℂ) := by
  have hsnd := congrArg Prod.snd hzero
  have hgpre : nativeGpreProvenanceBoundaryPencil.operator lambda state.2 = 0 := by
    simpa using hsnd
  exact nativeGpreProvenanceBoundaryPencil_operator_eq_zero_forces_level
    lambda state.2 hgpre c hactive

/-- Uma realizacao vertical do core de arestas produz a colagem diagonal:
o mesmo vetor alimenta a perna vertical e a perna de proveniencia. -/
def nativeGpreTfvdSameEdgeGlue
    (verticalRealization : NativeGpreComplexEdgeCore →ₗ[ℂ] CarryVerticalL2) :
    NativeGpreComplexEdgeCore →ₗ[ℂ] NativeGpreTfvdProductState :=
  verticalRealization.prod LinearMap.id

@[simp] theorem nativeGpreTfvdSameEdgeGlue_apply
    (verticalRealization : NativeGpreComplexEdgeCore →ₗ[ℂ] CarryVerticalL2)
    (x : NativeGpreComplexEdgeCore) :
    nativeGpreTfvdSameEdgeGlue verticalRealization x =
      (verticalRealization x, x) := rfl

/-- Pencil efetivamente colado por uma realizacao vertical comum. -/
def nativeGpreTfvdGluedBoundaryPencil
    (q : ℝ)
    (verticalRealization : NativeGpreComplexEdgeCore →ₗ[ℂ] CarryVerticalL2) :
    LinearBoundaryPencil NativeGpreComplexEdgeCore
      NativeGpreTfvdProductBoundary :=
  (nativeGpreTfvdProductBoundaryPencil q).pullback
    (nativeGpreTfvdSameEdgeGlue verticalRealization)

/-- Toda relacao colada fica contida na relacao de produto anterior. -/
theorem nativeGpreTfvdGluedBoundaryRelation_le_product
    (q : ℝ)
    (verticalRealization : NativeGpreComplexEdgeCore →ₗ[ℂ] CarryVerticalL2) :
    (nativeGpreTfvdGluedBoundaryPencil q verticalRealization).relation ≤
      (nativeGpreTfvdProductBoundaryPencil q).relation :=
  LinearBoundaryPencil.pullback_relation_le _ _

/-- O fechamento de um pencil colado, em qualquer realizacao vertical, ainda
forca o nivel de toda coordenada `G_pre` ativa. -/
theorem nativeGpreTfvdGlued_operator_eq_zero_forces_level
    (q : ℝ)
    (verticalRealization : NativeGpreComplexEdgeCore →ₗ[ℂ] CarryVerticalL2)
    (lambda : ℂ) (x : NativeGpreComplexEdgeCore)
    (hzero :
      (nativeGpreTfvdGluedBoundaryPencil q verticalRealization).operator
        lambda x = 0)
    (c : NativeGpreBoundaryContext)
    (hactive : nativeGpreBoundaryValueLift x c ≠ 0) :
    lambda = (c.towerLevel.val : ℂ) := by
  have hproduct :
      (nativeGpreTfvdProductBoundaryPencil q).operator lambda
        (nativeGpreTfvdSameEdgeGlue verticalRealization x) = 0 := by
    simpa [nativeGpreTfvdGluedBoundaryPencil] using hzero
  exact nativeGpreTfvdProduct_operator_eq_zero_forces_level
    q lambda (nativeGpreTfvdSameEdgeGlue verticalRealization x)
    hproduct c (by simpa using hactive)

end

end CPFormal.Analytic.Cp
