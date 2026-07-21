import CPFormal.Analytic.CpNativeGpreTfvdFiniteClosedRelation
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Analise TFVD enriquecida e range fechado em atlas finito

Este modulo acrescenta o bracket ao par valor--fluxo ja colado com a
proveniencia `G_pre`. Para um atlas finito `S`, o estado vertical completo e
analisado como

`x |-> ((B_q x, Tr_q x), (Gpre_0 x, Gpre_1 x))`.

Os dois ultimos termos preservam os papeis `value` e `numberFlux` em todas as
coordenadas de `S`. Como `S` e finito, cada coordenada do lift nativo se estende
continuamente do core finitamente suportado a `ell^2` pela avaliacao da mesma
celula.

A reconstrucao ignora somente a proveniencia e aplica o TFVD ja provado:

`Rec_q(g, b, pi) = G_q g + R_q b`.

O kernel prova `Rec_q comp Analysis_q,S = I`. Consequentemente, o mapa de
analise e injetivo e seu range e o conjunto de pontos fixos de uma projecao
continua; em particular, esse range e fechado. Nenhuma hipotese de zero,
identificacao `t=j` ou soma prematura dos eixos de proveniencia e usada.
-/

open scoped lp ENNReal NNReal

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Os dois papeis do lift nativo, ainda separados no atlas finito. -/
abbrev NativeGpreFiniteTfvdProvenanceCarrier
    (S : Finset NativeGpreBoundaryContext) :=
  NativeGpreFiniteBoundaryCarrier S × NativeGpreFiniteBoundaryCarrier S

/-- Carrier da analise completa: bracket, traco TFVD e proveniencia nos dois
papeis valor--fluxo. -/
abbrev NativeGpreFiniteTfvdAnalysisCarrier
    (S : Finset NativeGpreBoundaryContext) :=
  (CarryVerticalL2 × (ℂ × ℂ)) × NativeGpreFiniteTfvdProvenanceCarrier S

/-- Extensao continua, coordenada por coordenada, de um papel do lift nativo a
todo o Hilbert vertical. -/
noncomputable def nativeGpreFiniteContinuousBoundaryRoleLift
    (role : GpreGraphRole) (S : Finset NativeGpreBoundaryContext) :
    CarryVerticalL2 →L[ℂ] NativeGpreFiniteBoundaryCarrier S :=
  ContinuousLinearMap.pi fun c =>
    (nativeGpreTowerCoordinateCoefficient (c.1.withRole role) : ℂ) •
      carryVerticalL2Eval c.1.cell

@[simp] theorem nativeGpreFiniteContinuousBoundaryRoleLift_apply
    (role : GpreGraphRole) (S : Finset NativeGpreBoundaryContext)
    (x : CarryVerticalL2) (c : ↥S) :
    nativeGpreFiniteContinuousBoundaryRoleLift role S x c =
      x c.1.cell *
        (nativeGpreTowerCoordinateCoefficient (c.1.withRole role) : ℂ) := by
  change
    (nativeGpreTowerCoordinateCoefficient (c.1.withRole role) : ℂ) *
        x c.1.cell =
      x c.1.cell *
        (nativeGpreTowerCoordinateCoefficient (c.1.withRole role) : ℂ)
  ring

/-- Extensao continua do traco de valor de proveniencia. -/
noncomputable def nativeGpreFiniteContinuousBoundaryValueLift
    (S : Finset NativeGpreBoundaryContext) :
    CarryVerticalL2 →L[ℂ] NativeGpreFiniteBoundaryCarrier S :=
  nativeGpreFiniteContinuousBoundaryRoleLift .value S

/-- Extensao continua do traco de fluxo numero de proveniencia. -/
noncomputable def nativeGpreFiniteContinuousBoundaryNumberFluxLift
    (S : Finset NativeGpreBoundaryContext) :
    CarryVerticalL2 →L[ℂ] NativeGpreFiniteBoundaryCarrier S :=
  nativeGpreFiniteContinuousBoundaryRoleLift .numberFlux S

/-- No core canonico, a extensao continua de valor coincide literalmente com
o lift finito anterior. -/
@[simp] theorem nativeGpreFiniteContinuousBoundaryValueLift_canonical
    (S : Finset NativeGpreBoundaryContext)
    (x : NativeGpreComplexEdgeCore) (c : ↥S) :
    nativeGpreFiniteContinuousBoundaryValueLift S
        (nativeGpreCanonicalVerticalRealization x) c =
      nativeGpreFiniteBoundaryValueLift S x c := by
  change
    (nativeGpreTowerCoordinateCoefficient (c.1.withRole .value) : ℂ) *
        x c.1.cell =
      x c.1.cell *
        (nativeGpreTowerCoordinateCoefficient (c.1.withRole .value) : ℂ)
  ring

/-- A mesma compatibilidade para o papel de fluxo numero. -/
@[simp] theorem nativeGpreFiniteContinuousBoundaryNumberFluxLift_canonical
    (S : Finset NativeGpreBoundaryContext)
    (x : NativeGpreComplexEdgeCore) (c : ↥S) :
    nativeGpreFiniteContinuousBoundaryNumberFluxLift S
        (nativeGpreCanonicalVerticalRealization x) c =
      nativeGpreFiniteBoundaryNumberFluxLift S x c := by
  change
    (nativeGpreTowerCoordinateCoefficient
        (c.1.withRole .numberFlux) : ℂ) * x c.1.cell =
      x c.1.cell *
        (nativeGpreTowerCoordinateCoefficient
          (c.1.withRole .numberFlux) : ℂ)
  ring

/-- Mapa de analise enriquecido em `ell^2`: bracket e traco continuam nas
coordenadas TFVD, enquanto os dois papeis de `G_pre` permanecem resolvidos em
`S`. -/
noncomputable def nativeGpreFiniteTfvdAnalysis
    (q : ℝ) (S : Finset NativeGpreBoundaryContext) :
    CarryVerticalL2 →L[ℂ] NativeGpreFiniteTfvdAnalysisCarrier S :=
  ((carryWeightedVerticalCenteredBracket q).prod
      (carryWeightedVerticalTrace q)).prod
    ((nativeGpreFiniteContinuousBoundaryValueLift S).prod
      (nativeGpreFiniteContinuousBoundaryNumberFluxLift S))

@[simp] theorem nativeGpreFiniteTfvdAnalysis_apply
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (x : CarryVerticalL2) :
    nativeGpreFiniteTfvdAnalysis q S x =
      ((carryWeightedVerticalCenteredBracket q x,
          carryWeightedVerticalTrace q x),
        (nativeGpreFiniteContinuousBoundaryValueLift S x,
          nativeGpreFiniteContinuousBoundaryNumberFluxLift S x)) := rfl

/-- A analise do representante canonico recupera exatamente os tracos do
pencil finito ja construido. -/
theorem nativeGpreFiniteTfvdAnalysis_canonical
    (q : ℝ) (S : Finset NativeGpreBoundaryContext)
    (x : NativeGpreComplexEdgeCore) :
    nativeGpreFiniteTfvdAnalysis q S
        (nativeGpreCanonicalVerticalRealization x) =
      ((carryWeightedVerticalCenteredBracket q
          (nativeGpreCanonicalVerticalRealization x),
        carryWeightedVerticalTrace q
          (nativeGpreCanonicalVerticalRealization x)),
        (nativeGpreFiniteBoundaryValueLift S x,
          nativeGpreFiniteBoundaryNumberFluxLift S x)) := by
  rw [nativeGpreFiniteTfvdAnalysis_apply]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext c
      exact nativeGpreFiniteContinuousBoundaryValueLift_canonical S x c
    · funext c
      exact nativeGpreFiniteContinuousBoundaryNumberFluxLift_canonical S x c

/-- Projecao do carrier de analise para o par bracket--traco consumido pelo
TFVD. -/
def nativeGpreFiniteTfvdAnalysisTfvdProjection
    (S : Finset NativeGpreBoundaryContext) :
    NativeGpreFiniteTfvdAnalysisCarrier S →L[ℂ]
      (CarryVerticalL2 × (ℂ × ℂ)) :=
  ContinuousLinearMap.fst ℂ
    (CarryVerticalL2 × (ℂ × ℂ))
    (NativeGpreFiniteTfvdProvenanceCarrier S)

/-- Projecao para o bracket interior. -/
def nativeGpreFiniteTfvdAnalysisBracketProjection
    (S : Finset NativeGpreBoundaryContext) :
    NativeGpreFiniteTfvdAnalysisCarrier S →L[ℂ] CarryVerticalL2 :=
  (ContinuousLinearMap.fst ℂ CarryVerticalL2 (ℂ × ℂ)).comp
    (nativeGpreFiniteTfvdAnalysisTfvdProjection S)

/-- Projecao para o traco TFVD exterior. -/
def nativeGpreFiniteTfvdAnalysisTraceProjection
    (S : Finset NativeGpreBoundaryContext) :
    NativeGpreFiniteTfvdAnalysisCarrier S →L[ℂ] (ℂ × ℂ) :=
  (ContinuousLinearMap.snd ℂ CarryVerticalL2 (ℂ × ℂ)).comp
    (nativeGpreFiniteTfvdAnalysisTfvdProjection S)

/-- Left inverse continuo do mapa de analise. A proveniencia e preservada no
carrier, mas nao e usada como pseudoinversa do estado vertical. -/
noncomputable def nativeGpreFiniteTfvdReconstruction
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    NativeGpreFiniteTfvdAnalysisCarrier S →L[ℂ] CarryVerticalL2 :=
  (carryVerticalL2WeightedGreen q).comp
      (nativeGpreFiniteTfvdAnalysisBracketProjection S) +
    (carryWeightedVerticalReturn q hq0 hq1).comp
      (nativeGpreFiniteTfvdAnalysisTraceProjection S)

@[simp] theorem nativeGpreFiniteTfvdReconstruction_apply
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (data : NativeGpreFiniteTfvdAnalysisCarrier S) :
    nativeGpreFiniteTfvdReconstruction q hq0 hq1 S data =
      carryVerticalL2WeightedGreen q data.1.1 +
        carryWeightedVerticalReturn q hq0 hq1 data.1.2 := rfl

/-- O TFVD fornece um left inverse em todo `ell^2`, nao apenas no core
finitamente suportado. -/
@[simp] theorem nativeGpreFiniteTfvdReconstruction_analysis
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (x : CarryVerticalL2) :
    nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S
        (nativeGpreFiniteTfvdAnalysis q S x) = x := by
  change
    carryVerticalL2WeightedGreen q
          (carryWeightedVerticalCenteredBracket q x) +
        carryWeightedVerticalReturn q hqpos.le hq1
          (carryWeightedVerticalTrace q x) = x
  ext n
  exact carryWeightedVerticalTfvd_apply q hqpos hq1 x n

/-- Igualdade de operadores: `Rec_q,S comp Analysis_q,S = I`. -/
theorem nativeGpreFiniteTfvdReconstruction_comp_analysis
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S ∘L
        nativeGpreFiniteTfvdAnalysis q S =
      ContinuousLinearMap.id ℂ CarryVerticalL2 := by
  apply ContinuousLinearMap.ext
  intro x
  exact nativeGpreFiniteTfvdReconstruction_analysis q hqpos hq1 S x

/-- A analise enriquecida nao apaga estados verticais. -/
theorem nativeGpreFiniteTfvdAnalysis_injective
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    Function.Injective (nativeGpreFiniteTfvdAnalysis q S) := by
  intro x y hxy
  calc
    x = nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S
          (nativeGpreFiniteTfvdAnalysis q S x) :=
      (nativeGpreFiniteTfvdReconstruction_analysis q hqpos hq1 S x).symm
    _ = nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S
          (nativeGpreFiniteTfvdAnalysis q S y) :=
      congrArg
        (fun data =>
          nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S data)
        hxy
    _ = y :=
      nativeGpreFiniteTfvdReconstruction_analysis q hqpos hq1 S y

/-- Projecao continua sobre os dados compativeis com um estado vertical. -/
noncomputable def nativeGpreFiniteTfvdAnalysisProjection
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    NativeGpreFiniteTfvdAnalysisCarrier S →L[ℂ]
      NativeGpreFiniteTfvdAnalysisCarrier S :=
  (nativeGpreFiniteTfvdAnalysis q S).comp
    (nativeGpreFiniteTfvdReconstruction q hq0 hq1 S)

@[simp] theorem nativeGpreFiniteTfvdAnalysisProjection_apply
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (data : NativeGpreFiniteTfvdAnalysisCarrier S) :
    nativeGpreFiniteTfvdAnalysisProjection q hq0 hq1 S data =
      nativeGpreFiniteTfvdAnalysis q S
        (nativeGpreFiniteTfvdReconstruction q hq0 hq1 S data) := rfl

/-- A projecao de compatibilidade e idempotente. -/
theorem nativeGpreFiniteTfvdAnalysisProjection_idempotent
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    nativeGpreFiniteTfvdAnalysisProjection q hqpos.le hq1 S ∘L
        nativeGpreFiniteTfvdAnalysisProjection q hqpos.le hq1 S =
      nativeGpreFiniteTfvdAnalysisProjection q hqpos.le hq1 S := by
  apply ContinuousLinearMap.ext
  intro data
  change
    nativeGpreFiniteTfvdAnalysis q S
        (nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S
          (nativeGpreFiniteTfvdAnalysis q S
            (nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S data))) =
      nativeGpreFiniteTfvdAnalysis q S
        (nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S data)
  rw [nativeGpreFiniteTfvdReconstruction_analysis q hqpos hq1 S]

/-- O range da analise e exatamente o locus fixo da projecao continua. -/
theorem nativeGpreFiniteTfvdAnalysis_range_eq_eqLocus
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    (LinearMap.range (nativeGpreFiniteTfvdAnalysis q S).toLinearMap :
        Set (NativeGpreFiniteTfvdAnalysisCarrier S)) =
      (nativeGpreFiniteTfvdAnalysisProjection q hqpos.le hq1 S).eqLocus
        (ContinuousLinearMap.id ℂ
          (NativeGpreFiniteTfvdAnalysisCarrier S)) := by
  ext data
  constructor
  · rintro ⟨x, rfl⟩
    change
      nativeGpreFiniteTfvdAnalysis q S
          (nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S
            (nativeGpreFiniteTfvdAnalysis q S x)) =
        nativeGpreFiniteTfvdAnalysis q S x
    rw [nativeGpreFiniteTfvdReconstruction_analysis q hqpos hq1 S]
  · intro hfixed
    refine ⟨nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S data, ?_⟩
    change
      nativeGpreFiniteTfvdAnalysis q S
          (nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S data) = data
    exact hfixed

/-- O range enriquecido de todo atlas finito e fechado. A prova usa o left
inverse TFVD, nao finitude dimensional do dominio. -/
theorem nativeGpreFiniteTfvdAnalysis_range_isClosed
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    IsClosed
      (LinearMap.range (nativeGpreFiniteTfvdAnalysis q S).toLinearMap :
        Set (NativeGpreFiniteTfvdAnalysisCarrier S)) := by
  rw [nativeGpreFiniteTfvdAnalysis_range_eq_eqLocus q hqpos hq1 S]
  exact ContinuousLinearMap.isClosed_eqLocus _ _

/-- Como o carrier ambiente e completo, o range fechado tambem e completo. -/
theorem nativeGpreFiniteTfvdAnalysis_range_isComplete
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    IsComplete
      (LinearMap.range (nativeGpreFiniteTfvdAnalysis q S).toLinearMap :
        Set (NativeGpreFiniteTfvdAnalysisCarrier S)) :=
  (nativeGpreFiniteTfvdAnalysis_range_isClosed q hqpos hq1 S).isComplete

end

end CPFormal.Analytic.Cp
