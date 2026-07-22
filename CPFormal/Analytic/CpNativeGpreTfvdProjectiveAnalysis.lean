import CPFormal.Analytic.CpNativeGpreTfvdAnalysis
import CPFormal.Analytic.CpNativeGpreTfvdCutoffCompatibility
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Limite projetivo da analise TFVD--G_pre em atlas finitos

Cada atlas finito de proveniencia `S` ja possui uma analise continua

`Analysis_(q,S) : ell^2 -> ((bracket, trace), (value, numberFlux))`

com left inverse TFVD continuo. Este modulo organiza simultaneamente todos os
atlases finitos no produto dependente e prova que o mapa diagonal de analise
continua possuindo um left inverse continuo, obtido pela componente do atlas
vazio. Consequentemente, seu range projetivo e fechado.

A construcao usa a topologia produto. Ela nao declara ainda um unico carrier
Hilbertiano com majorante uniforme `128`; esse passo continua separado e exige
o certificado aritmetico global do lift `G_pre`.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Restricao continua do carrier de proveniencia de um atlas maior a um menor. -/
noncomputable def nativeGpreFiniteBoundaryContinuousRestrictionOfSubset
    {S T : Finset NativeGpreBoundaryContext} (hST : S ⊆ T) :
    NativeGpreFiniteBoundaryCarrier T →L[ℂ]
      NativeGpreFiniteBoundaryCarrier S where
  toLinearMap := nativeGpreFiniteBoundaryRestrictionOfSubset hST
  cont := LinearMap.continuous_of_finiteDimensional _

@[simp] theorem nativeGpreFiniteBoundaryContinuousRestrictionOfSubset_apply
    {S T : Finset NativeGpreBoundaryContext} (hST : S ⊆ T)
    (y : NativeGpreFiniteBoundaryCarrier T) (c : ↥S) :
    nativeGpreFiniteBoundaryContinuousRestrictionOfSubset hST y c =
      y (nativeGpreFiniteContextEmbedding hST c) := rfl

/-- Restricao simultanea dos dois papeis de proveniencia. -/
noncomputable def nativeGpreFiniteTfvdProvenanceRestriction
    {S T : Finset NativeGpreBoundaryContext} (hST : S ⊆ T) :
    NativeGpreFiniteTfvdProvenanceCarrier T →L[ℂ]
      NativeGpreFiniteTfvdProvenanceCarrier S :=
  (nativeGpreFiniteBoundaryContinuousRestrictionOfSubset hST).prodMap
    (nativeGpreFiniteBoundaryContinuousRestrictionOfSubset hST)

/-- Restricao do carrier completo de analise. A perna TFVD permanece literal;
somente os contextos de proveniencia fora de `S` sao esquecidos. -/
noncomputable def nativeGpreFiniteTfvdAnalysisRestriction
    {S T : Finset NativeGpreBoundaryContext} (hST : S ⊆ T) :
    NativeGpreFiniteTfvdAnalysisCarrier T →L[ℂ]
      NativeGpreFiniteTfvdAnalysisCarrier S :=
  (ContinuousLinearMap.id ℂ (CarryVerticalL2 × (ℂ × ℂ))).prodMap
    (nativeGpreFiniteTfvdProvenanceRestriction hST)

@[simp] theorem nativeGpreFiniteTfvdAnalysisRestriction_apply
    {S T : Finset NativeGpreBoundaryContext} (hST : S ⊆ T)
    (data : NativeGpreFiniteTfvdAnalysisCarrier T) :
    nativeGpreFiniteTfvdAnalysisRestriction hST data =
      (data.1,
        (nativeGpreFiniteBoundaryContinuousRestrictionOfSubset hST data.2.1,
          nativeGpreFiniteBoundaryContinuousRestrictionOfSubset hST data.2.2)) := rfl

/-- A analise enriquecida comuta exatamente com a restricao de atlas. -/
theorem nativeGpreFiniteTfvdAnalysis_restrict
    (q : ℝ) {S T : Finset NativeGpreBoundaryContext} (hST : S ⊆ T)
    (x : CarryVerticalL2) :
    nativeGpreFiniteTfvdAnalysisRestriction hST
        (nativeGpreFiniteTfvdAnalysis q T x) =
      nativeGpreFiniteTfvdAnalysis q S x := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext c
      rfl
    · funext c
      rfl

/-- Produto dependente de todos os carriers de analise em atlas finitos. -/
abbrev NativeGpreTfvdProjectiveAnalysisCarrier :=
  (S : Finset NativeGpreBoundaryContext) →
    NativeGpreFiniteTfvdAnalysisCarrier S

/-- Familia diagonal de todas as analises finitas. -/
noncomputable def nativeGpreTfvdProjectiveAnalysis (q : ℝ) :
    CarryVerticalL2 →L[ℂ] NativeGpreTfvdProjectiveAnalysisCarrier :=
  ContinuousLinearMap.pi fun S => nativeGpreFiniteTfvdAnalysis q S

@[simp] theorem nativeGpreTfvdProjectiveAnalysis_apply
    (q : ℝ) (x : CarryVerticalL2)
    (S : Finset NativeGpreBoundaryContext) :
    nativeGpreTfvdProjectiveAnalysis q x S =
      nativeGpreFiniteTfvdAnalysis q S x := rfl

/-- Compatibilidade projetiva de uma familia de dados enriquecidos. -/
def NativeGpreTfvdProjectiveCompatible
    (data : NativeGpreTfvdProjectiveAnalysisCarrier) : Prop :=
  ∀ {S T : Finset NativeGpreBoundaryContext} (hST : S ⊆ T),
    nativeGpreFiniteTfvdAnalysisRestriction hST (data T) = data S

/-- Toda familia produzida por um unico estado vertical e projetivamente
compativel. -/
theorem nativeGpreTfvdProjectiveAnalysis_compatible
    (q : ℝ) (x : CarryVerticalL2) :
    NativeGpreTfvdProjectiveCompatible
      (nativeGpreTfvdProjectiveAnalysis q x) := by
  intro S T hST
  exact nativeGpreFiniteTfvdAnalysis_restrict q hST x

/-- Reconstrucao projetiva: basta a componente do atlas vazio, pois ela ja
contem bracket e traco TFVD completos. -/
noncomputable def nativeGpreTfvdProjectiveReconstruction
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    NativeGpreTfvdProjectiveAnalysisCarrier →L[ℂ] CarryVerticalL2 :=
  (nativeGpreFiniteTfvdReconstruction q hq0 hq1
      (∅ : Finset NativeGpreBoundaryContext)).comp
    (ContinuousLinearMap.proj
      (R := ℂ)
      (φ := fun S : Finset NativeGpreBoundaryContext =>
        NativeGpreFiniteTfvdAnalysisCarrier S)
      (∅ : Finset NativeGpreBoundaryContext))

@[simp] theorem nativeGpreTfvdProjectiveReconstruction_apply
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (data : NativeGpreTfvdProjectiveAnalysisCarrier) :
    nativeGpreTfvdProjectiveReconstruction q hq0 hq1 data =
      nativeGpreFiniteTfvdReconstruction q hq0 hq1
        (∅ : Finset NativeGpreBoundaryContext)
        (data (∅ : Finset NativeGpreBoundaryContext)) := rfl

/-- O left inverse TFVD sobrevive ao produto de todos os cutoffs. -/
@[simp] theorem nativeGpreTfvdProjectiveReconstruction_analysis
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (x : CarryVerticalL2) :
    nativeGpreTfvdProjectiveReconstruction q hqpos.le hq1
        (nativeGpreTfvdProjectiveAnalysis q x) = x := by
  exact nativeGpreFiniteTfvdReconstruction_analysis q hqpos hq1
    (∅ : Finset NativeGpreBoundaryContext) x

/-- A analise projetiva possui left inverse continuo. -/
theorem nativeGpreTfvdProjectiveAnalysis_hasLeftInverse
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    (nativeGpreTfvdProjectiveAnalysis q).HasLeftInverse := by
  refine ⟨nativeGpreTfvdProjectiveReconstruction q hqpos.le hq1, ?_⟩
  intro x
  exact nativeGpreTfvdProjectiveReconstruction_analysis q hqpos hq1 x

/-- O mapa simultaneo de todos os atlas finitos nao apaga o estado vertical. -/
theorem nativeGpreTfvdProjectiveAnalysis_injective
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    Function.Injective (nativeGpreTfvdProjectiveAnalysis q) :=
  (nativeGpreTfvdProjectiveAnalysis_hasLeftInverse q hqpos hq1).injective

/-- Resultado topologico central: o range da analise sobre todos os atlas
finitos e fechado na topologia produto. -/
theorem nativeGpreTfvdProjectiveAnalysis_range_isClosed
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    IsClosed
      (LinearMap.range (nativeGpreTfvdProjectiveAnalysis q).toLinearMap :
        Set NativeGpreTfvdProjectiveAnalysisCarrier) :=
  (nativeGpreTfvdProjectiveAnalysis_hasLeftInverse q hqpos hq1).isClosed_range

end

end CPFormal.Analytic.Cp