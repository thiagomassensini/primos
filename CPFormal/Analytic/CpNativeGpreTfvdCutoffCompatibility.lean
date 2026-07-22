import CPFormal.Analytic.CpNativeGpreTfvdFiniteClosedRelation

/-!
# Compatibilidade dos cutoffs da relacao TFVD--G_pre

Cada atlas finito de proveniencia ja produz uma relacao fechada. Este modulo
prova que essas relacoes pertencem a um unico sistema projetivo.

Se `S ⊆ T`, existe uma restricao linear canonica

`C x C^T -> C x C^S`

que preserva a coordenada TFVD e esquece somente os contextos de proveniencia
fora de `S`. O kernel verifica que essa restricao comuta com os dois tracos,
com o operador do pencil e com a relacao valor--fluxo.

Consequentemente, um fechamento em um atlas maior restringe-se a um fechamento
em todo atlas menor. Nenhuma soma sobre contextos e executada e nenhum eixo e
identificado durante a passagem de cutoff.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Inclusao de subtipos induzida por uma inclusao de finsets. -/
def nativeGpreFiniteContextEmbedding
    {S T : Finset NativeGpreBoundaryContext} (hST : S ⊆ T) :
    ↥S ↪ ↥T where
  toFun c := ⟨c.1, hST c.2⟩
  inj' c d h := by
    apply Subtype.ext
    exact congrArg (fun z : ↥T => z.1) h

@[simp] theorem nativeGpreFiniteContextEmbedding_val
    {S T : Finset NativeGpreBoundaryContext} (hST : S ⊆ T)
    (c : ↥S) :
    (nativeGpreFiniteContextEmbedding hST c).1 = c.1 := rfl

/-- Restricao de funcoes de proveniencia de um atlas maior a um menor. -/
def nativeGpreFiniteBoundaryRestrictionOfSubset
    {S T : Finset NativeGpreBoundaryContext} (hST : S ⊆ T) :
    NativeGpreFiniteBoundaryCarrier T →ₗ[ℂ]
      NativeGpreFiniteBoundaryCarrier S where
  toFun y c := y (nativeGpreFiniteContextEmbedding hST c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem nativeGpreFiniteBoundaryRestrictionOfSubset_apply
    {S T : Finset NativeGpreBoundaryContext} (hST : S ⊆ T)
    (y : NativeGpreFiniteBoundaryCarrier T) (c : ↥S) :
    nativeGpreFiniteBoundaryRestrictionOfSubset hST y c =
      y (nativeGpreFiniteContextEmbedding hST c) := rfl

/-- Restricao do bordo enriquecido inteiro. -/
def nativeGpreFiniteTfvdBoundaryRestriction
    {S T : Finset NativeGpreBoundaryContext} (hST : S ⊆ T) :
    NativeGpreFiniteTfvdBoundary T →ₗ[ℂ]
      NativeGpreFiniteTfvdBoundary S where
  toFun boundary :=
    (boundary.1,
      nativeGpreFiniteBoundaryRestrictionOfSubset hST boundary.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem nativeGpreFiniteTfvdBoundaryRestriction_apply
    {S T : Finset NativeGpreBoundaryContext} (hST : S ⊆ T)
    (boundary : NativeGpreFiniteTfvdBoundary T) :
    nativeGpreFiniteTfvdBoundaryRestriction hST boundary =
      (boundary.1,
        nativeGpreFiniteBoundaryRestrictionOfSubset hST boundary.2) := rfl

/-- A restricao comuta com o traco de valor aritmetico. -/
theorem nativeGpreFiniteBoundaryValueLift_restrict
    {S T : Finset NativeGpreBoundaryContext} (hST : S ⊆ T)
    (x : NativeGpreComplexEdgeCore) :
    nativeGpreFiniteBoundaryRestrictionOfSubset hST
        (nativeGpreFiniteBoundaryValueLift T x) =
      nativeGpreFiniteBoundaryValueLift S x := by
  funext c
  rfl

/-- A restricao comuta com o traco de fluxo aritmetico. -/
theorem nativeGpreFiniteBoundaryNumberFluxLift_restrict
    {S T : Finset NativeGpreBoundaryContext} (hST : S ⊆ T)
    (x : NativeGpreComplexEdgeCore) :
    nativeGpreFiniteBoundaryRestrictionOfSubset hST
        (nativeGpreFiniteBoundaryNumberFluxLift T x) =
      nativeGpreFiniteBoundaryNumberFluxLift S x := by
  funext c
  rfl

/-- A restricao comuta com o traco de valor enriquecido completo. -/
theorem nativeGpreFiniteCanonicalTfvdValueTrace_restrict
    (q : ℝ) {S T : Finset NativeGpreBoundaryContext} (hST : S ⊆ T)
    (x : NativeGpreComplexEdgeCore) :
    nativeGpreFiniteTfvdBoundaryRestriction hST
        ((nativeGpreFiniteCanonicalTfvdBoundaryPencil q T).valueTrace x) =
      (nativeGpreFiniteCanonicalTfvdBoundaryPencil q S).valueTrace x := by
  apply Prod.ext
  · rfl
  · exact nativeGpreFiniteBoundaryValueLift_restrict hST x

/-- A restricao comuta com o traco de fluxo enriquecido completo. -/
theorem nativeGpreFiniteCanonicalTfvdFluxTrace_restrict
    (q : ℝ) {S T : Finset NativeGpreBoundaryContext} (hST : S ⊆ T)
    (x : NativeGpreComplexEdgeCore) :
    nativeGpreFiniteTfvdBoundaryRestriction hST
        ((nativeGpreFiniteCanonicalTfvdBoundaryPencil q T).fluxTrace x) =
      (nativeGpreFiniteCanonicalTfvdBoundaryPencil q S).fluxTrace x := by
  apply Prod.ext
  · rfl
  · exact nativeGpreFiniteBoundaryNumberFluxLift_restrict hST x

/-- Compatibilidade exata do operador do pencil entre cutoffs. -/
theorem nativeGpreFiniteCanonicalTfvdOperator_restrict
    (q : ℝ) {S T : Finset NativeGpreBoundaryContext} (hST : S ⊆ T)
    (lambda : ℂ) (x : NativeGpreComplexEdgeCore) :
    nativeGpreFiniteTfvdBoundaryRestriction hST
        ((nativeGpreFiniteCanonicalTfvdBoundaryPencil q T).operator lambda x) =
      (nativeGpreFiniteCanonicalTfvdBoundaryPencil q S).operator lambda x := by
  change
    nativeGpreFiniteTfvdBoundaryRestriction hST
      ((nativeGpreFiniteCanonicalTfvdBoundaryPencil q T).fluxTrace x -
        lambda •
          (nativeGpreFiniteCanonicalTfvdBoundaryPencil q T).valueTrace x) = _
  rw [map_sub, map_smul,
    nativeGpreFiniteCanonicalTfvdFluxTrace_restrict q hST x,
    nativeGpreFiniteCanonicalTfvdValueTrace_restrict q hST x]
  rfl

/-- Um zero do pencil em `T` permanece zero depois de restringir a `S`. -/
theorem nativeGpreFiniteCanonicalTfvdOperator_zero_mono
    (q : ℝ) {S T : Finset NativeGpreBoundaryContext} (hST : S ⊆ T)
    (lambda : ℂ) (x : NativeGpreComplexEdgeCore)
    (hzero :
      (nativeGpreFiniteCanonicalTfvdBoundaryPencil q T).operator lambda x = 0) :
    (nativeGpreFiniteCanonicalTfvdBoundaryPencil q S).operator lambda x = 0 := by
  rw [← nativeGpreFiniteCanonicalTfvdOperator_restrict q hST lambda x]
  rw [hzero, map_zero]

/-- Restricao simultanea dos lados valor e fluxo. -/
def nativeGpreFiniteTfvdRelationRestriction
    {S T : Finset NativeGpreBoundaryContext} (hST : S ⊆ T) :
    (NativeGpreFiniteTfvdBoundary T × NativeGpreFiniteTfvdBoundary T) →ₗ[ℂ]
      (NativeGpreFiniteTfvdBoundary S × NativeGpreFiniteTfvdBoundary S) where
  toFun boundary :=
    (nativeGpreFiniteTfvdBoundaryRestriction hST boundary.1,
      nativeGpreFiniteTfvdBoundaryRestriction hST boundary.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem nativeGpreFiniteTfvdRelationRestriction_apply
    {S T : Finset NativeGpreBoundaryContext} (hST : S ⊆ T)
    (boundary : NativeGpreFiniteTfvdBoundary T ×
      NativeGpreFiniteTfvdBoundary T) :
    nativeGpreFiniteTfvdRelationRestriction hST boundary =
      (nativeGpreFiniteTfvdBoundaryRestriction hST boundary.1,
        nativeGpreFiniteTfvdBoundaryRestriction hST boundary.2) := rfl

/-- A relacao de um cutoff maior projeta exatamente a uma relacao do cutoff
menor. -/
theorem nativeGpreFiniteCanonicalTfvdRelation_restrict
    (q : ℝ) {S T : Finset NativeGpreBoundaryContext} (hST : S ⊆ T)
    {boundary : NativeGpreFiniteTfvdBoundary T ×
      NativeGpreFiniteTfvdBoundary T}
    (hboundary : boundary ∈
      (nativeGpreFiniteCanonicalTfvdBoundaryPencil q T).relation) :
    nativeGpreFiniteTfvdRelationRestriction hST boundary ∈
      (nativeGpreFiniteCanonicalTfvdBoundaryPencil q S).relation := by
  change boundary ∈ LinearMap.range
    ((nativeGpreFiniteCanonicalTfvdBoundaryPencil q T).valueTrace.prod
      (nativeGpreFiniteCanonicalTfvdBoundaryPencil q T).fluxTrace) at hboundary
  rcases hboundary with ⟨x, rfl⟩
  change
    (nativeGpreFiniteTfvdBoundaryRestriction hST
        ((nativeGpreFiniteCanonicalTfvdBoundaryPencil q T).valueTrace x),
      nativeGpreFiniteTfvdBoundaryRestriction hST
        ((nativeGpreFiniteCanonicalTfvdBoundaryPencil q T).fluxTrace x)) ∈
      LinearMap.range
        ((nativeGpreFiniteCanonicalTfvdBoundaryPencil q S).valueTrace.prod
          (nativeGpreFiniteCanonicalTfvdBoundaryPencil q S).fluxTrace)
  rw [nativeGpreFiniteCanonicalTfvdValueTrace_restrict q hST x,
    nativeGpreFiniteCanonicalTfvdFluxTrace_restrict q hST x]
  exact ⟨x, rfl⟩

/-- A restricao de um atlas para ele mesmo e a identidade. -/
theorem nativeGpreFiniteTfvdBoundaryRestriction_refl
    (S : Finset NativeGpreBoundaryContext) :
    nativeGpreFiniteTfvdBoundaryRestriction (show S ⊆ S from fun _ h => h) =
      LinearMap.id := by
  apply LinearMap.ext
  intro boundary
  apply Prod.ext
  · rfl
  · funext c
    rfl

end

end CPFormal.Analytic.Cp
