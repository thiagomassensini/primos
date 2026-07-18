import CPFormal.Carry.C2WeightedReindex

/-!
# Caixas aritmeticas C2 perfeitamente alinhadas

Para `M` centros, a caixa bracketada usa os centros

`4, 8, ..., 4 * M`

e guarda as duas pernas de cada centro. A bijecao C2 transporta essa caixa
para uma caixa finita de pernas impares. Neste recorte induzido nao existe
bordo: nenhuma incidencia sobra e nenhuma falta.

Nao ha limite, serie infinita, zeta ou zero neste arquivo.
-/

open scoped BigOperators

namespace CPFormal.Carry.C2

/-- Incidencia da perna esquerda do centro `4 * (k + 1)`. -/
def leftIncidence (k : ℕ) : Incidence := by
  refine ⟨(4 * (k + 1), 4 * (k + 1) - 1), ?_⟩
  constructor
  · omega
  constructor
  · exact ⟨k + 1, rfl⟩
  · exact Or.inl rfl

/-- Incidencia da perna direita do centro `4 * (k + 1)`. -/
def rightIncidence (k : ℕ) : Incidence := by
  refine ⟨(4 * (k + 1), 4 * (k + 1) + 1), ?_⟩
  constructor
  · omega
  constructor
  · exact ⟨k + 1, rfl⟩
  · exact Or.inr rfl

/-- Indices diferentes produzem incidencias esquerdas diferentes. -/
def leftIncidenceEmbedding : ℕ ↪ Incidence where
  toFun := leftIncidence
  inj' := by
    intro a b h
    have hc : 4 * (a + 1) = 4 * (b + 1) :=
      congrArg (fun x : Incidence => x.1.1) h
    omega

/-- Indices diferentes produzem incidencias direitas diferentes. -/
def rightIncidenceEmbedding : ℕ ↪ Incidence where
  toFun := rightIncidence
  inj' := by
    intro a b h
    have hc : 4 * (a + 1) = 4 * (b + 1) :=
      congrArg (fun x : Incidence => x.1.1) h
    omega

/-- As duas incidencias de cada um dos primeiros `M` centros C2. -/
noncomputable def alignedIncidenceBox (M : ℕ) : Finset Incidence := by
  classical
  exact
    (Finset.range M).map leftIncidenceEmbedding ∪
      (Finset.range M).map rightIncidenceEmbedding

/-- A caixa de pernas que corresponde exatamente a caixa de incidencias. -/
noncomputable def alignedOddLegBox (M : ℕ) : Finset OddLeg := by
  classical
  exact
    (alignedIncidenceBox M).map oddLegEquivIncidence.symm.toEmbedding

/-- Aplicar a bijecao de volta recupera literalmente a caixa bracketada. -/
theorem incidenceImage_alignedOddLegBox (M : ℕ) :
    incidenceImage (alignedOddLegBox M) = alignedIncidenceBox M := by
  classical
  ext x
  simp [incidenceImage, alignedOddLegBox]

/-- A caixa alinhada nao possui incidencias extras. -/
@[simp] theorem extraIncidences_alignedBox (M : ℕ) :
    extraIncidences (alignedOddLegBox M) (alignedIncidenceBox M) = ∅ := by
  classical
  simp [extraIncidences, incidenceImage_alignedOddLegBox]

/-- A caixa alinhada nao possui incidencias faltantes. -/
@[simp] theorem missingIncidences_alignedBox (M : ℕ) :
    missingIncidences (alignedOddLegBox M) (alignedIncidenceBox M) = ∅ := by
  classical
  simp [missingIncidences, incidenceImage_alignedOddLegBox]

/--
Reindexacao ponderada exata para os centros `4, 8, ..., 4 * M` e suas pernas.
-/
theorem weighted_reindex_alignedBox
    {R : Type*} [CommRing R]
    (M : ℕ) (depthWeight : ℕ → R) (value : ℕ → R) :
    (∑ n ∈ alignedOddLegBox M, oddLegTerm depthWeight value n) =
      ∑ x ∈ alignedIncidenceBox M, incidenceTerm depthWeight value x := by
  apply weighted_reindex_of_exact_cover
  exact incidenceImage_alignedOddLegBox M

end CPFormal.Carry.C2
