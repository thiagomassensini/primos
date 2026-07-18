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

/-- A `k`-esima perna da lista aritmetica `3, 5, 7, ...`. -/
def arithmeticOddLeg (k : ℕ) : OddLeg := by
  refine ⟨2 * k + 3, by omega, ?_⟩
  exact ⟨k + 1, by omega⟩

/-- A enumeracao `k ↦ 2k+3` nao repete pernas. -/
def arithmeticOddLegEmbedding : ℕ ↪ OddLeg where
  toFun := arithmeticOddLeg
  inj' := by
    intro a b h
    have hv : 2 * a + 3 = 2 * b + 3 :=
      congrArg (fun n : OddLeg => n.1) h
    omega

/-- As primeiras `2M` pernas impares, isto e, `3, 5, ..., 4M+1`. -/
def arithmeticOddLegBox (M : ℕ) : Finset OddLeg :=
  (Finset.range (2 * M)).map arithmeticOddLegEmbedding

/-- Os indices pares da lista aritmetica sao pernas esquerdas. -/
theorem arithmeticOddLeg_even (k : ℕ) :
    arithmeticOddLeg (2 * k) =
      oddLegEquivIncidence.symm (leftIncidence k) := by
  apply Subtype.ext
  change 2 * (2 * k) + 3 = 4 * (k + 1) - 1
  omega

/-- Os indices impares da lista aritmetica sao pernas direitas. -/
theorem arithmeticOddLeg_odd (k : ℕ) :
    arithmeticOddLeg (2 * k + 1) =
      oddLegEquivIncidence.symm (rightIncidence k) := by
  apply Subtype.ext
  change 2 * (2 * k + 1) + 3 = 4 * (k + 1) + 1
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

/--
A caixa puxada pela bijecao e literalmente a lista `3, 5, ..., 4M+1`.
-/
theorem alignedOddLegBox_eq_arithmeticOddLegBox (M : ℕ) :
    alignedOddLegBox M = arithmeticOddLegBox M := by
  classical
  ext n
  constructor
  · intro hn
    rw [alignedOddLegBox] at hn
    rcases Finset.mem_map.mp hn with ⟨x, hx, hxn⟩
    rw [alignedIncidenceBox] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_map.mp hx with ⟨k, hk, hkx⟩
      have hklt : k < M := Finset.mem_range.mp hk
      subst x
      subst n
      rw [← arithmeticOddLeg_even]
      exact Finset.mem_map.mpr
        ⟨2 * k, Finset.mem_range.mpr (by omega), rfl⟩
    · rcases Finset.mem_map.mp hx with ⟨k, hk, hkx⟩
      subst x
      subst n
      rw [← arithmeticOddLeg_odd]
      have hklt : k < M := Finset.mem_range.mp hk
      exact Finset.mem_map.mpr
        ⟨2 * k + 1, Finset.mem_range.mpr (by omega), rfl⟩
  · intro hn
    rw [arithmeticOddLegBox] at hn
    rcases Finset.mem_map.mp hn with ⟨k, hk, hkn⟩
    subst n
    have hklt : k < 2 * M := Finset.mem_range.mp hk
    have hmodlt : k % 2 < 2 := Nat.mod_lt k (by omega)
    have hdecomp := Nat.mod_add_div k 2
    have hcases : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases hcases with hzero | hone
    · have hkform : k = 2 * (k / 2) := by omega
      have hhalf : k / 2 < M := by omega
      rw [hkform, arithmeticOddLeg_even, alignedOddLegBox]
      apply Finset.mem_map.mpr
      refine ⟨leftIncidence (k / 2), ?_, rfl⟩
      rw [alignedIncidenceBox]
      apply Finset.mem_union_left
      exact Finset.mem_map.mpr
        ⟨k / 2, Finset.mem_range.mpr hhalf, rfl⟩
    · have hkform : k = 2 * (k / 2) + 1 := by omega
      have hhalf : k / 2 < M := by omega
      rw [hkform, arithmeticOddLeg_odd, alignedOddLegBox]
      apply Finset.mem_map.mpr
      refine ⟨rightIncidence (k / 2), ?_, rfl⟩
      rw [alignedIncidenceBox]
      apply Finset.mem_union_right
      exact Finset.mem_map.mpr
        ⟨k / 2, Finset.mem_range.mpr hhalf, rfl⟩

/-- Pertencer a caixa equivale a estar abaixo da ultima perna `4M+1`. -/
theorem mem_alignedOddLegBox_iff {M : ℕ} {n : OddLeg} :
    n ∈ alignedOddLegBox M ↔ n.1 ≤ 4 * M + 1 := by
  rw [alignedOddLegBox_eq_arithmeticOddLegBox]
  constructor
  · intro hn
    rcases Finset.mem_map.mp hn with ⟨k, hk, hkn⟩
    have hklt : k < 2 * M := Finset.mem_range.mp hk
    have hv : 2 * k + 3 = n.1 :=
      congrArg (fun m : OddLeg => m.1) hkn
    omega
  · intro hn
    rcases n.2.2 with ⟨q, hq⟩
    have hqpos : 1 ≤ q := by omega
    have hklt : q - 1 < 2 * M := by omega
    have heq : arithmeticOddLeg (q - 1) = n := by
      apply Subtype.ext
      change 2 * (q - 1) + 3 = n.1
      omega
    rw [← heq]
    exact Finset.mem_map.mpr
      ⟨q - 1, Finset.mem_range.mpr hklt, rfl⟩

/-- A caixa alinhada com `M` centros possui exatamente `2M` pernas. -/
@[simp] theorem card_alignedOddLegBox (M : ℕ) :
    (alignedOddLegBox M).card = 2 * M := by
  rw [alignedOddLegBox_eq_arithmeticOddLegBox]
  simp [arithmeticOddLegBox]

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
