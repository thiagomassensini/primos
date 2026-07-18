import CPFormal.Carry.C2Depth

/-!
# Reindexacao ponderada finita C2

Este arquivo transforma uma soma finita indexada por pernas impares numa soma
indexada pelas incidencias centro--perna correspondentes. A igualdade de
profundidade provada em `C2Depth` transporta o peso de carry.

Para duas caixas finitas que nao coincidem, o bordo e mantido explicitamente:

`bordo = incidencias extras - incidencias faltantes`.

Nao ha limite, serie infinita, zeta ou zero neste arquivo.
-/

open scoped BigOperators

namespace CPFormal.Carry.C2

/-- Imagem de uma caixa finita de pernas pela bijecao C2. -/
def incidenceImage (legs : Finset OddLeg) : Finset Incidence :=
  legs.map oddLegEquivIncidence.toEmbedding

/-- Termo ponderado visto pelo canal direto. -/
def oddLegTerm {R : Type*} [Mul R]
    (depthWeight : ℕ → R) (value : ℕ → R) (n : OddLeg) : R :=
  depthWeight (effectiveDepth n.1) * value n.1

/-- O mesmo termo escrito nas coordenadas centro--perna. -/
def incidenceTerm {R : Type*} [Mul R]
    (depthWeight : ℕ → R) (value : ℕ → R) (x : Incidence) : R :=
  depthWeight (padicValNat 2 x.1.1) * value x.1.2

/-- O peso e o valor de uma perna sao preservados pela bijecao. -/
@[simp] theorem incidenceTerm_incidenceOfOddLeg
    {R : Type*} [Mul R] (depthWeight : ℕ → R) (value : ℕ → R)
    (n : OddLeg) :
    incidenceTerm depthWeight value (incidenceOfOddLeg n) =
      oddLegTerm depthWeight value n := by
  change
    depthWeight (padicValNat 2 (adjacentCenter n.1)) * value n.1 =
      depthWeight (effectiveDepth n.1) * value n.1
  rw [effectiveDepth_eq_centerDepth n.2.1 n.2.2]

/-- The same transport lemma through the named equivalence. -/
@[simp] theorem incidenceTerm_oddLegEquivIncidence
    {R : Type*} [Mul R] (depthWeight : ℕ → R) (value : ℕ → R)
    (n : OddLeg) :
    incidenceTerm depthWeight value (oddLegEquivIncidence n) =
      oddLegTerm depthWeight value n := by
  simp [oddLegEquivIncidence]

/-- Reindexacao exata de qualquer caixa finita de pernas. -/
theorem weighted_reindex
    {R : Type*} [CommRing R]
    (legs : Finset OddLeg) (depthWeight : ℕ → R) (value : ℕ → R) :
    (∑ n ∈ legs, oddLegTerm depthWeight value n) =
      ∑ x ∈ incidenceImage legs, incidenceTerm depthWeight value x := by
  classical
  symm
  simp [incidenceImage]

/-- Incidencias presentes no canal direto mas fora da caixa de brackets. -/
noncomputable def extraIncidences
    (legs : Finset OddLeg) (expected : Finset Incidence) : Finset Incidence := by
  classical
  exact incidenceImage legs \ expected

/-- Incidencias exigidas pela caixa de brackets mas ausentes no canal direto. -/
noncomputable def missingIncidences
    (legs : Finset OddLeg) (expected : Finset Incidence) : Finset Incidence := by
  classical
  exact expected \ incidenceImage legs

/--
Identidade abstrata de bordo para duas caixas finitas. Ela e independente da
origem dos termos somados.
-/
theorem finset_sum_eq_expected_add_boundary
    {α R : Type*} [DecidableEq α] [CommRing R]
    (actual expected : Finset α) (term : α → R) :
    (∑ x ∈ actual, term x) =
      (∑ x ∈ expected, term x) +
        ((∑ x ∈ actual \ expected, term x) -
          ∑ x ∈ expected \ actual, term x) := by
  have hactual :
      (∑ x ∈ actual, term x) =
        (∑ x ∈ actual ∩ expected, term x) +
          ∑ x ∈ actual \ expected, term x := by
    exact (actual.sum_inter_add_sum_sdiff expected term).symm
  have hexpected :
      (∑ x ∈ expected, term x) =
        (∑ x ∈ actual ∩ expected, term x) +
          ∑ x ∈ expected \ actual, term x := by
    calc
      (∑ x ∈ expected, term x) =
          (∑ x ∈ expected ∩ actual, term x) +
            ∑ x ∈ expected \ actual, term x :=
        (expected.sum_inter_add_sum_sdiff actual term).symm
      _ = (∑ x ∈ actual ∩ expected, term x) +
            ∑ x ∈ expected \ actual, term x := by
        rw [Finset.inter_comm expected actual]
  rw [hactual, hexpected]
  abel

/--
Reindexacao ponderada C2 com o bordo assinado preservado literalmente.
-/
theorem weighted_reindex_with_boundary
    {R : Type*} [CommRing R]
    (legs : Finset OddLeg) (expected : Finset Incidence)
    (depthWeight : ℕ → R) (value : ℕ → R) :
    (∑ n ∈ legs, oddLegTerm depthWeight value n) =
      (∑ x ∈ expected, incidenceTerm depthWeight value x) +
        ((∑ x ∈ extraIncidences legs expected,
            incidenceTerm depthWeight value x) -
          ∑ x ∈ missingIncidences legs expected,
            incidenceTerm depthWeight value x) := by
  classical
  rw [weighted_reindex]
  exact finset_sum_eq_expected_add_boundary
    (incidenceImage legs) expected (incidenceTerm depthWeight value)

/-- Caixas perfeitamente alinhadas possuem bordo vazio. -/
theorem weighted_reindex_of_exact_cover
    {R : Type*} [CommRing R]
    (legs : Finset OddLeg) (expected : Finset Incidence)
    (depthWeight : ℕ → R) (value : ℕ → R)
    (hcover : incidenceImage legs = expected) :
    (∑ n ∈ legs, oddLegTerm depthWeight value n) =
      ∑ x ∈ expected, incidenceTerm depthWeight value x := by
  rw [weighted_reindex, hcover]

end CPFormal.Carry.C2
