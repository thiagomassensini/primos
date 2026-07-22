import CPFormal.Carry.CpDepth

/-!
# Reindexacao ponderada finita Cₚ

Este arquivo transporta uma soma finita indexada por pernas inteiras nao
multiplas de um primo impar `p` para as incidencias centro--offset da camera
`Cₚ`.

O termo do canal direto usa a profundidade efetiva, definida como o supremo
sobre todos os offsets balanceados. O termo da incidencia usa diretamente a
valoracao `p`-adica do centro. O teorema de profundidade de `CpDepth` prova que
os dois pesos coincidem sob a bijecao global.

Para uma caixa de incidencias esperada que nao coincide com a imagem da caixa
de pernas, o bordo permanece literal:

`bordo = incidencias extras - incidencias faltantes`.

Nao ha limite, serie infinita, zeta, funcao L ou zero neste arquivo.
-/

open scoped BigOperators

namespace CPFormal.Carry.Cp

noncomputable section

/-- Imagem de uma caixa finita de pernas pela bijecao global `Cₚ`. -/
def incidenceImage
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (legs : Finset (Nonmultiple p)) : Finset (Incidence p) :=
  legs.map (nonmultipleEquivIncidence p hp hpodd).toEmbedding

/-- Termo ponderado no canal direto das pernas nao multiplas de `p`. -/
def nonmultipleTerm {R : Type*} [Mul R]
    (p : ℕ) (depthWeight : ℕ → R) (value : ℤ → R)
    (n : Nonmultiple p) : R :=
  depthWeight (effectiveDepth p n.1) * value n.1

/-- O mesmo termo escrito nas coordenadas centro--offset de uma incidencia. -/
def incidenceTerm {R : Type*} [Mul R]
    (p : ℕ) (depthWeight : ℕ → R) (value : ℤ → R)
    (x : Incidence p) : R :=
  depthWeight (padicValInt p x.1.1) * value (x.1.1 + x.1.2.1)

/--
O peso de profundidade e o valor da perna sao preservados pela ida canonica
da bijecao `Cₚ`.
-/
@[simp] theorem incidenceTerm_incidenceOfNonmultiple
    {R : Type*} [Mul R]
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (depthWeight : ℕ → R) (value : ℤ → R)
    (n : Nonmultiple p) :
    incidenceTerm p depthWeight value
        (incidenceOfNonmultiple p hp hpodd n) =
      nonmultipleTerm p depthWeight value n := by
  change
    depthWeight
        (padicValInt p (centerOfNonmultiple p hp hpodd n)) *
          value
            ((incidenceOfNonmultiple p hp hpodd n).1.1 +
              (incidenceOfNonmultiple p hp hpodd n).1.2.1) =
      depthWeight (effectiveDepth p n.1) * value n.1
  rw [incidenceOfNonmultiple_leg]
  rw [effectiveDepth_eq_centerDepth]
  rfl

/-- A mesma preservacao escrita por meio da equivalencia nomeada. -/
@[simp] theorem incidenceTerm_nonmultipleEquivIncidence
    {R : Type*} [Mul R]
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (depthWeight : ℕ → R) (value : ℤ → R)
    (n : Nonmultiple p) :
    incidenceTerm p depthWeight value
        (nonmultipleEquivIncidence p hp hpodd n) =
      nonmultipleTerm p depthWeight value n := by
  simp [nonmultipleEquivIncidence]

/-- Reindexacao exata de qualquer caixa finita de pernas `Cₚ`. -/
theorem weighted_reindex
    {R : Type*} [CommRing R]
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (legs : Finset (Nonmultiple p))
    (depthWeight : ℕ → R) (value : ℤ → R) :
    (∑ n ∈ legs, nonmultipleTerm p depthWeight value n) =
      ∑ x ∈ incidenceImage p hp hpodd legs,
        incidenceTerm p depthWeight value x := by
  classical
  symm
  simp [incidenceImage]

/-- Incidencias do canal direto que estao fora da caixa esperada. -/
noncomputable def extraIncidences
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (legs : Finset (Nonmultiple p))
    (expected : Finset (Incidence p)) : Finset (Incidence p) := by
  classical
  exact incidenceImage p hp hpodd legs \ expected

/-- Incidencias esperadas que estao ausentes no canal direto. -/
noncomputable def missingIncidences
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (legs : Finset (Nonmultiple p))
    (expected : Finset (Incidence p)) : Finset (Incidence p) := by
  classical
  exact expected \ incidenceImage p hp hpodd legs

/--
Identidade abstrata de bordo para dois conjuntos finitos. A igualdade e
independente da origem aritmetica dos termos.
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
Reindexacao ponderada `Cₚ` com o bordo assinado preservado literalmente.
-/
theorem weighted_reindex_with_boundary
    {R : Type*} [CommRing R]
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (legs : Finset (Nonmultiple p))
    (expected : Finset (Incidence p))
    (depthWeight : ℕ → R) (value : ℤ → R) :
    (∑ n ∈ legs, nonmultipleTerm p depthWeight value n) =
      (∑ x ∈ expected, incidenceTerm p depthWeight value x) +
        ((∑ x ∈ extraIncidences p hp hpodd legs expected,
            incidenceTerm p depthWeight value x) -
          ∑ x ∈ missingIncidences p hp hpodd legs expected,
            incidenceTerm p depthWeight value x) := by
  classical
  rw [weighted_reindex p hp hpodd]
  simpa [extraIncidences, missingIncidences] using
    (finset_sum_eq_expected_add_boundary
      (incidenceImage p hp hpodd legs) expected
      (incidenceTerm p depthWeight value))

/-- Caixas `Cₚ` com cobertura exata possuem bordo vazio. -/
theorem weighted_reindex_of_exact_cover
    {R : Type*} [CommRing R]
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (legs : Finset (Nonmultiple p))
    (expected : Finset (Incidence p))
    (depthWeight : ℕ → R) (value : ℤ → R)
    (hcover : incidenceImage p hp hpodd legs = expected) :
    (∑ n ∈ legs, nonmultipleTerm p depthWeight value n) =
      ∑ x ∈ expected, incidenceTerm p depthWeight value x := by
  rw [weighted_reindex p hp hpodd, hcover]

end

end CPFormal.Carry.Cp
