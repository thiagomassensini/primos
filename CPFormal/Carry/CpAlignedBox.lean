import CPFormal.Carry.CpWeightedReindex

/-!
# Caixas aritmeticas `Cₚ` perfeitamente alinhadas

Fixe um primo impar `p`. Para `M` centros, a caixa bracketada deste arquivo
usa os centros positivos

`p, 2p, ..., Mp`

e, em cada centro, inclui todos os `p-1` offsets balanceados nao nulos. A
caixa direta de pernas e a pre-imagem dessa caixa pela bijecao global `Cₚ`.

O arquivo prova que:

- as incidencias construidas nao colidem;
- as caixas de incidencias e de pernas possuem cardinalidade `M * (p-1)`;
- aplicar a bijecao a caixa direta recupera exatamente a caixa bracketada;
- extras e faltantes sao ambos vazios;
- a reindexacao ponderada nao possui termo de bordo.

Nao ha limite, serie infinita, zeta, funcao L ou zero neste arquivo.
-/

open scoped BigOperators

namespace CPFormal.Carry.Cp

open CPFormal.Genuine.Cp

noncomputable section

/-- A incidencia no centro `p * (k+1)` e no offset balanceado `a`. -/
def alignedIncidence
    (p : ℕ) (k : ℕ) (a : BalancedOffset p) : Incidence p := by
  refine ⟨(((p : ℤ) * ((k + 1 : ℕ) : ℤ), a)), ?_⟩
  exact ⟨((k + 1 : ℕ) : ℤ), rfl⟩

/--
Pares diferentes `(indice do centro, offset)` produzem incidencias diferentes.
-/
def alignedIncidenceEmbedding
    (p : ℕ) (hp : Nat.Prime p) :
    (ℕ × BalancedOffset p) ↪ Incidence p where
  toFun ka := alignedIncidence p ka.1 ka.2
  inj' := by
    intro x y hxy
    apply Prod.ext
    · have hcenter := congrArg (fun z : Incidence p => z.1.1) hxy
      change
        (p : ℤ) * ((x.1 + 1 : ℕ) : ℤ) =
          (p : ℤ) * ((y.1 + 1 : ℕ) : ℤ) at hcenter
      have hpzero : (p : ℤ) ≠ 0 := by
        exact_mod_cast hp.ne_zero
      have hsuccInt := mul_left_cancel₀ hpzero hcenter
      have hsucc : x.1 + 1 = y.1 + 1 := by
        exact_mod_cast hsuccInt
      omega
    · exact congrArg (fun z : Incidence p => z.1.2) hxy

/-- Os indices dos primeiros `M` centros e de todos os offsets da camera. -/
def incidenceIndexBox (p M : ℕ) : Finset (ℕ × BalancedOffset p) :=
  (Finset.range M).product (balancedOffsets p).attach

/--
Caixa concreta de incidencias nos centros `p, 2p, ..., Mp`, com todas as
`p-1` pernas de cada centro.
-/
def alignedIncidenceBox
    (p : ℕ) (hp : Nat.Prime p) (M : ℕ) : Finset (Incidence p) :=
  (incidenceIndexBox p M).map (alignedIncidenceEmbedding p hp)

/--
Uma incidencia pertence a caixa se, e somente se, seu centro e um dos
multiplos `p, 2p, ..., Mp`.
-/
theorem mem_alignedIncidenceBox_iff
    (p : ℕ) (hp : Nat.Prime p) (M : ℕ) (x : Incidence p) :
    x ∈ alignedIncidenceBox p hp M ↔
      ∃ k < M, x.1.1 = (p : ℤ) * ((k + 1 : ℕ) : ℤ) := by
  constructor
  · intro hx
    rcases Finset.mem_map.mp hx with ⟨ka, hka, hkax⟩
    have hk : ka.1 < M :=
      Finset.mem_range.mp (Finset.mem_product.mp hka).1
    refine ⟨ka.1, hk, ?_⟩
    have hcenter := congrArg (fun z : Incidence p => z.1.1) hkax
    exact hcenter.symm
  · rintro ⟨k, hk, hcenter⟩
    apply Finset.mem_map.mpr
    refine ⟨(k, x.1.2), ?_, ?_⟩
    · apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_range.mpr hk
      · exact Finset.mem_attach (balancedOffsets p) x.1.2
    · apply Subtype.ext
      apply Prod.ext
      · exact hcenter.symm
      · rfl

/-- A caixa de indices possui `M * (p-1)` enderecos. -/
@[simp] theorem card_incidenceIndexBox
    {p M : ℕ} (hpodd : Odd p) :
    (incidenceIndexBox p M).card = M * (p - 1) := by
  simp only [incidenceIndexBox, BalancedOffset, Finset.card_product,
    Finset.card_range, Finset.card_attach, card_balancedOffsets hpodd]

/-- A caixa de incidencias possui `M * (p-1)` elementos distintos. -/
@[simp] theorem card_alignedIncidenceBox
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) (M : ℕ) :
    (alignedIncidenceBox p hp M).card = M * (p - 1) := by
  simp [alignedIncidenceBox, card_incidenceIndexBox hpodd]

/-- A caixa direta e a pre-imagem exata da caixa bracketada pela bijecao. -/
def alignedNonmultipleBox
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) (M : ℕ) :
    Finset (Nonmultiple p) :=
  (alignedIncidenceBox p hp M).map
    (nonmultipleEquivIncidence p hp hpodd).symm.toEmbedding

/-- A caixa direta tambem possui exatamente `M * (p-1)` pernas. -/
@[simp] theorem card_alignedNonmultipleBox
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) (M : ℕ) :
    (alignedNonmultipleBox p hp hpodd M).card = M * (p - 1) := by
  simp [alignedNonmultipleBox, card_alignedIncidenceBox p hp hpodd M]

/-- Aplicar a bijecao de volta recupera literalmente a caixa bracketada. -/
theorem incidenceImage_alignedNonmultipleBox
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) (M : ℕ) :
    incidenceImage p hp hpodd (alignedNonmultipleBox p hp hpodd M) =
      alignedIncidenceBox p hp M := by
  classical
  ext x
  simp [incidenceImage, alignedNonmultipleBox]

/-- A caixa alinhada `Cₚ` nao possui incidencias extras. -/
@[simp] theorem extraIncidences_alignedBox
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) (M : ℕ) :
    extraIncidences p hp hpodd
      (alignedNonmultipleBox p hp hpodd M)
      (alignedIncidenceBox p hp M) = ∅ := by
  classical
  simp [extraIncidences, incidenceImage_alignedNonmultipleBox]

/-- A caixa alinhada `Cₚ` nao possui incidencias faltantes. -/
@[simp] theorem missingIncidences_alignedBox
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) (M : ℕ) :
    missingIncidences p hp hpodd
      (alignedNonmultipleBox p hp hpodd M)
      (alignedIncidenceBox p hp M) = ∅ := by
  classical
  simp [missingIncidences, incidenceImage_alignedNonmultipleBox]

/--
Reindexacao ponderada exata para os centros `p, 2p, ..., Mp` e todas as suas
pernas balanceadas.
-/
theorem weighted_reindex_alignedBox
    {R : Type*} [CommRing R]
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) (M : ℕ)
    (depthWeight : ℕ → R) (value : ℤ → R) :
    (∑ n ∈ alignedNonmultipleBox p hp hpodd M,
        nonmultipleTerm p depthWeight value n) =
      ∑ x ∈ alignedIncidenceBox p hp M,
        incidenceTerm p depthWeight value x := by
  apply weighted_reindex_of_exact_cover p hp hpodd
  exact incidenceImage_alignedNonmultipleBox p hp hpodd M

end

end CPFormal.Carry.Cp
