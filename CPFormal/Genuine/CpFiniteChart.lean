import CPFormal.Genuine.Cp
import CPFormal.Carry.CpBalancedResidue

/-!
# Carta finita `C_p` por blocos completos

Este arquivo abre cada bracket antes de qualquer passagem ao limite. Para um
centro `c`, o intervalo completo de offsets e

`[-halfRange p, ..., 0, ..., halfRange p]`.

O `legSum` usa o mesmo intervalo sem o zero. Portanto um bracket saturado e
literalmente

`bloco completo no centro c - p * f(c)`.

Somando os primeiros `M` centros `p, 2p, ..., Mp`, obtemos a identidade
finita da carta como prefixo por blocos menos a correcao vertical dos centros.
Os blocos sao depois ladrilhados no intervalo literal
`1, ..., pM + halfRange p`. Ainda nao introduzimos potencias complexas, series
infinitas ou limites.
-/

open scoped BigOperators

namespace CPFormal.Genuine.Cp

variable {R : Type*} [CommRing R]

noncomputable section

/-- Intervalo completo da camera, incluindo o offset central `0`. -/
def fullOffsets (p : ℕ) : Finset ℤ :=
  Finset.Icc (-(halfRange p : ℤ)) (halfRange p : ℤ)

/-- Um bloco completo de valores em torno do centro `center`. -/
def centerBlock (p : ℕ) (f : ℤ → R) (center : ℤ) : R :=
  ∑ a ∈ fullOffsets p, f (center + a)

/-- A semente positiva `1, ..., halfRange p` da carta finita. -/
def seedSum (p : ℕ) (f : ℤ → R) : R :=
  ∑ n ∈ Finset.Icc (1 : ℤ) (halfRange p : ℤ), f n

/-- O `k`-esimo centro positivo, com indices iniciando em zero. -/
def alignedCenter (p k : ℕ) : ℤ :=
  (p : ℤ) * ((k + 1 : ℕ) : ℤ)

/-- Soma finita da semente e dos brackets nos centros `p, ..., Mp`. -/
def finiteChart (p M : ℕ) (f : ℤ → R) : R :=
  seedSum p f +
    ∑ k ∈ Finset.range M, bracket p f (alignedCenter p k)

/-- Prefixo finito ainda escrito como semente seguida de blocos completos. -/
def blockPrefix (p M : ℕ) (f : ℤ → R) : R :=
  seedSum p f +
    ∑ k ∈ Finset.range M, centerBlock p f (alignedCenter p k)

/-- Correcao vertical: `p` copias do valor em cada centro. -/
def verticalCorrection (p M : ℕ) (f : ℤ → R) : R :=
  ∑ k ∈ Finset.range M, (p : R) * f (alignedCenter p k)

/-- Remover o centro do intervalo completo recupera os offsets das pernas. -/
@[simp] theorem fullOffsets_erase_zero (p : ℕ) :
    (fullOffsets p).erase 0 = balancedOffsets p := by
  rfl

/-- O offset central pertence sempre ao bloco completo. -/
@[simp] theorem zero_mem_fullOffsets (p : ℕ) :
    (0 : ℤ) ∈ fullOffsets p := by
  simp [fullOffsets]

/-- Para `p` impar, um bloco completo possui literalmente `p` posicoes. -/
@[simp] theorem card_fullOffsets {p : ℕ} (hpodd : Odd p) :
    (fullOffsets p).card = p := by
  have hpformNat := CPFormal.Carry.Cp.two_mul_halfRange_add_one hpodd
  have hpformInt :
      (p : ℤ) = 2 * (halfRange p : ℤ) + 1 := by
    exact_mod_cast hpformNat.symm
  unfold fullOffsets
  rw [Int.card_Icc]
  rw [show
    (halfRange p : ℤ) + 1 - (-(halfRange p : ℤ)) = (p : ℤ) by omega]
  simp

/-- O bloco completo e a soma das pernas mais a unica copia do centro. -/
theorem centerBlock_eq_legSum_add_center
    (p : ℕ) (f : ℤ → R) (center : ℤ) :
    centerBlock p f center = legSum p f center + f center := by
  classical
  have hsum := Finset.sum_erase_add
    (fullOffsets p) (fun a : ℤ => f (center + a))
    (zero_mem_fullOffsets p)
  simpa [centerBlock, legSum] using hsum.symm

/-- Transladar os offsets completos produz o intervalo inteiro do bloco. -/
theorem centerBlock_eq_sum_Icc
    (p : ℕ) (f : ℤ → R) (center : ℤ) :
    centerBlock p f center =
      ∑ n ∈ Finset.Icc
        (center - (halfRange p : ℤ))
        (center + (halfRange p : ℤ)), f n := by
  classical
  unfold centerBlock fullOffsets
  apply Finset.sum_bijective (fun a : ℤ => center + a)
  · constructor
    · intro a b hab
      exact add_left_cancel hab
    · intro n
      exact ⟨n - center, by ring⟩
  · intro a
    simp only [Finset.mem_Icc]
    constructor <;> intro ha <;> constructor <;> omega
  · intro a ha
    rfl

/-- Soma sobre dois intervalos inteiros adjacentes. -/
theorem sum_Icc_split_adjacent
    (f : ℤ → R) {left middle right : ℤ}
    (hleft : left ≤ middle) (hright : middle < right) :
    (∑ n ∈ Finset.Icc left right, f n) =
      (∑ n ∈ Finset.Icc left middle, f n) +
        ∑ n ∈ Finset.Icc (middle + 1) right, f n := by
  classical
  have hdisjoint :
      Disjoint (Finset.Icc left middle) (Finset.Icc (middle + 1) right) := by
    rw [Finset.disjoint_left]
    intro n hnleft hnright
    simp only [Finset.mem_Icc] at hnleft hnright
    omega
  have hunion :
      Finset.Icc left middle ∪ Finset.Icc (middle + 1) right =
        Finset.Icc left right := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  rw [← hunion, Finset.sum_union hdisjoint]

/-- Acrescentar um centro acrescenta exatamente seu bloco completo. -/
theorem blockPrefix_succ
    (p M : ℕ) (f : ℤ → R) :
    blockPrefix p (M + 1) f =
      blockPrefix p M f + centerBlock p f (alignedCenter p M) := by
  unfold blockPrefix
  rw [Finset.sum_range_succ]
  ring

/-
O coeficiente `p-1` do bracket, junto da copia central que faltava nas
pernas, produz exatamente a correcao `p * f(center)`.
-/
theorem bracket_eq_centerBlock_sub_p_mul_center
    (p : ℕ) (hp : Nat.Prime p) (f : ℤ → R) (center : ℤ) :
    bracket p f center = centerBlock p f center - (p : R) * f center := by
  rw [centerBlock_eq_legSum_add_center]
  unfold bracket
  rw [Nat.cast_sub hp.one_le, Nat.cast_one]
  ring

/-!
Identidade finita principal deste modulo. Ela nao usa convergencia, zeta,
zeros, ortogonalidade ou argumentos numericos.
-/
theorem finiteChart_eq_blockPrefix_sub_verticalCorrection
    (p : ℕ) (hp : Nat.Prime p) (M : ℕ) (f : ℤ → R) :
    finiteChart p M f = blockPrefix p M f - verticalCorrection p M f := by
  classical
  unfold finiteChart blockPrefix verticalCorrection
  simp_rw [bracket_eq_centerBlock_sub_p_mul_center p hp]
  rw [Finset.sum_sub_distrib]
  ring

/-- A correcao vertical tambem pode ser lida como `p` vezes a soma dos centros. -/
theorem verticalCorrection_eq_p_mul_centerSum
    (p M : ℕ) (f : ℤ → R) :
    verticalCorrection p M f =
      (p : R) * ∑ k ∈ Finset.range M, f (alignedCenter p k) := by
  classical
  simp [verticalCorrection, Finset.mul_sum]

/-- Forma tradicional: prefixo por blocos menos `p` vezes os centros. -/
theorem finiteChart_eq_blockPrefix_sub_p_mul_centerSum
    (p : ℕ) (hp : Nat.Prime p) (M : ℕ) (f : ℤ → R) :
    finiteChart p M f =
      blockPrefix p M f -
        (p : R) * ∑ k ∈ Finset.range M, f (alignedCenter p k) := by
  rw [finiteChart_eq_blockPrefix_sub_verticalCorrection p hp]
  rw [verticalCorrection_eq_p_mul_centerSum]

/-!
Ladrilhamento minimo necessario para ligar a carta por blocos ao prefixo
literal dos inteiros positivos.
-/
theorem blockPrefix_eq_positiveIntervalSum
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (M : ℕ) (f : ℤ → R) :
    blockPrefix p M f =
      ∑ n ∈ Finset.Icc (1 : ℤ)
        ((p : ℤ) * (M : ℤ) + (halfRange p : ℤ)), f n := by
  induction M with
  | zero =>
      simp [blockPrefix, seedSum]
  | succ M ih =>
      rw [blockPrefix_succ, ih, centerBlock_eq_sum_Icc]
      have hpformNat := CPFormal.Carry.Cp.two_mul_halfRange_add_one hpodd
      have hpformInt :
          (p : ℤ) = 2 * (halfRange p : ℤ) + 1 := by
        exact_mod_cast hpformNat.symm
      have hlower :
          alignedCenter p M - (halfRange p : ℤ) =
            (p : ℤ) * (M : ℤ) + (halfRange p : ℤ) + 1 := by
        unfold alignedCenter
        push_cast
        rw [hpformInt]
        ring
      have hupper :
          alignedCenter p M + (halfRange p : ℤ) =
            (p : ℤ) * ((M + 1 : ℕ) : ℤ) + (halfRange p : ℤ) := by
        rfl
      rw [hlower, hupper]
      have hhNat : 1 ≤ halfRange p := by
        have hpgt := hp.one_lt
        omega
      have hhInt : (1 : ℤ) ≤ (halfRange p : ℤ) := by
        exact_mod_cast hhNat
      have hnonneg : 0 ≤ (p : ℤ) * (M : ℤ) := by
        positivity
      have hleft :
          (1 : ℤ) ≤
            (p : ℤ) * (M : ℤ) + (halfRange p : ℤ) := by
        omega
      have hpIntPos : 0 < (p : ℤ) := by
        exact_mod_cast hp.pos
      have hstep :
          (p : ℤ) * ((M + 1 : ℕ) : ℤ) + (halfRange p : ℤ) =
            ((p : ℤ) * (M : ℤ) + (halfRange p : ℤ)) + (p : ℤ) := by
        push_cast
        ring
      have hright :
          (p : ℤ) * (M : ℤ) + (halfRange p : ℤ) <
            (p : ℤ) * ((M + 1 : ℕ) : ℤ) + (halfRange p : ℤ) := by
        rw [hstep]
        exact lt_add_of_pos_right _ hpIntPos
      exact (sum_Icc_split_adjacent f hleft hright).symm

/-- Carta finita escrita diretamente no prefixo positivo literal. -/
theorem finiteChart_eq_positiveIntervalSum_sub_p_mul_centerSum
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (M : ℕ) (f : ℤ → R) :
    finiteChart p M f =
      (∑ n ∈ Finset.Icc (1 : ℤ)
        ((p : ℤ) * (M : ℤ) + (halfRange p : ℤ)), f n) -
          (p : R) * ∑ k ∈ Finset.range M, f (alignedCenter p k) := by
  rw [finiteChart_eq_blockPrefix_sub_p_mul_centerSum p hp]
  rw [blockPrefix_eq_positiveIntervalSum p hp hpodd]

end

end CPFormal.Genuine.Cp
