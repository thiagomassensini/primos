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
Ainda nao identificamos aqui o prefixo por blocos com uma serie de Dirichlet,
nem tomamos limites.
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

/-
O coeficiente `p-1` do bracket, junto da copia central que faltava nas
pernas, produz exatamente a correcao `p * f(center)`.
-/
theorem bracket_eq_centerBlock_sub_p_mul_center
    (p : ℕ) (hp : Nat.Prime p) (f : ℤ → R) (center : ℤ) :
    bracket p f center = centerBlock p f center - (p : R) * f center := by
  have hpcast : (((p - 1 : ℕ) : R) + 1) = (p : R) := by
    rw [← Nat.cast_one, ← Nat.cast_add, Nat.sub_add_cancel hp.one_le]
  rw [centerBlock_eq_legSum_add_center]
  unfold bracket
  rw [← hpcast]
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

end

end CPFormal.Genuine.Cp
