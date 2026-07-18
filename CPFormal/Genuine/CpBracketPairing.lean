import CPFormal.Finite.Bracket
import CPFormal.Genuine.CpFiniteChart

/-!
# Identificacao da braquetada saturada com a camera Genuine Cp

Este arquivo fecha uma identidade puramente finita. Para primo impar, os
offsets balanceados nao nulos sao exatamente os pares

`-halfRange(p), ..., -1, 1, ..., halfRange(p)`.

Logo o `Genuine.Cp.bracket`, definido pela soma das pernas menos `p-1`
copias do centro, coincide com a soma das segundas diferencas de raios
`1, ..., halfRange(p)`.
-/

open scoped BigOperators

namespace CPFormal.Genuine.Cp

variable {R : Type*} [CommRing R]

noncomputable section

/-- Reindexacao dos raios naturais positivos pelo intervalo inteiro positivo. -/
lemma sum_nat_radii_eq_sum_int_positive
    (h : ℕ) (g : ℤ → R) :
    (∑ radius ∈ Finset.Icc 1 h, g (radius : ℤ)) =
      ∑ a ∈ Finset.Icc (1 : ℤ) (h : ℤ), g a := by
  classical
  refine Finset.sum_bij (fun radius _ ↦ (radius : ℤ)) ?_ ?_ ?_ ?_
  · intro radius hradius
    simp only [Finset.mem_Icc] at hradius ⊢
    exact_mod_cast hradius
  · intro radius₁ hradius₁ radius₂ hradius₂ heq
    exact_mod_cast heq
  · intro a ha
    have haBounds := Finset.mem_Icc.mp ha
    have haNonneg : 0 ≤ a := le_trans (by norm_num) haBounds.1
    have hcast : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg haNonneg
    refine ⟨a.toNat, ?_, hcast⟩
    apply Finset.mem_Icc.mpr
    constructor
    · exact_mod_cast (show (1 : ℤ) ≤ (a.toNat : ℤ) by simpa [hcast] using haBounds.1)
    · exact_mod_cast (show (a.toNat : ℤ) ≤ (h : ℤ) by simpa [hcast] using haBounds.2)
  · intro radius hradius
    rfl

/-- Reindexacao dos raios naturais positivos pelo intervalo inteiro negativo. -/
lemma sum_neg_nat_radii_eq_sum_int_negative
    (h : ℕ) (g : ℤ → R) :
    (∑ radius ∈ Finset.Icc 1 h, g (-(radius : ℤ))) =
      ∑ a ∈ Finset.Icc (-(h : ℤ)) (-1), g a := by
  classical
  refine Finset.sum_bij (fun radius _ ↦ -(radius : ℤ)) ?_ ?_ ?_ ?_
  · intro radius hradius
    simp only [Finset.mem_Icc] at hradius ⊢
    have hlower : (1 : ℤ) ≤ (radius : ℤ) := by exact_mod_cast hradius.1
    have hupper : (radius : ℤ) ≤ (h : ℤ) := by exact_mod_cast hradius.2
    constructor <;> omega
  · intro radius₁ hradius₁ radius₂ hradius₂ heq
    have : (radius₁ : ℤ) = (radius₂ : ℤ) := neg_injective heq
    exact_mod_cast this
  · intro a ha
    have haBounds := Finset.mem_Icc.mp ha
    have hnegNonneg : 0 ≤ -a := by omega
    have hcast : (((-a).toNat : ℕ) : ℤ) = -a :=
      Int.toNat_of_nonneg hnegNonneg
    refine ⟨(-a).toNat, ?_, ?_⟩
    · apply Finset.mem_Icc.mpr
      constructor
      · exact_mod_cast (show (1 : ℤ) ≤ ((-a).toNat : ℤ) by
          rw [hcast]
          omega)
      · exact_mod_cast (show (((-a).toNat : ℕ) : ℤ) ≤ (h : ℤ) by
          rw [hcast]
          omega)
    · rw [hcast]
      omega
  · intro radius hradius
    rfl

/-- Um bloco completo e o centro seguido dos pares de raios positivos. -/
theorem centerBlock_eq_center_add_pairSum
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (f : ℤ → R) (center : ℤ) :
    centerBlock p f center =
      f center +
        ∑ radius ∈ Finset.Icc 1 (halfRange p),
          (f (center - (radius : ℤ)) + f (center + (radius : ℤ))) := by
  classical
  rcases hpodd with ⟨q, hq⟩
  have hp3 : 3 ≤ p := by
    have hp2 := hp.two_le
    omega
  have hh : 1 ≤ halfRange p := by
    unfold halfRange
    omega
  have hneg : -(halfRange p : ℤ) ≤ -1 := by exact_mod_cast hh
  have hpos : (0 : ℤ) < halfRange p := by exact_mod_cast hh
  rw [centerBlock]
  unfold fullOffsets
  rw [sum_Icc_split_adjacent (fun a : ℤ ↦ f (center + a)) hneg (by omega)]
  rw [sum_Icc_split_adjacent (fun a : ℤ ↦ f (center + a)) (by omega) hpos]
  rw [← sum_neg_nat_radii_eq_sum_int_negative
    (R := R) (halfRange p) (fun a : ℤ ↦ f (center + a))]
  rw [← sum_nat_radii_eq_sum_int_positive
    (R := R) (halfRange p) (fun a : ℤ ↦ f (center + a))]
  simp only [Finset.sum_add_distrib]
  simp <;> ring

/-- As pernas balanceadas sao exatamente a soma dos pares de raios positivos. -/
theorem legSum_eq_pairSum
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (f : ℤ → R) (center : ℤ) :
    legSum p f center =
      ∑ radius ∈ Finset.Icc 1 (halfRange p),
        (f (center - (radius : ℤ)) + f (center + (radius : ℤ))) := by
  have hblock := centerBlock_eq_center_add_pairSum p hp hpodd f center
  rw [centerBlock_eq_legSum_add_center] at hblock
  exact add_right_cancel (hblock.trans (add_comm _ _))

/-!
Identidade finita central: a definicao por pernas balanceadas e a definicao
por segundas diferencas saturadas sao o mesmo objeto.
-/
theorem bracket_eq_saturatedBracket
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (f : ℤ → R) (center : ℤ) :
    bracket p f center =
      CPFormal.saturatedBracket (halfRange p) f center := by
  classical
  have hleg := legSum_eq_pairSum p hp hpodd f center
  have hpform := CPFormal.Carry.Cp.two_mul_halfRange_add_one hpodd
  have hpminus : p - 1 = 2 * halfRange p := by omega
  have hcard : (Finset.Icc 1 (halfRange p)).card = halfRange p := by
    rw [Nat.card_Icc]
    omega
  unfold bracket CPFormal.saturatedBracket CPFormal.centeredSecondDifference
  rw [hleg]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp [hcard, hpminus, nsmul_eq_mul] <;> ring

end

end CPFormal.Genuine.Cp
