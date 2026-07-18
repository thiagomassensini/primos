import Mathlib

/-!
# Bijeção local de carry C2

Todo impar `n >= 3` possui exatamente um vizinho multiplo de quatro. Esse
vizinho e o centro C2 cuja perna e `n`. Esta e a camada combinatoria que liga o
canal direto, indexado por impares, ao canal bracketado, indexado por centros.
-/

namespace CPFormal.Carry.C2

/-- O vizinho de um impar que ocupa a vertical C2 de profundidade pelo menos 2. -/
def adjacentCenter (n : ℕ) : ℕ :=
  if n % 4 = 1 then n - 1 else n + 1

theorem odd_mod_four {n : ℕ} (hn : Odd n) :
    n % 4 = 1 ∨ n % 4 = 3 :=
  Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hn)

@[simp] theorem adjacentCenter_of_mod_one {n : ℕ} (h : n % 4 = 1) :
    adjacentCenter n = n - 1 := by
  simp [adjacentCenter, h]

@[simp] theorem adjacentCenter_of_mod_three {n : ℕ} (h : n % 4 = 3) :
    adjacentCenter n = n + 1 := by
  simp [adjacentCenter, h]

/-- O centro escolhido e sempre multiplo de quatro. -/
theorem four_dvd_adjacentCenter {n : ℕ} (hn : Odd n) :
    4 ∣ adjacentCenter n := by
  rw [Nat.dvd_iff_mod_eq_zero]
  rcases odd_mod_four hn with h | h
  · rw [adjacentCenter_of_mod_one h]
    omega
  · rw [adjacentCenter_of_mod_three h]
    omega

/-- Para as pernas do Genuine, o centro escolhido comeca em `4`. -/
theorem four_le_adjacentCenter {n : ℕ} (hn3 : 3 ≤ n) (hn : Odd n) :
    4 ≤ adjacentCenter n := by
  rcases odd_mod_four hn with h | h
  · rw [adjacentCenter_of_mod_one h]
    omega
  · rw [adjacentCenter_of_mod_three h]
    omega

/-- O impar original e literalmente uma das duas pernas do centro escolhido. -/
theorem leg_of_adjacentCenter {n : ℕ} (hn3 : 3 ≤ n) (hn : Odd n) :
    n = adjacentCenter n - 1 ∨ n = adjacentCenter n + 1 := by
  rcases odd_mod_four hn with h | h
  · right
    rw [adjacentCenter_of_mod_one h]
    omega
  · left
    rw [adjacentCenter_of_mod_three h]
    omega

/--
Unicidade do centro: qualquer multiplo de quatro que tenha `n` como perna e o
centro construido por `adjacentCenter`.
-/
theorem adjacentCenter_unique {n c : ℕ}
    (hn3 : 3 ≤ n) (hc : 4 ∣ c)
    (hleg : n = c - 1 ∨ n = c + 1) :
    adjacentCenter n = c := by
  have hcmod : c % 4 = 0 := Nat.dvd_iff_mod_eq_zero.mp hc
  unfold adjacentCenter
  split_ifs with h
  · rcases hleg with hleg | hleg <;> omega
  · rcases hleg with hleg | hleg <;> omega

/-- Dominio das pernas C2: impares a partir de `3`. -/
def OddLeg := {n : ℕ // 3 ≤ n ∧ Odd n}

/--
Uma incidencia C2 guarda um centro multiplo de quatro e uma de suas duas
pernas. A perna faz parte do dado: centros sozinhos nao estao em bijecao com
as pernas, pois cada centro possui duas delas.
-/
def Incidence :=
  {x : ℕ × ℕ //
    4 ≤ x.1 ∧ 4 ∣ x.1 ∧ (x.2 = x.1 - 1 ∨ x.2 = x.1 + 1)}

/-- A incidencia determinada por uma perna impar. -/
def incidenceOfOddLeg (n : OddLeg) : Incidence :=
  ⟨(adjacentCenter n.1, n.1),
    four_le_adjacentCenter n.2.1 n.2.2,
    four_dvd_adjacentCenter n.2.2,
    leg_of_adjacentCenter n.2.1 n.2.2⟩

/-- A perna guardada por uma incidencia C2 e impar e pelo menos `3`. -/
def oddLegOfIncidence (x : Incidence) : OddLeg := by
  refine ⟨x.1.2, ?_, ?_⟩
  · have hc4 : 4 ≤ x.1.1 := x.2.1
    rcases x.2.2.2 with h | h <;> omega
  · have htwoFour : 2 ∣ (4 : ℕ) := by norm_num
    have hcTwo : 2 ∣ x.1.1 := htwoFour.trans x.2.2.1
    have hcEven : Even x.1.1 := even_iff_two_dvd.mpr hcTwo
    rcases x.2.2.2 with h | h
    · rw [h]
      exact Nat.Even.sub_odd (by omega) hcEven odd_one
    · rw [h]
      exact hcEven.add_one

/--
Bijeção combinatoria exata da ponte C2: cada perna impar `n >= 3` corresponde
a uma unica incidencia `(centro multiplo de 4, n)`, e reciprocamente.
-/
def oddLegEquivIncidence : OddLeg ≃ Incidence where
  toFun := incidenceOfOddLeg
  invFun := oddLegOfIncidence
  left_inv n := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · change adjacentCenter x.1.2 = x.1.1
      exact adjacentCenter_unique
        (oddLegOfIncidence x).2.1 x.2.2.1 x.2.2.2
    · rfl

end CPFormal.Carry.C2
