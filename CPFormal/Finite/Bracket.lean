import CPFormal.Finite.SymmetricPair
import Mathlib

/-!
# Bracket finito abstrato

Antes de introduzir `n^{-s}`, formalizamos a identidade puramente aditiva da
segunda diferenca. Isso separa cancelamento combinatorio de analise complexa.
-/

open scoped BigOperators

namespace CPFormal

variable {A : Type*} [AddCommGroup A]

/-- Segunda diferenca centrada com centro e raio inteiros. -/
def centeredSecondDifference (f : ℤ → A) (center radius : ℤ) : A :=
  f (center - radius) - (2 • f center) + f (center + radius)

@[simp] theorem centeredSecondDifference_zero (center radius : ℤ) :
    centeredSecondDifference (fun _ : ℤ ↦ (0 : A)) center radius = 0 := by
  simp [centeredSecondDifference]

theorem centeredSecondDifference_neg_radius
    (f : ℤ → A) (center radius : ℤ) :
    centeredSecondDifference f center (-radius) =
      centeredSecondDifference f center radius := by
  simp [centeredSecondDifference, sub_eq_add_neg, add_comm, add_left_comm,
    add_assoc]

theorem centeredSecondDifference_add
    (f g : ℤ → A) (center radius : ℤ) :
    centeredSecondDifference (fun n ↦ f n + g n) center radius =
      centeredSecondDifference f center radius +
        centeredSecondDifference g center radius := by
  simp only [centeredSecondDifference, nsmul_add]
  abel

/-- Soma das segundas diferencas para raios `1, ..., h`. -/
def saturatedBracket (h : ℕ) (f : ℤ → A) (center : ℤ) : A :=
  ∑ radius ∈ Finset.Icc 1 h,
    centeredSecondDifference f center (radius : ℤ)

@[simp] theorem saturatedBracket_zero (h : ℕ) (center : ℤ) :
    saturatedBracket h (fun _ : ℤ ↦ (0 : A)) center = 0 := by
  simp [saturatedBracket]

theorem saturatedBracket_add
    (h : ℕ) (f g : ℤ → A) (center : ℤ) :
    saturatedBracket h (fun n ↦ f n + g n) center =
      saturatedBracket h f center + saturatedBracket h g center := by
  simp [saturatedBracket, centeredSecondDifference_add]

end CPFormal
