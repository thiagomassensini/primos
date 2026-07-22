import Mathlib

/-!
# Shifts multiplicativos

Este e o primeiro esqueleto formal da planura multibase: subir pela vertical
`p` e depois pela vertical `q` produz o mesmo indice que inverter a ordem.
-/

namespace CPFormal

variable {A : Type*}

/-- Pullback de uma sequencia pelo mapa `n ↦ p*n`. -/
def mulShift (p : ℕ) (x : ℕ → A) : ℕ → A :=
  fun n ↦ x (p * n)

@[simp] theorem mulShift_one (x : ℕ → A) :
    mulShift 1 x = x := by
  funext n
  simp [mulShift]

theorem mulShift_comm (p q : ℕ) (x : ℕ → A) :
    mulShift p (mulShift q x) = mulShift q (mulShift p x) := by
  funext n
  simp [mulShift, Nat.mul_left_comm]

end CPFormal
