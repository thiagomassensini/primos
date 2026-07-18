import Mathlib

/-!
# Pares simetricos em torno de um centro

Esta e a unidade combinatoria anterior ao bracket: duas pernas `c-r` e `c+r`
compartilham o mesmo centro.
-/

namespace CPFormal

structure SymmetricPair where
  center : ℤ
  radius : ℤ
  deriving Repr, DecidableEq

namespace SymmetricPair

def left (pair : SymmetricPair) : ℤ :=
  pair.center - pair.radius

def right (pair : SymmetricPair) : ℤ :=
  pair.center + pair.radius

def reflected (pair : SymmetricPair) : SymmetricPair :=
  ⟨pair.center, -pair.radius⟩

@[simp] theorem left_add_right (pair : SymmetricPair) :
    pair.left + pair.right = 2 * pair.center := by
  simp [left, right]
  ring

@[simp] theorem reflected_left (pair : SymmetricPair) :
    pair.reflected.left = pair.right := by
  simp [reflected, left, right]

@[simp] theorem reflected_right (pair : SymmetricPair) :
    pair.reflected.right = pair.left := by
  simp [reflected, left, right]

end SymmetricPair
end CPFormal
