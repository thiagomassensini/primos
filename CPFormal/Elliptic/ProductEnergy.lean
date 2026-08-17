import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Product profiles and quadratic lift-fiber energy

This file formalizes the algebraic layer behind coprime-camera energy
inheritance.  A finite camera profile assigns a natural lift count to each
state.  Its defect is the integer difference from the regular count, and its
energy is the sum of squared defects.

For product states, the product profile multiplies the two component lift
counts.  The file proves the exact double-sum formula and the scaling law used
when one component camera is regular:

```text
E_(ab) = card(X_b) * b^2 * E_a.
```

No elliptic curve, CRT equivalence or raw congruence state is assumed here;
those enter through separate bridge modules.
-/

set_option autoImplicit false

namespace CPFormal.Elliptic

open scoped BigOperators

/-- Integer deviation of a fiber count from its regular expected size. -/
def fiberDefect (expected count : ℕ) : ℤ :=
  (count : ℤ) - (expected : ℤ)

/-- Quadratic defect energy of a finite lift-count profile. -/
def fiberEnergy {α : Type*} [Fintype α]
    (expected : ℕ) (profile : α → ℕ) : ℤ :=
  ∑ x, fiberDefect expected (profile x) ^ 2

/-- Pointwise product of two finite camera lift-count profiles. -/
def productFiberProfile {α β : Type*}
    (left : α → ℕ) (right : β → ℕ) : α × β → ℕ :=
  fun xy => left xy.1 * right xy.2

/-- The product-camera energy is literally the double sum over both states. -/
theorem fiberEnergy_product_exact
    {α β : Type*} [Fintype α] [Fintype β]
    (a b : ℕ) (left : α → ℕ) (right : β → ℕ) :
    fiberEnergy (a * b) (productFiberProfile left right) =
      ∑ x : α, ∑ y : β,
        fiberDefect (a * b) (left x * right y) ^ 2 := by
  rw [fiberEnergy, Fintype.sum_prod_type]
  rfl

/--
When the right fiber is regular, the product defect is the left defect scaled
by the right expected size.
-/
theorem fiberDefect_product_right_regular
    {α β : Type*}
    (a b : ℕ) (left : α → ℕ) (right : β → ℕ)
    (x : α) (y : β) (hy : right y = b) :
    fiberDefect (a * b) (productFiberProfile left right (x, y)) =
      (b : ℤ) * fiberDefect a (left x) := by
  simp [fiberDefect, productFiberProfile, hy]
  ring

/--
When the left fiber is regular, the product defect is the right defect scaled
by the left expected size.
-/
theorem fiberDefect_product_left_regular
    {α β : Type*}
    (a b : ℕ) (left : α → ℕ) (right : β → ℕ)
    (x : α) (y : β) (hx : left x = a) :
    fiberDefect (a * b) (productFiberProfile left right (x, y)) =
      (a : ℤ) * fiberDefect b (right y) := by
  simp [fiberDefect, productFiberProfile, hx]
  ring

/--
If the right camera is regular at every state, product energy is the left
energy multiplied by the right population and the square of its regular fiber
size.
-/
theorem fiberEnergy_product_right_regular
    {α β : Type*} [Fintype α] [Fintype β]
    (a b : ℕ) (left : α → ℕ) (right : β → ℕ)
    (hright : ∀ y, right y = b) :
    fiberEnergy (a * b) (productFiberProfile left right) =
      (Fintype.card β : ℤ) * (b : ℤ) ^ 2 * fiberEnergy a left := by
  rw [fiberEnergy, Fintype.sum_prod_type]
  have hpoint : ∀ (x : α) (y : β),
      fiberDefect (a * b) (productFiberProfile left right (x, y)) =
        (b : ℤ) * fiberDefect a (left x) := by
    intro x y
    exact fiberDefect_product_right_regular
      a b left right x y (hright y)
  simp_rw [hpoint, mul_pow]
  calc
    (∑ x : α, ∑ _y : β,
        (b : ℤ) ^ 2 * fiberDefect a (left x) ^ 2) =
        ∑ x : α, (Fintype.card β : ℤ) *
          ((b : ℤ) ^ 2 * fiberDefect a (left x) ^ 2) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp
    _ = ∑ x : α,
        ((Fintype.card β : ℤ) * (b : ℤ) ^ 2) *
          fiberDefect a (left x) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = ((Fintype.card β : ℤ) * (b : ℤ) ^ 2) *
        ∑ x : α, fiberDefect a (left x) ^ 2 := by
      rw [Finset.mul_sum]

/-- Symmetric scaling law when the left camera is regular. -/
theorem fiberEnergy_product_left_regular
    {α β : Type*} [Fintype α] [Fintype β]
    (a b : ℕ) (left : α → ℕ) (right : β → ℕ)
    (hleft : ∀ x, left x = a) :
    fiberEnergy (a * b) (productFiberProfile left right) =
      (Fintype.card α : ℤ) * (a : ℤ) ^ 2 * fiberEnergy b right := by
  rw [fiberEnergy, Fintype.sum_prod_type]
  have hpoint : ∀ (x : α) (y : β),
      fiberDefect (a * b) (productFiberProfile left right (x, y)) =
        (a : ℤ) * fiberDefect b (right y) := by
    intro x y
    exact fiberDefect_product_left_regular
      a b left right x y (hleft x)
  simp_rw [hpoint, mul_pow]
  calc
    (∑ _x : α, ∑ y : β,
        (a : ℤ) ^ 2 * fiberDefect b (right y) ^ 2) =
        (Fintype.card α : ℤ) *
          ∑ y : β, (a : ℤ) ^ 2 * fiberDefect b (right y) ^ 2 := by
      simp
    _ = (Fintype.card α : ℤ) * (a : ℤ) ^ 2 *
        ∑ y : β, fiberDefect b (right y) ^ 2 := by
      rw [← Finset.mul_sum]
      ring

end CPFormal.Elliptic
