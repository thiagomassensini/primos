import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Fibers of product maps

This file proves the finite categorical identity behind coprime lift-fiber
factorization.  The fiber of a product map over a product point is canonically
equivalent to the product of the two component fibers.  Consequently, finite
fiber cardinalities multiply exactly.

The theorem is deliberately independent of elliptic equations and CRT.  A
later congruence-state bridge only has to identify its reduction map with a
product map; the fiber and cardinality conclusions then follow without new
counting arguments.
-/

set_option autoImplicit false

namespace CPFormal.Elliptic

/-- Fiber of a map above one target point. -/
def MapFiber {α β : Type*} (f : α → β) (y : β) : Type :=
  {x : α // f x = y}

/-- A fiber of a map with finite source is finite. -/
noncomputable instance mapFiberFintype
    {α β : Type*} [Fintype α] (f : α → β) (y : β) :
    Fintype (MapFiber f y) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Product of two maps. -/
def productMap {α β γ δ : Type*}
    (f : α → β) (g : γ → δ) : α × γ → β × δ :=
  fun x => (f x.1, g x.2)

/-- The fiber of a product map is the product of the component fibers. -/
def productMapFiberEquiv
    {α β γ δ : Type*}
    (f : α → β) (g : γ → δ) (y : β) (z : δ) :
    MapFiber (productMap f g) (y, z) ≃
      MapFiber f y × MapFiber g z := by
  refine
    { toFun := fun x =>
        (⟨x.1.1, ?_⟩, ⟨x.1.2, ?_⟩)
      invFun := fun x =>
        ⟨(x.1.1, x.2.1), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · simpa [productMap] using congrArg Prod.fst x.2
  · simpa [productMap] using congrArg Prod.snd x.2
  · apply Prod.ext
    · exact x.1.2
    · exact x.2.2
  · intro x
    apply Subtype.ext
    rfl
  · intro x
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl

/-- Finite product-map fibers have exactly multiplicative cardinality. -/
theorem card_productMapFiber
    {α β γ δ : Type*} [Fintype α] [Fintype γ]
    (f : α → β) (g : γ → δ) (y : β) (z : δ) :
    Fintype.card (MapFiber (productMap f g) (y, z)) =
      Fintype.card (MapFiber f y) * Fintype.card (MapFiber g z) := by
  calc
    Fintype.card (MapFiber (productMap f g) (y, z)) =
        Fintype.card (MapFiber f y × MapFiber g z) :=
      Fintype.card_congr (productMapFiberEquiv f g y z)
    _ = Fintype.card (MapFiber f y) * Fintype.card (MapFiber g z) :=
      Fintype.card_prod _ _

end CPFormal.Elliptic
