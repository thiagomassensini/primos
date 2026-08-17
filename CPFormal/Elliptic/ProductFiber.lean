import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Fibers of product maps

This file proves the finite categorical identities behind coprime lift-fiber
factorization.  Fibers transport through commuting source and target
equivalences, and the fiber of a product map over a product point is
canonically equivalent to the product of the two component fibers.
Consequently, finite fiber cardinalities multiply exactly.

The theorems are deliberately independent of elliptic equations and CRT.  A
congruence-state bridge only has to prove that its reduction square commutes;
the fiber and cardinality conclusions then follow without new counting
arguments.
-/

set_option autoImplicit false

namespace CPFormal.Elliptic

/-- Fiber of a map above one target point. -/
def MapFiber {α β : Type*} (f : α → β) (y : β) :=
  {x : α // f x = y}

/-- A fiber of a map with finite source is finite. -/
noncomputable instance mapFiberFintype
    {α β : Type*} [Fintype α] (f : α → β) (y : β) :
    Fintype (MapFiber f y) :=
  Fintype.ofInjective
    (fun x : MapFiber f y => x.1)
    (by
      intro x x' h
      exact Subtype.ext h)

/-- Product of two maps. -/
def productMap {α β γ δ : Type*}
    (f : α → β) (g : γ → δ) : α × γ → β × δ :=
  fun x => (f x.1, g x.2)

/--
A commuting square with equivalences on source and target transports every
fiber to the corresponding fiber.
-/
def mapFiberEquivOfCommutingEquiv
    {α β γ δ : Type*}
    (f : α → β) (g : γ → δ)
    (sourceEquiv : α ≃ γ) (targetEquiv : β ≃ δ)
    (commutes : ∀ x, targetEquiv (f x) = g (sourceEquiv x))
    (y : β) :
    MapFiber f y ≃ MapFiber g (targetEquiv y) :=
  { toFun := fun x =>
      ⟨sourceEquiv x.1, by
        calc
          g (sourceEquiv x.1) = targetEquiv (f x.1) :=
            (commutes x.1).symm
          _ = targetEquiv y := congrArg targetEquiv x.2⟩
    invFun := fun x =>
      ⟨sourceEquiv.symm x.1, by
        apply targetEquiv.injective
        calc
          targetEquiv (f (sourceEquiv.symm x.1)) =
              g (sourceEquiv (sourceEquiv.symm x.1)) :=
            commutes (sourceEquiv.symm x.1)
          _ = g x.1 := by rw [sourceEquiv.apply_symm_apply]
          _ = targetEquiv y := x.2⟩
    left_inv := fun x => by
      apply Subtype.ext
      exact sourceEquiv.symm_apply_apply x.1
    right_inv := fun x => by
      apply Subtype.ext
      exact sourceEquiv.apply_symm_apply x.1 }

/-- The fiber of a product map is the product of the component fibers. -/
def productMapFiberEquiv
    {α β γ δ : Type*}
    (f : α → β) (g : γ → δ) (y : β) (z : δ) :
    MapFiber (productMap f g) (y, z) ≃
      MapFiber f y × MapFiber g z :=
  { toFun := fun x =>
      (⟨x.1.1, by
          simpa [productMap] using congrArg Prod.fst x.2⟩,
        ⟨x.1.2, by
          simpa [productMap] using congrArg Prod.snd x.2⟩)
    invFun := fun x =>
      ⟨(x.1.1, x.2.1), by
        apply Prod.ext
        · exact x.1.2
        · exact x.2.2⟩
    left_inv := fun x => by
      apply Subtype.ext
      rfl
    right_inv := fun x => by
      apply Prod.ext
      · apply Subtype.ext
        rfl
      · apply Subtype.ext
        rfl }

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
