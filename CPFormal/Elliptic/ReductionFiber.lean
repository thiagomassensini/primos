import CPFormal.Elliptic.CoprimeState
import CPFormal.Elliptic.ProductFiber

/-!
# Reduction fibers under coprime factorization

This file connects the abstract product-fiber theorem to affine
short-Weierstrass congruence states.  Canonical reduction along a divisor is
defined coordinatewise with `ZMod.castHom`.  The reduction square commutes with
the Chinese remainder state equivalences, so every composite reduction fiber
is canonically equivalent to the product of its two local reduction fibers.

This is the exact finite CRT lift-fiber identity.  It remains attached to the
displayed affine integral model and does not add projective or global elliptic
semantics.
-/

set_option autoImplicit false

namespace CPFormal.Elliptic

noncomputable section

/-- Canonical reduction from a larger residue ring to a divisor modulus. -/
def zmodReduction {small large : ℕ} (h : small ∣ large) :
    ZMod large →+* ZMod small :=
  ZMod.castHom h (ZMod small)

/-- Coordinatewise reduction of an affine residue-plane point. -/
def zmodPointReduction {small large : ℕ} (h : small ∣ large) :
    (ZMod large × ZMod large) → (ZMod small × ZMod small) :=
  fun point => (zmodReduction h point.1, zmodReduction h point.2)

/-- Weierstrass residuals commute with canonical modular reduction. -/
@[simp]
theorem shortWeierstrassResidual_zmodPointReduction
    {small large : ℕ} (h : small ∣ large) (a b : ℤ)
    (point : ZMod large × ZMod large) :
    shortWeierstrassResidual a b (zmodPointReduction h point) =
      zmodReduction h (shortWeierstrassResidual a b point) := by
  simp [shortWeierstrassResidual, zmodPointReduction]

/-- Reduction of affine congruence states along a divisor of moduli. -/
def affineCongruenceStateReduction
    {small large : ℕ} (h : small ∣ large) (a b : ℤ) :
    AffineCongruenceState large a b →
      AffineCongruenceState small a b :=
  fun point =>
    ⟨zmodPointReduction h point.1, by
      rw [shortWeierstrassResidual_zmodPointReduction]
      rw [point.2]
      simp⟩

/-- Ring-level CRT commutes with canonical reductions in both components. -/
theorem zmodReduction_chineseRemainder
    {mSmall mLarge nSmall nLarge : ℕ}
    (hm : mSmall ∣ mLarge) (hn : nSmall ∣ nLarge)
    (hSmall : mSmall.Coprime nSmall)
    (hLarge : mLarge.Coprime nLarge)
    (hProduct : mSmall * nSmall ∣ mLarge * nLarge)
    (x : ZMod (mLarge * nLarge)) :
    (ZMod.chineseRemainder hSmall) (zmodReduction hProduct x) =
      (zmodReduction hm ((ZMod.chineseRemainder hLarge x).1),
        zmodReduction hn ((ZMod.chineseRemainder hLarge x).2)) := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
  apply Prod.ext <;> simp [zmodReduction]

/-- The affine-state reduction square commutes with both CRT equivalences. -/
theorem affineCongruenceStateReduction_crt_commutes
    {mSmall mLarge nSmall nLarge : ℕ}
    (hm : mSmall ∣ mLarge) (hn : nSmall ∣ nLarge)
    (hSmall : mSmall.Coprime nSmall)
    (hLarge : mLarge.Coprime nLarge)
    (hProduct : mSmall * nSmall ∣ mLarge * nLarge)
    (a b : ℤ)
    (point : AffineCongruenceState (mLarge * nLarge) a b) :
    affineCongruenceStateCrtEquiv hSmall a b
        (affineCongruenceStateReduction hProduct a b point) =
      productMap
        (affineCongruenceStateReduction hm a b)
        (affineCongruenceStateReduction hn a b)
        (affineCongruenceStateCrtEquiv hLarge a b point) := by
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · simpa [affineCongruenceStateReduction, zmodPointReduction,
        affineCongruenceStateCrtEquiv, crtPointEquiv, productMap]
        using congrArg Prod.fst
          (zmodReduction_chineseRemainder
            hm hn hSmall hLarge hProduct point.1.1)
    · simpa [affineCongruenceStateReduction, zmodPointReduction,
        affineCongruenceStateCrtEquiv, crtPointEquiv, productMap]
        using congrArg Prod.fst
          (zmodReduction_chineseRemainder
            hm hn hSmall hLarge hProduct point.1.2)
  · apply Subtype.ext
    apply Prod.ext
    · simpa [affineCongruenceStateReduction, zmodPointReduction,
        affineCongruenceStateCrtEquiv, crtPointEquiv, productMap]
        using congrArg Prod.snd
          (zmodReduction_chineseRemainder
            hm hn hSmall hLarge hProduct point.1.1)
    · simpa [affineCongruenceStateReduction, zmodPointReduction,
        affineCongruenceStateCrtEquiv, crtPointEquiv, productMap]
        using congrArg Prod.snd
          (zmodReduction_chineseRemainder
            hm hn hSmall hLarge hProduct point.1.2)

/--
A composite affine reduction fiber is canonically the product of the two local
reduction fibers.
-/
def affineCongruenceReductionFiberCrtEquiv
    {mSmall mLarge nSmall nLarge : ℕ}
    (hm : mSmall ∣ mLarge) (hn : nSmall ∣ nLarge)
    (hSmall : mSmall.Coprime nSmall)
    (hLarge : mLarge.Coprime nLarge)
    (hProduct : mSmall * nSmall ∣ mLarge * nLarge)
    (a b : ℤ)
    (target : AffineCongruenceState (mSmall * nSmall) a b) :
    MapFiber
        (affineCongruenceStateReduction hProduct a b)
        target ≃
      MapFiber
          (affineCongruenceStateReduction hm a b)
          ((affineCongruenceStateCrtEquiv hSmall a b target).1) ×
        MapFiber
          (affineCongruenceStateReduction hn a b)
          ((affineCongruenceStateCrtEquiv hSmall a b target).2) := by
  let sourceEquiv := affineCongruenceStateCrtEquiv hLarge a b
  let targetEquiv := affineCongruenceStateCrtEquiv hSmall a b
  let leftReduction := affineCongruenceStateReduction hm a b
  let rightReduction := affineCongruenceStateReduction hn a b
  let compositeReduction :=
    affineCongruenceStateReduction hProduct a b
  exact
    (mapFiberEquivOfCommutingEquiv
      compositeReduction
      (productMap leftReduction rightReduction)
      sourceEquiv targetEquiv
      (affineCongruenceStateReduction_crt_commutes
        hm hn hSmall hLarge hProduct a b)
      target).trans
      (productMapFiberEquiv
        leftReduction rightReduction
        (targetEquiv target).1 (targetEquiv target).2)

/-- Finite composite reduction-fiber cardinalities multiply exactly. -/
theorem card_affineCongruenceReductionFiber_mul
    {mSmall mLarge nSmall nLarge : ℕ}
    [NeZero (mLarge * nLarge)] [NeZero mLarge] [NeZero nLarge]
    (hm : mSmall ∣ mLarge) (hn : nSmall ∣ nLarge)
    (hSmall : mSmall.Coprime nSmall)
    (hLarge : mLarge.Coprime nLarge)
    (hProduct : mSmall * nSmall ∣ mLarge * nLarge)
    (a b : ℤ)
    (target : AffineCongruenceState (mSmall * nSmall) a b) :
    Fintype.card
        (MapFiber
          (affineCongruenceStateReduction hProduct a b)
          target) =
      Fintype.card
          (MapFiber
            (affineCongruenceStateReduction hm a b)
            ((affineCongruenceStateCrtEquiv hSmall a b target).1)) *
        Fintype.card
          (MapFiber
            (affineCongruenceStateReduction hn a b)
            ((affineCongruenceStateCrtEquiv hSmall a b target).2)) := by
  calc
    Fintype.card
        (MapFiber
          (affineCongruenceStateReduction hProduct a b)
          target) =
        Fintype.card
          (MapFiber
              (affineCongruenceStateReduction hm a b)
              ((affineCongruenceStateCrtEquiv hSmall a b target).1) ×
            MapFiber
              (affineCongruenceStateReduction hn a b)
              ((affineCongruenceStateCrtEquiv hSmall a b target).2)) :=
      Fintype.card_congr
        (affineCongruenceReductionFiberCrtEquiv
          hm hn hSmall hLarge hProduct a b target)
    _ = Fintype.card
          (MapFiber
            (affineCongruenceStateReduction hm a b)
            ((affineCongruenceStateCrtEquiv hSmall a b target).1)) *
        Fintype.card
          (MapFiber
            (affineCongruenceStateReduction hn a b)
            ((affineCongruenceStateCrtEquiv hSmall a b target).2)) :=
      Fintype.card_prod _ _

end

end CPFormal.Elliptic
