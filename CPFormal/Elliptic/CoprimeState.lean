import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Coprime factorization of affine Weierstrass congruence states

For coprime natural numbers `m` and `n`, the Chinese remainder equivalence on
`ZMod (m*n)` is applied coordinatewise to the affine short-Weierstrass
congruence

```text
y^2 = x^3 + a*x + b.
```

The resulting theorem identifies the state type modulo `m*n` with the product
of the state types modulo `m` and modulo `n`.  Finite state cardinalities then
factor exactly.

This file concerns a displayed affine integral model.  It does not yet prove
covariance under changes of Weierstrass coordinates or add the projective point
at infinity.
-/

set_option autoImplicit false

namespace CPFormal.Elliptic

noncomputable section

/-- Residual of the displayed short-Weierstrass equation over `ZMod modulus`. -/
def shortWeierstrassResidual
    (a b : ℤ) {modulus : ℕ}
    (point : ZMod modulus × ZMod modulus) : ZMod modulus :=
  point.2 ^ 2 -
    (point.1 ^ 3 + (a : ZMod modulus) * point.1 + (b : ZMod modulus))

/-- Affine congruence states of a displayed short-Weierstrass model. -/
def AffineCongruenceState (modulus : ℕ) (a b : ℤ) : Type :=
  {point : ZMod modulus × ZMod modulus //
    shortWeierstrassResidual a b point = 0}

/-- Affine congruence states are finite for a nonzero modulus. -/
noncomputable instance affineCongruenceStateFintype
    (modulus : ℕ) [NeZero modulus] (a b : ℤ) :
    Fintype (AffineCongruenceState modulus a b) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Coordinatewise Chinese remainder equivalence for affine plane points. -/
def crtPointEquiv
    {m n : ℕ} (h : m.Coprime n) :
    (ZMod (m * n) × ZMod (m * n)) ≃
      (ZMod m × ZMod m) × (ZMod n × ZMod n) := by
  let crt := ZMod.chineseRemainder h
  refine
    { toFun := fun point =>
        (((crt point.1).1, (crt point.2).1),
          ((crt point.1).2, (crt point.2).2))
      invFun := fun point =>
        (crt.symm (point.1.1, point.2.1),
          crt.symm (point.1.2, point.2.2))
      left_inv := ?_
      right_inv := ?_ }
  · intro point
    apply Prod.ext <;> simp [crt]
  · rintro ⟨⟨xm, ym⟩, ⟨xn, yn⟩⟩
    simp [crt]

/-- The first CRT component preserves the Weierstrass residual. -/
@[simp]
theorem shortWeierstrassResidual_crtPointEquiv_fst
    {m n : ℕ} (h : m.Coprime n) (a b : ℤ)
    (point : ZMod (m * n) × ZMod (m * n)) :
    shortWeierstrassResidual a b ((crtPointEquiv h point).1) =
      ((ZMod.chineseRemainder h)
        (shortWeierstrassResidual a b point)).1 := by
  simp [shortWeierstrassResidual, crtPointEquiv]

/-- The second CRT component preserves the Weierstrass residual. -/
@[simp]
theorem shortWeierstrassResidual_crtPointEquiv_snd
    {m n : ℕ} (h : m.Coprime n) (a b : ℤ)
    (point : ZMod (m * n) × ZMod (m * n)) :
    shortWeierstrassResidual a b ((crtPointEquiv h point).2) =
      ((ZMod.chineseRemainder h)
        (shortWeierstrassResidual a b point)).2 := by
  simp [shortWeierstrassResidual, crtPointEquiv]

/--
Affine congruence states modulo a coprime product are exactly pairs of local
states.
-/
def affineCongruenceStateCrtEquiv
    {m n : ℕ} (h : m.Coprime n) (a b : ℤ) :
    AffineCongruenceState (m * n) a b ≃
      AffineCongruenceState m a b × AffineCongruenceState n a b := by
  let pointEquiv := crtPointEquiv h
  refine
    { toFun := fun point =>
        (⟨(pointEquiv point.1).1, ?_⟩,
          ⟨(pointEquiv point.1).2, ?_⟩)
      invFun := fun point =>
        ⟨pointEquiv.symm (point.1.1, point.2.1), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [shortWeierstrassResidual_crtPointEquiv_fst]
    rw [point.2]
    simp
  · rw [shortWeierstrassResidual_crtPointEquiv_snd]
    rw [point.2]
    simp
  · apply (ZMod.chineseRemainder h).injective
    apply Prod.ext
    · simpa [pointEquiv, crtPointEquiv, shortWeierstrassResidual]
        using point.1.2
    · simpa [pointEquiv, crtPointEquiv, shortWeierstrassResidual]
        using point.2.2
  · intro point
    apply Subtype.ext
    exact pointEquiv.symm_apply_apply point.1
  · intro point
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst
        (pointEquiv.apply_symm_apply (point.1.1, point.2.1))
    · apply Subtype.ext
      exact congrArg Prod.snd
        (pointEquiv.apply_symm_apply (point.1.1, point.2.1))

/-- Finite affine state counts factor over coprime nonzero moduli. -/
theorem card_affineCongruenceState_mul
    (m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n) (a b : ℤ) :
    Fintype.card (AffineCongruenceState (m * n) a b) =
      Fintype.card (AffineCongruenceState m a b) *
        Fintype.card (AffineCongruenceState n a b) := by
  calc
    Fintype.card (AffineCongruenceState (m * n) a b) =
        Fintype.card
          (AffineCongruenceState m a b × AffineCongruenceState n a b) :=
      Fintype.card_congr (affineCongruenceStateCrtEquiv h a b)
    _ = Fintype.card (AffineCongruenceState m a b) *
        Fintype.card (AffineCongruenceState n a b) :=
      Fintype.card_prod _ _

end

end CPFormal.Elliptic
