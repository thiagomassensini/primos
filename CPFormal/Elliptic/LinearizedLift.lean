import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Linearized lift fibers for affine elliptic congruence cameras

This file kernel-checks the finite local counting mechanism isolated by the
elliptic-congruence experiments.  For a prime `p`, a residual quotient `c` and
a gradient `(gx, gy)` in `ZMod p`, the first-order lift equation is

```text
c + u * gx + v * gy = 0.
```

The solution fiber has exactly one of the three cardinalities

```text
p, 0, p^2.
```

A nonzero gradient gives exactly `p` solutions.  A zero gradient gives either
no solution or every pair, according to whether `c` is nonzero or zero.  The
file also proves that deviation from the regular cardinality `p` is equivalent
to vanishing of both gradient coordinates.

This is the abstract linearized local gate.  It does not yet identify this
fiber with the raw lift fiber of a displayed Weierstrass equation modulo
`p^(k+1)`, and it contains no projective group law or global elliptic claim.
-/

set_option autoImplicit false

namespace CPFormal.Elliptic

noncomputable section

/-- Solutions of the linearized two-coordinate lift equation over `ZMod p`. -/
def LinearizedLiftFiber (p : ℕ) (c gx gy : ZMod p) : Type :=
  {uv : ZMod p × ZMod p // c + uv.1 * gx + uv.2 * gy = 0}

/-- The linearized solution fiber is finite over a prime residue field. -/
noncomputable instance linearizedLiftFiberFintype
    (p : ℕ) [Fact (Nat.Prime p)] (c gx gy : ZMod p) :
    Fintype (LinearizedLiftFiber p c gx gy) :=
  Fintype.ofFinite _

/-- The finite field `ZMod p` has exactly `p` elements when `p` is prime. -/
theorem card_zmod_prime (p : ℕ) [Fact (Nat.Prime p)] :
    Fintype.card (ZMod p) = p := by
  simpa using Fintype.card_congr (ZMod.finEquiv p).toEquiv.symm

/--
If the first gradient coordinate is nonzero, the second coordinate freely
parametrizes the complete lift fiber.
-/
def linearizedLiftFiberEquivOfGxNeZero
    (p : ℕ) [Fact (Nat.Prime p)]
    (c gx gy : ZMod p) (hx : gx ≠ 0) :
    ZMod p ≃ LinearizedLiftFiber p c gx gy := by
  refine
    { toFun := fun v =>
        ⟨(-(c + v * gy) / gx, v), ?_⟩
      invFun := fun uv => uv.1.2
      left_inv := by
        intro v
        rfl
      right_inv := ?_ }
  · change c + (-(c + v * gy) / gx) * gx + v * gy = 0
    rw [div_mul_cancel₀ _ hx]
    ring
  · intro uv
    apply Subtype.ext
    apply Prod.ext
    · apply (div_eq_iff hx).2
      have hEq : c + uv.1.1 * gx + uv.1.2 * gy = 0 := uv.2
      linear_combination -hEq
    · rfl

/--
If the second gradient coordinate is nonzero, the first coordinate freely
parametrizes the complete lift fiber.
-/
def linearizedLiftFiberEquivOfGyNeZero
    (p : ℕ) [Fact (Nat.Prime p)]
    (c gx gy : ZMod p) (hy : gy ≠ 0) :
    ZMod p ≃ LinearizedLiftFiber p c gx gy := by
  refine
    { toFun := fun u =>
        ⟨(u, -(c + u * gx) / gy), ?_⟩
      invFun := fun uv => uv.1.1
      left_inv := by
        intro u
        rfl
      right_inv := ?_ }
  · change c + u * gx + (-(c + u * gx) / gy) * gy = 0
    rw [div_mul_cancel₀ _ hy]
    ring
  · intro uv
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply (div_eq_iff hy).2
      have hEq : c + uv.1.1 * gx + uv.1.2 * gy = 0 := uv.2
      linear_combination -hEq

/-- A nonzero first gradient coordinate gives exactly `p` lifts. -/
theorem card_linearizedLiftFiber_of_gx_ne_zero
    (p : ℕ) [Fact (Nat.Prime p)]
    (c gx gy : ZMod p) (hx : gx ≠ 0) :
    Fintype.card (LinearizedLiftFiber p c gx gy) = p := by
  calc
    Fintype.card (LinearizedLiftFiber p c gx gy) =
        Fintype.card (ZMod p) :=
      Fintype.card_congr
        (linearizedLiftFiberEquivOfGxNeZero p c gx gy hx).symm
    _ = p := card_zmod_prime p

/-- A nonzero second gradient coordinate gives exactly `p` lifts. -/
theorem card_linearizedLiftFiber_of_gy_ne_zero
    (p : ℕ) [Fact (Nat.Prime p)]
    (c gx gy : ZMod p) (hy : gy ≠ 0) :
    Fintype.card (LinearizedLiftFiber p c gx gy) = p := by
  calc
    Fintype.card (LinearizedLiftFiber p c gx gy) =
        Fintype.card (ZMod p) :=
      Fintype.card_congr
        (linearizedLiftFiberEquivOfGyNeZero p c gx gy hy).symm
    _ = p := card_zmod_prime p

/-- A zero gradient and zero residual quotient make every pair a lift. -/
theorem card_linearizedLiftFiber_of_gradient_zero_of_residual_zero
    (p : ℕ) [Fact (Nat.Prime p)]
    (c gx gy : ZMod p)
    (hx : gx = 0) (hy : gy = 0) (hc : c = 0) :
    Fintype.card (LinearizedLiftFiber p c gx gy) = p ^ 2 := by
  subst gx
  subst gy
  subst c
  simp [LinearizedLiftFiber, card_zmod_prime, Fintype.card_prod, pow_two]

/-- A zero gradient and nonzero residual quotient leave no lift. -/
theorem card_linearizedLiftFiber_of_gradient_zero_of_residual_ne_zero
    (p : ℕ) [Fact (Nat.Prime p)]
    (c gx gy : ZMod p)
    (hx : gx = 0) (hy : gy = 0) (hc : c ≠ 0) :
    Fintype.card (LinearizedLiftFiber p c gx gy) = 0 := by
  rw [Fintype.card_eq_zero_iff]
  refine ⟨?_⟩
  intro uv
  apply hc
  simpa [LinearizedLiftFiber, hx, hy] using uv.2

/-- The complete local cardinality trichotomy `p / 0 / p^2`. -/
theorem card_linearizedLiftFiber_trichotomy
    (p : ℕ) [Fact (Nat.Prime p)]
    (c gx gy : ZMod p) :
    Fintype.card (LinearizedLiftFiber p c gx gy) = p ∨
      Fintype.card (LinearizedLiftFiber p c gx gy) = 0 ∨
      Fintype.card (LinearizedLiftFiber p c gx gy) = p ^ 2 := by
  by_cases hx : gx = 0
  · by_cases hy : gy = 0
    · by_cases hc : c = 0
      · exact Or.inr <| Or.inr <|
          card_linearizedLiftFiber_of_gradient_zero_of_residual_zero
            p c gx gy hx hy hc
      · exact Or.inr <| Or.inl <|
          card_linearizedLiftFiber_of_gradient_zero_of_residual_ne_zero
            p c gx gy hx hy hc
    · exact Or.inl <|
        card_linearizedLiftFiber_of_gy_ne_zero p c gx gy hy
  · exact Or.inl <|
      card_linearizedLiftFiber_of_gx_ne_zero p c gx gy hx

/-- For a prime `p`, the exceptional cardinality `p^2` is not regular `p`. -/
theorem prime_sq_ne_self (p : ℕ) [Fact (Nat.Prime p)] : p ^ 2 ≠ p := by
  have hp : Nat.Prime p := Fact.out
  have hlt : p < p ^ 2 := by
    calc
      p = p * 1 := by simp
      _ < p * p := mul_lt_mul_of_pos_left hp.one_lt hp.pos
      _ = p ^ 2 := by simp [pow_two]
  exact ne_of_gt hlt

/--
The linearized fiber is defective precisely when both gradient coordinates
vanish.  The residual quotient selects between the two exceptional sizes but
does not change their support.
-/
theorem card_ne_expected_iff_gradient_zero
    (p : ℕ) [Fact (Nat.Prime p)]
    (c gx gy : ZMod p) :
    Fintype.card (LinearizedLiftFiber p c gx gy) ≠ p ↔
      gx = 0 ∧ gy = 0 := by
  constructor
  · intro hdefect
    by_cases hx : gx = 0
    · refine ⟨hx, ?_⟩
      by_contra hy
      exact hdefect <|
        card_linearizedLiftFiber_of_gy_ne_zero p c gx gy hy
    · exfalso
      exact hdefect <|
        card_linearizedLiftFiber_of_gx_ne_zero p c gx gy hx
  · rintro ⟨hx, hy⟩
    by_cases hc : c = 0
    · rw [card_linearizedLiftFiber_of_gradient_zero_of_residual_zero
          p c gx gy hx hy hc]
      exact prime_sq_ne_self p
    · rw [card_linearizedLiftFiber_of_gradient_zero_of_residual_ne_zero
          p c gx gy hx hy hc]
      exact ((Fact.out : Nat.Prime p).ne_zero).symm

end

end CPFormal.Elliptic
