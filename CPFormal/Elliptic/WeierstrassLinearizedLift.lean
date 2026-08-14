import CPFormal.Elliptic.CoprimeState
import CPFormal.Elliptic.LinearizedLift

/-!
# Linearized lift fibers for short-Weierstrass states

This file specializes the abstract two-coordinate lift equation to the
displayed affine short-Weierstrass model

```text
y^2 = x^3 + a*x + b.
```

For a state modulo a prime `p`, the two gradient coordinates are

```text
F_x = -3*x^2 - a,
F_y =  2*y.
```

The local residual quotient `c : ZMod p` selects between the two exceptional
singular fibers, but the support of every non-regular fiber is exactly the
vanishing support of `(F_x,F_y)`.  Thus the finite linearized camera has the
exact cardinality trichotomy `p / 0 / p^2`, with defective support equal to the
singular-gradient support.

This module formalizes the linearized camera.  The separate integer Taylor
bridge identifying raw lifts modulo `p^(k+1)` with this equation is not asserted
here.
-/

set_option autoImplicit false

namespace CPFormal.Elliptic

noncomputable section

/-- The `x` coordinate of the gradient of the short-Weierstrass residual. -/
def shortWeierstrassGradientX
    (p : ℕ) (a : ℤ) (x : ZMod p) : ZMod p :=
  (-3 : ZMod p) * x ^ 2 - (a : ZMod p)

/-- The `y` coordinate of the gradient of the short-Weierstrass residual. -/
def shortWeierstrassGradientY
    (p : ℕ) (y : ZMod p) : ZMod p :=
  (2 : ZMod p) * y

/-- A displayed affine state is singular when both gradient coordinates vanish. -/
def IsAffineSingularState
    (p : ℕ) (a b : ℤ)
    (point : AffineCongruenceState p a b) : Prop :=
  shortWeierstrassGradientX p a point.1.1 = 0 ∧
    shortWeierstrassGradientY p point.1.2 = 0

/-- Linearized lift fiber attached to one affine Weierstrass state. -/
def WeierstrassLinearizedLiftFiber
    (p : ℕ) (a b : ℤ)
    (point : AffineCongruenceState p a b)
    (residualQuotient : ZMod p) : Type :=
  LinearizedLiftFiber p residualQuotient
    (shortWeierstrassGradientX p a point.1.1)
    (shortWeierstrassGradientY p point.1.2)

/-- Every specialized local fiber has cardinality `p`, `0`, or `p^2`. -/
theorem card_weierstrassLinearizedLiftFiber_trichotomy
    (p : ℕ) [Fact (Nat.Prime p)] (a b : ℤ)
    (point : AffineCongruenceState p a b)
    (residualQuotient : ZMod p) :
    Fintype.card
        (WeierstrassLinearizedLiftFiber
          p a b point residualQuotient) = p ∨
      Fintype.card
        (WeierstrassLinearizedLiftFiber
          p a b point residualQuotient) = 0 ∨
      Fintype.card
        (WeierstrassLinearizedLiftFiber
          p a b point residualQuotient) = p ^ 2 := by
  exact card_linearizedLiftFiber_trichotomy p residualQuotient
    (shortWeierstrassGradientX p a point.1.1)
    (shortWeierstrassGradientY p point.1.2)

/--
A Weierstrass linearized fiber is non-regular exactly at a singular affine
state.  The residual quotient decides `0` versus `p^2`, not the support.
-/
theorem card_weierstrassLinearizedLiftFiber_ne_expected_iff_singular
    (p : ℕ) [Fact (Nat.Prime p)] (a b : ℤ)
    (point : AffineCongruenceState p a b)
    (residualQuotient : ZMod p) :
    Fintype.card
        (WeierstrassLinearizedLiftFiber
          p a b point residualQuotient) ≠ p ↔
      IsAffineSingularState p a b point := by
  exact card_ne_expected_iff_gradient_zero p residualQuotient
    (shortWeierstrassGradientX p a point.1.1)
    (shortWeierstrassGradientY p point.1.2)

/-- A singular state with zero residual quotient has all `p^2` lifts. -/
theorem card_weierstrassLinearizedLiftFiber_of_singular_of_residual_zero
    (p : ℕ) [Fact (Nat.Prime p)] (a b : ℤ)
    (point : AffineCongruenceState p a b)
    (residualQuotient : ZMod p)
    (hsingular : IsAffineSingularState p a b point)
    (hresidual : residualQuotient = 0) :
    Fintype.card
        (WeierstrassLinearizedLiftFiber
          p a b point residualQuotient) = p ^ 2 := by
  exact card_linearizedLiftFiber_of_gradient_zero_of_residual_zero
    p residualQuotient
    (shortWeierstrassGradientX p a point.1.1)
    (shortWeierstrassGradientY p point.1.2)
    hsingular.1 hsingular.2 hresidual

/-- A singular state with nonzero residual quotient has no lift. -/
theorem card_weierstrassLinearizedLiftFiber_of_singular_of_residual_ne_zero
    (p : ℕ) [Fact (Nat.Prime p)] (a b : ℤ)
    (point : AffineCongruenceState p a b)
    (residualQuotient : ZMod p)
    (hsingular : IsAffineSingularState p a b point)
    (hresidual : residualQuotient ≠ 0) :
    Fintype.card
        (WeierstrassLinearizedLiftFiber
          p a b point residualQuotient) = 0 := by
  exact card_linearizedLiftFiber_of_gradient_zero_of_residual_ne_zero
    p residualQuotient
    (shortWeierstrassGradientX p a point.1.1)
    (shortWeierstrassGradientY p point.1.2)
    hsingular.1 hsingular.2 hresidual

end

end CPFormal.Elliptic
