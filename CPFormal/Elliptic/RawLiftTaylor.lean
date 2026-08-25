import CPFormal.Elliptic.WeierstrassLinearizedLift
import Mathlib.Tactic

/-!
# Integral Taylor bridge for raw short-Weierstrass lifts

This file closes the first-order arithmetic bridge left open by the finite
elliptic camera gates.  For the displayed integral residual

```text
F(x,y) = y^2 - (x^3 + a*x + b),
```

it proves the exact polynomial identity at a shifted point

```text
(x + h*u, y + h*v).
```

Specializing `h = p^k`, with `k >= 1`, the higher-order remainder is divisible
by `p^(k+1)`.  If the base residual is written exactly as

```text
F(x,y) = p^k * c,
```

then the raw lift condition modulo `p^(k+1)` is equivalent to the linearized
condition modulo `p`:

```text
p^(k+1) | F(x + p^k*u, y + p^k*v)
  <->
p | c + u*Fx(x,y) + v*Fy(x,y).
```

The residual quotient `c` is carried by an equality rather than introduced by
integer division.  Thus no divisibility fact is hidden inside a definition.
The file then packages the theorem as an equivalence between the finite raw
increment fiber and the already kernel-checked `LinearizedLiftFiber`.

This remains attached to the displayed affine integral model.  It does not add
projective completion, model covariance, a group law or any global elliptic
claim.
-/

set_option autoImplicit false

namespace CPFormal.Elliptic

noncomputable section

/-- Integral residual of the displayed short-Weierstrass equation. -/
def shortWeierstrassResidualInt
    (a b x y : ℤ) : ℤ :=
  y ^ 2 - (x ^ 3 + a * x + b)

/-- Integral `x`-gradient of the short-Weierstrass residual. -/
def shortWeierstrassGradientXInt
    (a x : ℤ) : ℤ :=
  -3 * x ^ 2 - a

/-- Integral `y`-gradient of the short-Weierstrass residual. -/
def shortWeierstrassGradientYInt
    (y : ℤ) : ℤ :=
  2 * y

/-- First-order directional term in the increment `(u,v)`. -/
def shortWeierstrassLinearTermInt
    (a x y u v : ℤ) : ℤ :=
  u * shortWeierstrassGradientXInt a x +
    v * shortWeierstrassGradientYInt y

/-- Exact higher-order remainder after a shift by the common scale `h`. -/
def shortWeierstrassHigherOrderInt
    (h x u v : ℤ) : ℤ :=
  h ^ 2 * (v ^ 2 - 3 * x * u ^ 2 - h * u ^ 3)

/--
Exact polynomial expansion.  This is an identity in `ℤ`, not an asymptotic
statement and not a truncated series.
-/
theorem shortWeierstrassResidualInt_taylor
    (a b x y h u v : ℤ) :
    shortWeierstrassResidualInt a b (x + h * u) (y + h * v) =
      shortWeierstrassResidualInt a b x y +
        h * shortWeierstrassLinearTermInt a x y u v +
          shortWeierstrassHigherOrderInt h x u v := by
  simp [shortWeierstrassResidualInt,
    shortWeierstrassLinearTermInt,
    shortWeierstrassGradientXInt,
    shortWeierstrassGradientYInt,
    shortWeierstrassHigherOrderInt]
  ring

/-- The integral residual agrees with the residue-ring residual after casting. -/
@[simp]
theorem shortWeierstrassResidual_intCast
    (p : ℕ) (a b x y : ℤ) :
    shortWeierstrassResidual a b ((x : ZMod p), (y : ZMod p)) =
      (shortWeierstrassResidualInt a b x y : ZMod p) := by
  simp [shortWeierstrassResidual, shortWeierstrassResidualInt]

/-- The integral `x`-gradient agrees with the residue-ring gradient. -/
@[simp]
theorem shortWeierstrassGradientX_intCast
    (p : ℕ) (a x : ℤ) :
    shortWeierstrassGradientX p a (x : ZMod p) =
      (shortWeierstrassGradientXInt a x : ZMod p) := by
  simp [shortWeierstrassGradientX, shortWeierstrassGradientXInt]

/-- The integral `y`-gradient agrees with the residue-ring gradient. -/
@[simp]
theorem shortWeierstrassGradientY_intCast
    (p : ℕ) (y : ℤ) :
    shortWeierstrassGradientY p (y : ZMod p) =
      (shortWeierstrassGradientYInt y : ZMod p) := by
  simp [shortWeierstrassGradientY, shortWeierstrassGradientYInt]

/--
The exact raw-lift divisibility condition is the first-order condition modulo
`p`.  Positivity of the depth is essential: at depth zero the quadratic terms
need not disappear modulo `p`.
-/
theorem shortWeierstrassRawLift_dvd_iff
    (p k : ℕ) (hp : p ≠ 0) (hk : 1 ≤ k)
    (a b x y u v c : ℤ)
    (hbase :
      shortWeierstrassResidualInt a b x y = (p : ℤ) ^ k * c) :
    (p : ℤ) ^ (k + 1) ∣
        shortWeierstrassResidualInt a b
          (x + (p : ℤ) ^ k * u)
          (y + (p : ℤ) ^ k * v) ↔
      (p : ℤ) ∣ c + shortWeierstrassLinearTermInt a x y u v := by
  have hpz : (p : ℤ) ≠ 0 := by
    exact_mod_cast hp
  have hpk : (p : ℤ) ^ k ≠ 0 :=
    pow_ne_zero _ hpz
  let tail : ℤ :=
    v ^ 2 - 3 * x * u ^ 2 - (p : ℤ) ^ k * u ^ 3
  have hexpand :
      shortWeierstrassResidualInt a b
          (x + (p : ℤ) ^ k * u)
          (y + (p : ℤ) ^ k * v) =
        (p : ℤ) ^ k *
          (c + shortWeierstrassLinearTermInt a x y u v +
            (p : ℤ) ^ k * tail) := by
    rw [shortWeierstrassResidualInt_taylor, hbase]
    simp [shortWeierstrassHigherOrderInt, tail]
    ring
  rw [hexpand, pow_succ, mul_dvd_mul_iff_left hpk]
  have hpow : (p : ℤ) ∣ (p : ℤ) ^ k := by
    simpa using (pow_dvd_pow (p : ℤ) hk)
  have htail : (p : ℤ) ∣ (p : ℤ) ^ k * tail :=
    hpow.mul_right tail
  exact dvd_add_left htail

/--
A residue-ring linearized equation is exactly the corresponding integral
divisibility statement for canonical integer representatives.
-/
theorem linearizedEquation_zmod_iff_dvd
    (p : ℕ) (c gx gy : ℤ) (uv : ZMod p × ZMod p) :
    (c : ZMod p) + uv.1 * (gx : ZMod p) + uv.2 * (gy : ZMod p) = 0 ↔
      (p : ℤ) ∣
        c + (ZMod.cast uv.1 : ℤ) * gx +
          (ZMod.cast uv.2 : ℤ) * gy := by
  simpa [ZMod.intCast_zmod_cast] using
    (CharP.intCast_eq_zero_iff (ZMod p) p
      (c + (ZMod.cast uv.1 : ℤ) * gx +
        (ZMod.cast uv.2 : ℤ) * gy))

/-- Canonically parametrized raw increment fiber above an integral base point. -/
def RawWeierstrassLiftFiber
    (p k : ℕ) (a b x y : ℤ) : Type :=
  {uv : ZMod p × ZMod p //
    (p : ℤ) ^ (k + 1) ∣
      shortWeierstrassResidualInt a b
        (x + (p : ℤ) ^ k * (ZMod.cast uv.1 : ℤ))
        (y + (p : ℤ) ^ k * (ZMod.cast uv.2 : ℤ))}

/-- The raw increment fiber is finite for a prime camera. -/
noncomputable instance rawWeierstrassLiftFiberFintype
    (p k : ℕ) [Fact (Nat.Prime p)] (a b x y : ℤ) :
    Fintype (RawWeierstrassLiftFiber p k a b x y) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/--
The raw increment fiber is canonically the abstract linearized lift fiber.
The equivalence is the identity on the increment pair; only the certified
predicate changes form.
-/
def rawWeierstrassLiftFiberEquivLinearized
    (p k : ℕ) [Fact (Nat.Prime p)] (hk : 1 ≤ k)
    (a b x y c : ℤ)
    (hbase :
      shortWeierstrassResidualInt a b x y = (p : ℤ) ^ k * c) :
    RawWeierstrassLiftFiber p k a b x y ≃
      LinearizedLiftFiber p (c : ZMod p)
        (shortWeierstrassGradientXInt a x : ZMod p)
        (shortWeierstrassGradientYInt y : ZMod p) := by
  have hp : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
  refine
    { toFun := fun uv => ⟨uv.1, ?_⟩
      invFun := fun uv => ⟨uv.1, ?_⟩
      left_inv := by
        intro uv
        apply Subtype.ext
        rfl
      right_inv := by
        intro uv
        apply Subtype.ext
        rfl }
  · exact
      (linearizedEquation_zmod_iff_dvd p c
        (shortWeierstrassGradientXInt a x)
        (shortWeierstrassGradientYInt y) uv.1).2
        (by
          simpa [shortWeierstrassLinearTermInt, add_assoc] using
            ((shortWeierstrassRawLift_dvd_iff
              p k hp hk a b x y
              (ZMod.cast uv.1.1 : ℤ)
              (ZMod.cast uv.1.2 : ℤ) c hbase).1 uv.2))
  · exact
      (shortWeierstrassRawLift_dvd_iff
        p k hp hk a b x y
        (ZMod.cast uv.1.1 : ℤ)
        (ZMod.cast uv.1.2 : ℤ) c hbase).2
        (by
          simpa [shortWeierstrassLinearTermInt, add_assoc] using
            ((linearizedEquation_zmod_iff_dvd p c
              (shortWeierstrassGradientXInt a x)
              (shortWeierstrassGradientYInt y) uv.1).1 uv.2))

/--
The integral base residual produces a genuine affine state modulo the prime
camera.
-/
def affineCongruenceStateModPrimeOfIntegralResidual
    (p k : ℕ) [Fact (Nat.Prime p)] (hk : 1 ≤ k)
    (a b x y c : ℤ)
    (hbase :
      shortWeierstrassResidualInt a b x y = (p : ℤ) ^ k * c) :
    AffineCongruenceState p a b := by
  refine ⟨((x : ZMod p), (y : ZMod p)), ?_⟩
  have hpow : (p : ℤ) ∣ (p : ℤ) ^ k := by
    simpa using (pow_dvd_pow (p : ℤ) hk)
  have hres : (p : ℤ) ∣ shortWeierstrassResidualInt a b x y := by
    rw [hbase]
    exact hpow.mul_right c
  have hz :
      (shortWeierstrassResidualInt a b x y : ZMod p) = 0 :=
    (CharP.intCast_eq_zero_iff (ZMod p) p _).2 hres
  simpa using hz

/--
Specialized form of the raw/linearized equivalence for the displayed
short-Weierstrass state modulo `p`.
-/
def rawWeierstrassLiftFiberEquivWeierstrassLinearized
    (p k : ℕ) [Fact (Nat.Prime p)] (hk : 1 ≤ k)
    (a b x y c : ℤ)
    (hbase :
      shortWeierstrassResidualInt a b x y = (p : ℤ) ^ k * c) :
    RawWeierstrassLiftFiber p k a b x y ≃
      WeierstrassLinearizedLiftFiber p a b
        (affineCongruenceStateModPrimeOfIntegralResidual
          p k hk a b x y c hbase)
        (c : ZMod p) := by
  simpa [WeierstrassLinearizedLiftFiber,
    affineCongruenceStateModPrimeOfIntegralResidual] using
    (rawWeierstrassLiftFiberEquivLinearized
      p k hk a b x y c hbase)

/-- Every actual raw increment fiber has cardinality `p`, `0`, or `p^2`. -/
theorem card_rawWeierstrassLiftFiber_trichotomy
    (p k : ℕ) [Fact (Nat.Prime p)] (hk : 1 ≤ k)
    (a b x y c : ℤ)
    (hbase :
      shortWeierstrassResidualInt a b x y = (p : ℤ) ^ k * c) :
    Fintype.card (RawWeierstrassLiftFiber p k a b x y) = p ∨
      Fintype.card (RawWeierstrassLiftFiber p k a b x y) = 0 ∨
      Fintype.card (RawWeierstrassLiftFiber p k a b x y) = p ^ 2 := by
  let point :=
    affineCongruenceStateModPrimeOfIntegralResidual
      p k hk a b x y c hbase
  let e :=
    rawWeierstrassLiftFiberEquivWeierstrassLinearized
      p k hk a b x y c hbase
  have hcard :
      Fintype.card (RawWeierstrassLiftFiber p k a b x y) =
        Fintype.card
          (WeierstrassLinearizedLiftFiber p a b point (c : ZMod p)) :=
    Fintype.card_congr e
  rw [hcard]
  exact card_weierstrassLinearizedLiftFiber_trichotomy
    p a b point (c : ZMod p)

/--
Raw lift-fiber defect is supported exactly on the singular gradient of the
reduced affine state.
-/
theorem card_rawWeierstrassLiftFiber_ne_expected_iff_singular
    (p k : ℕ) [Fact (Nat.Prime p)] (hk : 1 ≤ k)
    (a b x y c : ℤ)
    (hbase :
      shortWeierstrassResidualInt a b x y = (p : ℤ) ^ k * c) :
    Fintype.card (RawWeierstrassLiftFiber p k a b x y) ≠ p ↔
      IsAffineSingularState p a b
        (affineCongruenceStateModPrimeOfIntegralResidual
          p k hk a b x y c hbase) := by
  let point :=
    affineCongruenceStateModPrimeOfIntegralResidual
      p k hk a b x y c hbase
  let e :=
    rawWeierstrassLiftFiberEquivWeierstrassLinearized
      p k hk a b x y c hbase
  have hcard :
      Fintype.card (RawWeierstrassLiftFiber p k a b x y) =
        Fintype.card
          (WeierstrassLinearizedLiftFiber p a b point (c : ZMod p)) :=
    Fintype.card_congr e
  rw [hcard]
  exact card_weierstrassLinearizedLiftFiber_ne_expected_iff_singular
    p a b point (c : ZMod p)

end

end CPFormal.Elliptic
