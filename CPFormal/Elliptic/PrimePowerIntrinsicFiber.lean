import CPFormal.Elliptic.PrimePowerAffineFiber

/-!
# Intrinsic laws for affine prime-power reduction fibers

The raw Taylor fiber is already equivalent to the actual affine reduction
fiber.  This file chooses canonical integer representatives only long enough to
produce the exact residual quotient required by the Taylor theorem, then
transfers the local cardinality trichotomy and singular-support theorem to the
intrinsic `MapFiber` of the prime-power state tower.
-/

set_option autoImplicit false

namespace CPFormal.Elliptic

noncomputable section

/-- Canonical integer representative of the target `x` coordinate. -/
def canonicalPrimePowerX
    {modulus : ℕ} {a b : ℤ}
    (target : AffineCongruenceState modulus a b) : ℤ :=
  ZMod.cast target.1.1

/-- Canonical integer representative of the target `y` coordinate. -/
def canonicalPrimePowerY
    {modulus : ℕ} {a b : ℤ}
    (target : AffineCongruenceState modulus a b) : ℤ :=
  ZMod.cast target.1.2

@[simp]
theorem canonicalPrimePowerX_intCast
    {modulus : ℕ} {a b : ℤ}
    (target : AffineCongruenceState modulus a b) :
    (canonicalPrimePowerX target : ZMod modulus) = target.1.1 := by
  simp [canonicalPrimePowerX]

@[simp]
theorem canonicalPrimePowerY_intCast
    {modulus : ℕ} {a b : ℤ}
    (target : AffineCongruenceState modulus a b) :
    (canonicalPrimePowerY target : ZMod modulus) = target.1.2 := by
  simp [canonicalPrimePowerY]

/-- The canonical integral residual is divisible by the target prime power. -/
theorem canonicalPrimePowerResidual_dvd
    (p k : ℕ) [Fact (Nat.Prime p)]
    (a b : ℤ)
    (target : AffineCongruenceState (p ^ k) a b) :
    (p : ℤ) ^ k ∣
      shortWeierstrassResidualInt a b
        (canonicalPrimePowerX target)
        (canonicalPrimePowerY target) := by
  have hz :
      (shortWeierstrassResidualInt a b
          (canonicalPrimePowerX target)
          (canonicalPrimePowerY target) : ZMod (p ^ k)) = 0 := by
    rw [← shortWeierstrassResidual_intCast]
    simpa using target.2
  have hdiv :
      (((p ^ k : ℕ) : ℤ) ∣
        shortWeierstrassResidualInt a b
          (canonicalPrimePowerX target)
          (canonicalPrimePowerY target)) :=
    (CharP.intCast_eq_zero_iff (ZMod (p ^ k)) (p ^ k) _).1 hz
  simpa only [Nat.cast_pow] using hdiv

/-- Exact residual quotient attached to the canonical representatives. -/
noncomputable def canonicalPrimePowerResidualQuotient
    (p k : ℕ) [Fact (Nat.Prime p)]
    (a b : ℤ)
    (target : AffineCongruenceState (p ^ k) a b) : ℤ :=
  Classical.choose (canonicalPrimePowerResidual_dvd p k a b target)

/-- The canonical residual quotient satisfies the required exact equality. -/
theorem canonicalPrimePowerResidual_eq
    (p k : ℕ) [Fact (Nat.Prime p)]
    (a b : ℤ)
    (target : AffineCongruenceState (p ^ k) a b) :
    shortWeierstrassResidualInt a b
        (canonicalPrimePowerX target)
        (canonicalPrimePowerY target) =
      (p : ℤ) ^ k *
        canonicalPrimePowerResidualQuotient p k a b target :=
  Classical.choose_spec (canonicalPrimePowerResidual_dvd p k a b target)

/--
Canonical raw coordinates identify with the intrinsic affine reduction fiber.
The choice is merely a convenient chart; representative independence was
proved in `PrimePowerAffineFiber.lean`.
-/
def canonicalRawWeierstrassLiftFiberEquivPrimePowerReduction
    (p k : ℕ) [Fact (Nat.Prime p)]
    (a b : ℤ)
    (target : AffineCongruenceState (p ^ k) a b) :
    RawWeierstrassLiftFiber p k a b
        (canonicalPrimePowerX target)
        (canonicalPrimePowerY target) ≃
      MapFiber
        (affineCongruenceStateReduction
          (primePowerStepDvd p k) a b)
        target :=
  rawWeierstrassLiftFiberEquivPrimePowerReduction
    p k a b
    (canonicalPrimePowerX target)
    (canonicalPrimePowerY target)
    target
    (canonicalPrimePowerX_intCast target)
    (canonicalPrimePowerY_intCast target)

/-- The prime divides every positive prime-power level. -/
theorem primeDvdPrimePower
    (p k : ℕ) (hk : 1 ≤ k) : p ∣ p ^ k := by
  simpa using (pow_dvd_pow p hk)

/-- The intrinsic reduction of a target state from `p^k` to `p`. -/
def affineCongruenceStatePrimeReduction
    (p k : ℕ) (hk : 1 ≤ k)
    (a b : ℤ)
    (target : AffineCongruenceState (p ^ k) a b) :
    AffineCongruenceState p a b :=
  affineCongruenceStateReduction
    (primeDvdPrimePower p k hk) a b target

/--
The prime-level state produced from canonical integral representatives is the
intrinsic reduction of the target state.
-/
theorem canonicalPrimeState_eq_reduction
    (p k : ℕ) [Fact (Nat.Prime p)] (hk : 1 ≤ k)
    (a b : ℤ)
    (target : AffineCongruenceState (p ^ k) a b) :
    affineCongruenceStateModPrimeOfIntegralResidual
        p k hk a b
        (canonicalPrimePowerX target)
        (canonicalPrimePowerY target)
        (canonicalPrimePowerResidualQuotient p k a b target)
        (canonicalPrimePowerResidual_eq p k a b target) =
      affineCongruenceStatePrimeReduction p k hk a b target := by
  apply Subtype.ext
  apply Prod.ext
  · change
      (canonicalPrimePowerX target : ZMod p) =
        zmodReduction (primeDvdPrimePower p k hk) target.1.1
    have hx := congrArg
      (fun z : ZMod (p ^ k) =>
        zmodReduction (primeDvdPrimePower p k hk) z)
      (canonicalPrimePowerX_intCast target)
    simpa [zmodReduction] using hx
  · change
      (canonicalPrimePowerY target : ZMod p) =
        zmodReduction (primeDvdPrimePower p k hk) target.1.2
    have hy := congrArg
      (fun z : ZMod (p ^ k) =>
        zmodReduction (primeDvdPrimePower p k hk) z)
      (canonicalPrimePowerY_intCast target)
    simpa [zmodReduction] using hy

/--
Every intrinsic affine reduction fiber from `p^(k+1)` to `p^k` has cardinality
`p`, `0`, or `p^2`.
-/
theorem card_primePowerAffineReductionFiber_trichotomy
    (p k : ℕ) [Fact (Nat.Prime p)] (hk : 1 ≤ k)
    (a b : ℤ)
    (target : AffineCongruenceState (p ^ k) a b) :
    Fintype.card
        (MapFiber
          (affineCongruenceStateReduction
            (primePowerStepDvd p k) a b)
          target) = p ∨
      Fintype.card
        (MapFiber
          (affineCongruenceStateReduction
            (primePowerStepDvd p k) a b)
          target) = 0 ∨
      Fintype.card
        (MapFiber
          (affineCongruenceStateReduction
            (primePowerStepDvd p k) a b)
          target) = p ^ 2 := by
  let raw := RawWeierstrassLiftFiber p k a b
    (canonicalPrimePowerX target)
    (canonicalPrimePowerY target)
  have hcard :
      Fintype.card raw =
        Fintype.card
          (MapFiber
            (affineCongruenceStateReduction
              (primePowerStepDvd p k) a b)
            target) :=
    Fintype.card_congr
      (canonicalRawWeierstrassLiftFiberEquivPrimePowerReduction
        p k a b target)
  rw [← hcard]
  exact card_rawWeierstrassLiftFiber_trichotomy
    p k hk a b
    (canonicalPrimePowerX target)
    (canonicalPrimePowerY target)
    (canonicalPrimePowerResidualQuotient p k a b target)
    (canonicalPrimePowerResidual_eq p k a b target)

/--
An intrinsic prime-power reduction fiber is non-regular exactly when the target
state reduced modulo `p` has vanishing affine gradient.
-/
theorem card_primePowerAffineReductionFiber_ne_expected_iff_singular
    (p k : ℕ) [Fact (Nat.Prime p)] (hk : 1 ≤ k)
    (a b : ℤ)
    (target : AffineCongruenceState (p ^ k) a b) :
    Fintype.card
        (MapFiber
          (affineCongruenceStateReduction
            (primePowerStepDvd p k) a b)
          target) ≠ p ↔
      IsAffineSingularState p a b
        (affineCongruenceStatePrimeReduction p k hk a b target) := by
  let raw := RawWeierstrassLiftFiber p k a b
    (canonicalPrimePowerX target)
    (canonicalPrimePowerY target)
  have hcard :
      Fintype.card raw =
        Fintype.card
          (MapFiber
            (affineCongruenceStateReduction
              (primePowerStepDvd p k) a b)
            target) :=
    Fintype.card_congr
      (canonicalRawWeierstrassLiftFiberEquivPrimePowerReduction
        p k a b target)
  calc
    Fintype.card
        (MapFiber
          (affineCongruenceStateReduction
            (primePowerStepDvd p k) a b)
          target) ≠ p ↔
        Fintype.card raw ≠ p := by rw [hcard]
    _ ↔ IsAffineSingularState p a b
        (affineCongruenceStateModPrimeOfIntegralResidual
          p k hk a b
          (canonicalPrimePowerX target)
          (canonicalPrimePowerY target)
          (canonicalPrimePowerResidualQuotient p k a b target)
          (canonicalPrimePowerResidual_eq p k a b target)) :=
      card_rawWeierstrassLiftFiber_ne_expected_iff_singular
        p k hk a b
        (canonicalPrimePowerX target)
        (canonicalPrimePowerY target)
        (canonicalPrimePowerResidualQuotient p k a b target)
        (canonicalPrimePowerResidual_eq p k a b target)
    _ ↔ IsAffineSingularState p a b
        (affineCongruenceStatePrimeReduction p k hk a b target) := by
      rw [canonicalPrimeState_eq_reduction]

end

end CPFormal.Elliptic
