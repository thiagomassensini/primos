import CPFormal.Elliptic.PrimePowerIntrinsicFiber
import Mathlib.Tactic

/-!
# Discriminant support for affine short-Weierstrass fibers

For the displayed integral model

```text
y^2 = x^3 + a*x + b
```

and primes `p >= 5`, this file identifies three finite local supports:

* divisibility of the integral discriminant by `p`;
* existence of a singular affine state modulo `p`;
* existence of a non-regular intrinsic reduction fiber from `p^2` to `p`.

The restriction `p >= 5` keeps `2` and `3` invertible.  Characteristics `2`
and `3` require separate normal forms and are deliberately not folded into the
short-Weierstrass argument.
-/

set_option autoImplicit false

namespace CPFormal.Elliptic

noncomputable section

/-- Integral discriminant of the displayed short-Weierstrass model. -/
def shortWeierstrassDiscriminantInt (a b : ℤ) : ℤ :=
  -16 * (4 * a ^ 3 + 27 * b ^ 2)

/-- The discriminant core reduced modulo `p`. -/
def shortWeierstrassDiscriminantCore
    (p : ℕ) (a b : ℤ) : ZMod p :=
  (4 : ZMod p) * (a : ZMod p) ^ 3 +
    (27 : ZMod p) * (b : ZMod p) ^ 2

/-- A positive natural strictly below the modulus has nonzero class. -/
theorem zmodNatCast_ne_zero_of_lt
    (p n : ℕ) (hn : 0 < n) (hnp : n < p) :
    (n : ZMod p) ≠ 0 := by
  intro hz
  have hdvd : p ∣ n :=
    (ZMod.natCast_eq_zero_iff n p).1 hz
  exact (Nat.not_le_of_gt hnp) (Nat.le_of_dvd hn hdvd)

/-- `2` is nonzero modulo every prime at least `5`. -/
theorem zmodTwo_ne_zero_of_five_le
    (p : ℕ) [Fact (Nat.Prime p)] (hp : 5 ≤ p) :
    (2 : ZMod p) ≠ 0 := by
  exact zmodNatCast_ne_zero_of_lt p 2 (by omega) (by omega)

/-- `3` is nonzero modulo every prime at least `5`. -/
theorem zmodThree_ne_zero_of_five_le
    (p : ℕ) [Fact (Nat.Prime p)] (hp : 5 ≤ p) :
    (3 : ZMod p) ≠ 0 := by
  exact zmodNatCast_ne_zero_of_lt p 3 (by omega) (by omega)

/-- The conventional factor `-16` is a unit modulo primes at least `5`. -/
theorem zmodNegSixteen_ne_zero_of_five_le
    (p : ℕ) [Fact (Nat.Prime p)] (hp : 5 ≤ p) :
    (-16 : ZMod p) ≠ 0 := by
  have hpow : (-16 : ZMod p) = -((2 : ZMod p) ^ 4) := by
    norm_num
  rw [hpow]
  exact neg_ne_zero.mpr
    (pow_ne_zero 4 (zmodTwo_ne_zero_of_five_le p hp))

/-- The coefficient `27` is nonzero modulo primes at least `5`. -/
theorem zmodTwentySeven_ne_zero_of_five_le
    (p : ℕ) [Fact (Nat.Prime p)] (hp : 5 ≤ p) :
    (27 : ZMod p) ≠ 0 := by
  have hpow : (27 : ZMod p) = (3 : ZMod p) ^ 3 := by
    norm_num
  rw [hpow]
  exact pow_ne_zero 3 (zmodThree_ne_zero_of_five_le p hp)

/-- Reduction of the integral discriminant is `-16` times its core. -/
@[simp]
theorem shortWeierstrassDiscriminantInt_cast
    (p : ℕ) (a b : ℤ) :
    (shortWeierstrassDiscriminantInt a b : ZMod p) =
      (-16 : ZMod p) * shortWeierstrassDiscriminantCore p a b := by
  simp [shortWeierstrassDiscriminantInt,
    shortWeierstrassDiscriminantCore]

/-- For `p >= 5`, divisibility of the full discriminant is core vanishing. -/
theorem int_dvd_shortWeierstrassDiscriminant_iff_core_eq_zero
    (p : ℕ) [Fact (Nat.Prime p)] (hp : 5 ≤ p)
    (a b : ℤ) :
    (p : ℤ) ∣ shortWeierstrassDiscriminantInt a b ↔
      shortWeierstrassDiscriminantCore p a b = 0 := by
  constructor
  · intro hdvd
    have hcast :
        (shortWeierstrassDiscriminantInt a b : ZMod p) = 0 :=
      (CharP.intCast_eq_zero_iff
        (ZMod p) p (shortWeierstrassDiscriminantInt a b)).2 hdvd
    rw [shortWeierstrassDiscriminantInt_cast] at hcast
    exact
      (mul_eq_zero.mp hcast).resolve_left
        (zmodNegSixteen_ne_zero_of_five_le p hp)
  · intro hcore
    apply
      (CharP.intCast_eq_zero_iff
        (ZMod p) p (shortWeierstrassDiscriminantInt a b)).1
    rw [shortWeierstrassDiscriminantInt_cast, hcore, mul_zero]

/-- Every singular affine state forces the discriminant core to vanish. -/
theorem shortWeierstrassDiscriminantCore_eq_zero_of_singular
    (p : ℕ) [Fact (Nat.Prime p)] (hp : 5 ≤ p)
    (a b : ℤ)
    (point : AffineCongruenceState p a b)
    (hsingular : IsAffineSingularState p a b point) :
    shortWeierstrassDiscriminantCore p a b = 0 := by
  have hy : point.1.2 = 0 :=
    (mul_eq_zero.mp hsingular.2).resolve_left
      (zmodTwo_ne_zero_of_five_le p hp)
  have ha :
      (a : ZMod p) = (-3 : ZMod p) * point.1.1 ^ 2 :=
    (sub_eq_zero.mp hsingular.1).symm
  have hcurve :
      point.1.1 ^ 3 + (a : ZMod p) * point.1.1 +
          (b : ZMod p) = 0 := by
    simpa [shortWeierstrassResidual, hy] using point.2
  have hb :
      (b : ZMod p) = (2 : ZMod p) * point.1.1 ^ 3 := by
    rw [ha] at hcurve
    linear_combination hcurve
  rw [shortWeierstrassDiscriminantCore, ha, hb]
  ring

/-- Vanishing discriminant core produces an explicit singular affine state. -/
theorem exists_affineSingularState_of_discriminantCore_eq_zero
    (p : ℕ) [Fact (Nat.Prime p)] (hp : 5 ≤ p)
    (a b : ℤ)
    (hcore : shortWeierstrassDiscriminantCore p a b = 0) :
    ∃ point : AffineCongruenceState p a b,
      IsAffineSingularState p a b point := by
  have hcore' :
      (4 : ZMod p) * (a : ZMod p) ^ 3 +
          (27 : ZMod p) * (b : ZMod p) ^ 2 = 0 := by
    simpa [shortWeierstrassDiscriminantCore] using hcore
  by_cases ha : (a : ZMod p) = 0
  · have hmul :
        (27 : ZMod p) * (b : ZMod p) ^ 2 = 0 := by
      simpa [ha] using hcore'
    have hsq : (b : ZMod p) ^ 2 = 0 :=
      (mul_eq_zero.mp hmul).resolve_left
        (zmodTwentySeven_ne_zero_of_five_le p hp)
    have hb : (b : ZMod p) = 0 := by
      have hself : (b : ZMod p) * (b : ZMod p) = 0 := by
        simpa [pow_two] using hsq
      rcases mul_eq_zero.mp hself with hb | hb
      · exact hb
      · exact hb
    let point : AffineCongruenceState p a b :=
      ⟨(0, 0), by
        simp [shortWeierstrassResidual, ha, hb]⟩
    refine ⟨point, ?_⟩
    constructor
    · simp [point, shortWeierstrassGradientX, ha]
    · simp [point, shortWeierstrassGradientY]
  · let x : ZMod p :=
      -((3 : ZMod p) * (b : ZMod p)) /
        ((2 : ZMod p) * (a : ZMod p))
    have hden :
        (2 : ZMod p) * (a : ZMod p) ≠ 0 :=
      mul_ne_zero (zmodTwo_ne_zero_of_five_le p hp) ha
    have hxGradient :
        shortWeierstrassGradientX p a x = 0 := by
      rw [shortWeierstrassGradientX]
      dsimp [x]
      field_simp [hden]
      linear_combination -hcore'
    have hcurvePolynomial :
        x ^ 3 + (a : ZMod p) * x + (b : ZMod p) = 0 := by
      dsimp [x]
      field_simp [hden]
      linear_combination -(b : ZMod p) * hcore'
    let point : AffineCongruenceState p a b :=
      ⟨(x, 0), by
        simp [shortWeierstrassResidual, hcurvePolynomial]⟩
    refine ⟨point, ?_⟩
    constructor
    · simpa [point] using hxGradient
    · simp [point, shortWeierstrassGradientY]

/-- For `p >= 5`, discriminant divisibility is exactly singular affine support. -/
theorem int_dvd_shortWeierstrassDiscriminant_iff_exists_singular
    (p : ℕ) [Fact (Nat.Prime p)] (hp : 5 ≤ p)
    (a b : ℤ) :
    (p : ℤ) ∣ shortWeierstrassDiscriminantInt a b ↔
      ∃ point : AffineCongruenceState p a b,
        IsAffineSingularState p a b point := by
  rw [int_dvd_shortWeierstrassDiscriminant_iff_core_eq_zero p hp a b]
  constructor
  · exact exists_affineSingularState_of_discriminantCore_eq_zero p hp a b
  · rintro ⟨point, hsingular⟩
    exact shortWeierstrassDiscriminantCore_eq_zero_of_singular
      p hp a b point hsingular

/-- Reduction from the first prime-power level back to `p` is the identity. -/
@[simp]
theorem affineCongruenceStatePrimeReduction_one
    (p : ℕ) [Fact (Nat.Prime p)]
    (a b : ℤ)
    (target : AffineCongruenceState p a b) :
    affineCongruenceStatePrimeReduction p 1 (by omega) a b target =
      target := by
  apply Subtype.ext
  apply Prod.ext <;>
    simp [affineCongruenceStatePrimeReduction,
      affineCongruenceStateReduction, zmodPointReduction, zmodReduction]

/--
For `p >= 5`, bad discriminant support is exactly the support of a non-regular
intrinsic fiber from `p^2` to `p`.
-/
theorem int_dvd_shortWeierstrassDiscriminant_iff_exists_nonregular_primeSquareFiber
    (p : ℕ) [Fact (Nat.Prime p)] (hp : 5 ≤ p)
    (a b : ℤ) :
    (p : ℤ) ∣ shortWeierstrassDiscriminantInt a b ↔
      ∃ target : AffineCongruenceState p a b,
        Fintype.card
            (MapFiber
              (affineCongruenceStateReduction
                (primePowerStepDvd p 1) a b)
              target) ≠ p := by
  rw [int_dvd_shortWeierstrassDiscriminant_iff_exists_singular p hp a b]
  constructor
  · rintro ⟨target, hsingular⟩
    refine ⟨target, ?_⟩
    apply
      (card_primePowerAffineReductionFiber_ne_expected_iff_singular
        p 1 (by omega) a b target).2
    simpa using hsingular
  · rintro ⟨target, hnonregular⟩
    refine ⟨target, ?_⟩
    have hsingular :=
      (card_primePowerAffineReductionFiber_ne_expected_iff_singular
        p 1 (by omega) a b target).1 hnonregular
    simpa using hsingular

end

end CPFormal.Elliptic
