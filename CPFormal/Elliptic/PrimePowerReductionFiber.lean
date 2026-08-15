import CPFormal.Elliptic.RawLiftTaylor
import CPFormal.Elliptic.ReductionFiber
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-!
# Prime-power reduction fibers

This module identifies coordinate increments modulo `p` with the actual fibers
of reduction from `p^(k+1)` to `p^k`.  It keeps two complementary descriptions:

* a canonical mixed-radix equivalence `target × digit ≃ source`;
* an integral-anchor description `x + p^k * digit`, suitable for the raw
  Taylor fibers from `RawLiftTaylor.lean`.

The affine-state bridge is built below from these coordinate fibers.
-/

set_option autoImplicit false

namespace CPFormal.Elliptic

noncomputable section

/-- The canonical divisibility `p^k ∣ p^(k+1)`. -/
theorem primePowerStepDvd (p k : ℕ) : p ^ k ∣ p ^ (k + 1) := by
  refine ⟨p, ?_⟩
  simp [pow_succ]

/-- `ZMod.finEquiv` preserves canonical values. -/
@[simp]
theorem zmodFinEquiv_apply_val
    (n : ℕ) [NeZero n] (x : Fin n) :
    (ZMod.finEquiv n x).val = x.val := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

/-- The inverse of `ZMod.finEquiv` preserves canonical values. -/
@[simp]
theorem zmodFinEquiv_symm_apply_val
    (n : ℕ) [NeZero n] (x : ZMod n) :
    ((ZMod.finEquiv n).symm x).val = x.val := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

/--
Every residue modulo `p^(k+1)` is uniquely a target residue modulo `p^k`
plus one digit modulo `p`.  The product is ordered as `(target, digit)`.
-/
def zmodPrimePowerTargetDigitEquiv
    (p k : ℕ) [NeZero p] :
    ZMod (p ^ k) × ZMod p ≃ ZMod (p ^ (k + 1)) := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero k (NeZero.ne p)⟩
  letI : NeZero (p * p ^ k) :=
    ⟨mul_ne_zero (NeZero.ne p) (pow_ne_zero k (NeZero.ne p))⟩
  have hpow : p * p ^ k = p ^ (k + 1) := by
    simp [pow_succ, Nat.mul_comm]
  let toFinProduct : ZMod p × ZMod (p ^ k) ≃ Fin p × Fin (p ^ k) :=
    ((ZMod.finEquiv p).symm.toEquiv).prodCongr
      ((ZMod.finEquiv (p ^ k)).symm.toEquiv)
  let packFin : Fin p × Fin (p ^ k) ≃ Fin (p * p ^ k) :=
    finProdFinEquiv
  let toZMod : Fin (p * p ^ k) ≃ ZMod (p * p ^ k) :=
    (ZMod.finEquiv (p * p ^ k)).toEquiv
  let changeModulus : ZMod (p * p ^ k) ≃ ZMod (p ^ (k + 1)) :=
    (ZMod.ringEquivCongr hpow).toEquiv
  exact
    (Equiv.prodComm (ZMod (p ^ k)) (ZMod p)).trans
      (((toFinProduct.trans packFin).trans toZMod).trans changeModulus)

/-- The mixed-radix equivalence has the expected canonical natural value. -/
@[simp]
theorem zmodPrimePowerTargetDigitEquiv_apply
    (p k : ℕ) [NeZero p]
    (target : ZMod (p ^ k)) (digit : ZMod p) :
    zmodPrimePowerTargetDigitEquiv p k (target, digit) =
      ((target.val + p ^ k * digit.val : ℕ) : ZMod (p ^ (k + 1))) := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero k (NeZero.ne p)⟩
  letI : NeZero (p * p ^ k) :=
    ⟨mul_ne_zero (NeZero.ne p) (pow_ne_zero k (NeZero.ne p))⟩
  letI : NeZero (p ^ (k + 1)) :=
    ⟨pow_ne_zero (k + 1) (NeZero.ne p)⟩
  have hlt : target.val + p ^ k * digit.val < p ^ (k + 1) := by
    have htarget : target.val < p ^ k := target.val_lt
    have hdigit : digit.val < p := digit.val_lt
    calc
      target.val + p ^ k * digit.val <
          p ^ k + p ^ k * digit.val :=
        Nat.add_lt_add_right htarget _
      _ = p ^ k * (digit.val + 1) := by ring
      _ ≤ p ^ k * p :=
        Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr hdigit)
      _ = p ^ (k + 1) := by simp [pow_succ]
  apply ZMod.val_injective
  rw [ZMod.val_natCast_of_lt hlt]
  dsimp [zmodPrimePowerTargetDigitEquiv]
  rw [ZMod.ringEquivCongr_val]
  rw [zmodFinEquiv_apply_val]
  change
    ((ZMod.finEquiv (p ^ k)).symm target).val +
        p ^ k * ((ZMod.finEquiv p).symm digit).val =
      target.val + p ^ k * digit.val
  simp

/-- The target component of the digit decomposition is canonical reduction. -/
@[simp]
theorem zmodReduction_zmodPrimePowerTargetDigitEquiv
    (p k : ℕ) [NeZero p]
    (target : ZMod (p ^ k)) (digit : ZMod p) :
    zmodReduction (primePowerStepDvd p k)
        (zmodPrimePowerTargetDigitEquiv p k (target, digit)) =
      target := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero k (NeZero.ne p)⟩
  rw [zmodPrimePowerTargetDigitEquiv_apply]
  change
    (ZMod.cast
      ((target.val + p ^ k * digit.val : ℕ) : ZMod (p ^ (k + 1))) :
        ZMod (p ^ k)) = target
  rw [ZMod.cast_natCast (R := ZMod (p ^ k))
    (primePowerStepDvd p k)]
  rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
  simp

/-- The integral-coordinate lift used by the raw Taylor fiber. -/
def primePowerCoordinateLift
    (p k : ℕ) (x : ℤ) (digit : ZMod p) :
    ZMod (p ^ (k + 1)) :=
  ((x + (p : ℤ) ^ k * (ZMod.cast digit : ℤ) : ℤ) :
    ZMod (p ^ (k + 1)))

/-- Integral-coordinate lifts reduce to their anchored residue modulo `p^k`. -/
@[simp]
theorem zmodReduction_primePowerCoordinateLift
    (p k : ℕ) [NeZero p] (x : ℤ) (digit : ZMod p) :
    zmodReduction (primePowerStepDvd p k)
        (primePowerCoordinateLift p k x digit) =
      (x : ZMod (p ^ k)) := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero k (NeZero.ne p)⟩
  change
    (ZMod.cast
      ((x + (p : ℤ) ^ k * (ZMod.cast digit : ℤ) : ℤ) :
        ZMod (p ^ (k + 1))) : ZMod (p ^ k)) =
      (x : ZMod (p ^ k))
  rw [ZMod.cast_intCast (R := ZMod (p ^ k))
    (primePowerStepDvd p k)]
  rw [Int.cast_add, Int.cast_mul]
  simp

/-- An anchored digit as an element of the coordinate reduction fiber. -/
def primePowerCoordinateFiberMap
    (p k : ℕ) [NeZero p] (x : ℤ) :
    ZMod p →
      MapFiber
        (zmodReduction (primePowerStepDvd p k))
        (x : ZMod (p ^ k)) :=
  fun digit =>
    ⟨primePowerCoordinateLift p k x digit,
      zmodReduction_primePowerCoordinateLift p k x digit⟩

/-- Distinct digits give distinct anchored lifts modulo `p^(k+1)`. -/
theorem primePowerCoordinateFiberMap_injective
    (p k : ℕ) [NeZero p] (x : ℤ) :
    Function.Injective (primePowerCoordinateFiberMap p k x) := by
  intro u v huv
  have hcoord :
      primePowerCoordinateLift p k x u =
        primePowerCoordinateLift p k x v :=
    congrArg Subtype.val huv
  have hdiv :
      ((p ^ (k + 1) : ℕ) : ℤ) ∣
        (x + (p : ℤ) ^ k * (ZMod.cast v : ℤ)) -
          (x + (p : ℤ) ^ k * (ZMod.cast u : ℤ)) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub
      (x + (p : ℤ) ^ k * (ZMod.cast u : ℤ))
      (x + (p : ℤ) ^ k * (ZMod.cast v : ℤ))
      (p ^ (k + 1))).1 hcoord
  have hsource :
      ((p ^ (k + 1) : ℕ) : ℤ) =
        (p : ℤ) ^ k * (p : ℤ) := by
    push_cast
    rw [pow_succ]
  have hdiff :
      (x + (p : ℤ) ^ k * (ZMod.cast v : ℤ)) -
          (x + (p : ℤ) ^ k * (ZMod.cast u : ℤ)) =
        (p : ℤ) ^ k *
          ((ZMod.cast v : ℤ) - (ZMod.cast u : ℤ)) := by
    ring
  rw [hsource, hdiff] at hdiv
  have hpz : (p : ℤ) ≠ 0 := by
    exact_mod_cast NeZero.ne p
  have hpk : (p : ℤ) ^ k ≠ 0 :=
    pow_ne_zero _ hpz
  have hpdiv :
      (p : ℤ) ∣ (ZMod.cast v : ℤ) - (ZMod.cast u : ℤ) :=
    (mul_dvd_mul_iff_left hpk).1 hdiv
  have hcasts :
      ((ZMod.cast u : ℤ) : ZMod p) =
        ((ZMod.cast v : ℤ) : ZMod p) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub
      (ZMod.cast u : ℤ) (ZMod.cast v : ℤ) p).2 hpdiv
  simpa using hcasts

/-- Every coordinate reduction fiber is reached by one anchored digit. -/
theorem primePowerCoordinateFiberMap_surjective
    (p k : ℕ) [NeZero p] (x : ℤ) :
    Function.Surjective (primePowerCoordinateFiberMap p k x) := by
  intro point
  let z : ℤ := ZMod.cast point.1
  have hred :
      (z : ZMod (p ^ k)) = (x : ZMod (p ^ k)) := by
    simpa [z, zmodReduction] using point.2
  have hdiv :
      (p : ℤ) ^ k ∣ z - x := by
    simpa using
      (ZMod.intCast_eq_intCast_iff_dvd_sub
        x z (p ^ k)).1 hred.symm
  rcases hdiv with ⟨q, hq⟩
  let digit : ZMod p := (q : ZMod p)
  refine ⟨digit, ?_⟩
  apply Subtype.ext
  change primePowerCoordinateLift p k x digit = point.1
  rw [← ZMod.intCast_zmod_cast point.1]
  apply
    (ZMod.intCast_eq_intCast_iff_dvd_sub
      (x + (p : ℤ) ^ k * (ZMod.cast digit : ℤ))
      z (p ^ (k + 1))).2
  have hpdiv :
      (p : ℤ) ∣ q - (ZMod.cast digit : ℤ) := by
    apply
      (ZMod.intCast_eq_intCast_iff_dvd_sub
        (ZMod.cast digit : ℤ) q p).1
    simp [digit]
  have hscaled :
      (p : ℤ) ^ k * (p : ℤ) ∣
        (p : ℤ) ^ k * (q - (ZMod.cast digit : ℤ)) :=
    mul_dvd_mul_left ((p : ℤ) ^ k) hpdiv
  have hsource :
      ((p ^ (k + 1) : ℕ) : ℤ) =
        (p : ℤ) ^ k * (p : ℤ) := by
    push_cast
    rw [pow_succ]
  have hdiff :
      z - (x + (p : ℤ) ^ k * (ZMod.cast digit : ℤ)) =
        (p : ℤ) ^ k * (q - (ZMod.cast digit : ℤ)) := by
    calc
      z - (x + (p : ℤ) ^ k * (ZMod.cast digit : ℤ)) =
          (z - x) - (p : ℤ) ^ k * (ZMod.cast digit : ℤ) := by
        ring
      _ = (p : ℤ) ^ k * q -
          (p : ℤ) ^ k * (ZMod.cast digit : ℤ) := by
        rw [hq]
      _ = (p : ℤ) ^ k *
          (q - (ZMod.cast digit : ℤ)) := by
        ring
  rw [hsource, hdiff]
  exact hscaled

/--
The actual coordinate reduction fiber is equivalent to one digit modulo `p`,
for every integral representative of the target coordinate.
-/
def primePowerCoordinateReductionFiberEquiv
    (p k : ℕ) [NeZero p] (x : ℤ) :
    ZMod p ≃
      MapFiber
        (zmodReduction (primePowerStepDvd p k))
        (x : ZMod (p ^ k)) :=
  Equiv.ofBijective
    (primePowerCoordinateFiberMap p k x)
    ⟨primePowerCoordinateFiberMap_injective p k x,
      primePowerCoordinateFiberMap_surjective p k x⟩

@[simp]
theorem primePowerCoordinateReductionFiberEquiv_apply_val
    (p k : ℕ) [NeZero p] (x : ℤ) (digit : ZMod p) :
    (primePowerCoordinateReductionFiberEquiv p k x digit).1 =
      primePowerCoordinateLift p k x digit :=
  rfl

end

end CPFormal.Elliptic
