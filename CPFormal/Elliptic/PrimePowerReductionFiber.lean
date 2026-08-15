import CPFormal.Elliptic.RawLiftTaylor
import CPFormal.Elliptic.ReductionFiber
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-!
# Prime-power reduction fibers

This module begins the intrinsic bridge from the coordinate raw increment
fiber to the actual `MapFiber` of affine-state reduction from `p^(k+1)` to
`p^k`.  The first layer is the unique base-plus-digit decomposition of one
coordinate.
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
  apply ZMod.val_injective
  rw [ZMod.val_natCast_of_lt]
  · simp [zmodPrimePowerTargetDigitEquiv, ZMod.ringEquivCongr_val,
      finProdFinEquiv]
  · have htarget : target.val < p ^ k := target.val_lt
    have hdigit : digit.val < p := digit.val_lt
    calc
      target.val + p ^ k * digit.val <
          p ^ k + p ^ k * digit.val :=
        Nat.add_lt_add_right htarget _
      _ = p ^ k * (digit.val + 1) := by ring
      _ ≤ p ^ k * p := Nat.mul_le_mul_left _ hdigit
      _ = p ^ (k + 1) := by simp [pow_succ]

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
  simp [zmodReduction, ZMod.natCast_zmod_val]

end

end CPFormal.Elliptic
