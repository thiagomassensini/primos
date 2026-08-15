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
def primePowerStepDvd (p k : ℕ) : p ^ k ∣ p ^ (k + 1) := by
  refine ⟨p, ?_⟩
  simp [pow_succ]

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
  exact
    (Equiv.prodComm (ZMod (p ^ k)) (ZMod p)).trans
      (((((ZMod.finEquiv p).symm.toEquiv).prodCongr
          ((ZMod.finEquiv (p ^ k)).symm.toEquiv)).trans
        finProdFinEquiv).trans
        (ZMod.finEquiv (p * p ^ k)).toEquiv).trans
        (ZMod.ringEquivCongr hpow).toEquiv

/-- The target component of the digit decomposition is canonical reduction. -/
@[simp]
theorem zmodReduction_zmodPrimePowerTargetDigitEquiv
    (p k : ℕ) [NeZero p]
    (target : ZMod (p ^ k)) (digit : ZMod p) :
    zmodReduction (primePowerStepDvd p k)
        (zmodPrimePowerTargetDigitEquiv p k (target, digit)) =
      target := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero k (NeZero.ne p)⟩
  obtain ⟨targetNat, rfl⟩ := ZMod.natCast_zmod_surjective target
  obtain ⟨digitNat, rfl⟩ := ZMod.natCast_zmod_surjective digit
  simp [zmodPrimePowerTargetDigitEquiv, zmodReduction,
    primePowerStepDvd, finProdFinEquiv, pow_succ, Nat.mul_comm,
    Nat.add_mod]

end

end CPFormal.Elliptic
