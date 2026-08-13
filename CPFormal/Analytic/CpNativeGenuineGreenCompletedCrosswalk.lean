import CPFormal.Analytic.CpGenuineNativeRealBoundaryCrosswalk
import CPFormal.Analytic.CpGenuineGreenCompletedOperator
import Mathlib.Tactic.Linarith

/-!
# Native, Genuine, and Green: zero versus transverse equilibrium

This module records the separation that is essential to the architecture.

Inside the open Genuine strip, the native camera-three zero and the scalar
Genuine zero are the same vanishing event, at every radial coordinate:

```text
native zero at (re(s), im(s))  <->  genuineContinuation s = 0.
```

Independently, the Green center detects the transverse displacement
`re(s) - 1 / 2`.  Therefore the *completed* two-channel operator vanishes
exactly when both facts hold:

```text
completed Green operator = 0
  <-> native/Genuine zero and re(s) = 1 / 2.
```

Thus an off-equilibrium zero remains a zero.  What cannot vanish there is the
additional Green diagnostic channel.  Quadratic mass compatibility is never
inserted into the definition of zero.
-/

open scoped Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/--
The primitive native real camera and the scalar Genuine continuation have
exactly the same zero set throughout the open strip.
-/
theorem isNativeCarryRealOperatorZero_three_iff_genuineContinuation_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    IsNativeCarryRealOperatorZero 3 s.re s.im ↔
      genuineContinuation s = 0 := by
  rw [isNativeCarryRealOperatorZero_iff]
  exact nativeCarryRealBoundaryClosure_iff_genuineContinuation_zero hs

/--
At a native/Genuine zero, Green closure is exactly transverse equilibrium; it
is not part of the zero hypothesis.
-/
theorem crossPrimeAlignedGreenClosure_at_nativeZero_iff_re_eq_half
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : IsNativeCarryRealOperatorZero 3 s.re s.im) :
    CrossPrimeAlignedGreenClosure p q s ↔
      s.re = (1 : ℝ) / 2 := by
  have hgenuine : genuineContinuation s = 0 :=
    (isNativeCarryRealOperatorZero_three_iff_genuineContinuation_zero hs).1
      hzero
  rw [crossPrimeAlignedGreenClosure_iff_limitVector_eq_zero
      p q hp hq hs hgenuine,
    crossPrimeAlignedGreenLimitVector_eq_zero_iff_criticalDisplacement_eq_zero
      p q hp hq hs]
  unfold criticalDisplacement
  constructor <;> intro h <;> linarith

/--
The completed two-channel operator is zero exactly when the native/Genuine
zero and Green equilibrium occur together.
-/
theorem genuineGreenCompletedLimitOperator_eq_zero_iff_nativeZero_and_re_eq_half
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    genuineGreenCompletedLimitOperator p q s = 0 ↔
      IsNativeCarryRealOperatorZero 3 s.re s.im ∧
        s.re = (1 : ℝ) / 2 := by
  rw [genuineGreenCompletedLimitOperator_eq_zero_iff_re_eq_half
      p q hp hq hs,
    isNativeCarryRealOperatorZero_three_iff_genuineContinuation_zero hs]

/-- Equivalent coordinate-free formulation using the Green displacement. -/
theorem genuineGreenCompletedLimitOperator_eq_zero_iff_nativeZero_and_greenCenter_zero
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    genuineGreenCompletedLimitOperator p q s = 0 ↔
      IsNativeCarryRealOperatorZero 3 s.re s.im ∧
        criticalDisplacement s.re = 0 := by
  rw [genuineGreenCompletedLimitOperator_eq_zero_iff p q hp hq hs,
    isNativeCarryRealOperatorZero_three_iff_genuineContinuation_zero hs]

/--
Exact channel separation at an off-equilibrium zero: the Genuine block is
zero, while the Green center is nonzero. This is the formal statement that
Green detects the tilt without changing the meaning of the zero.
-/
theorem nativeZero_offEquilibrium_channelSeparation
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : IsNativeCarryRealOperatorZero 3 s.re s.im)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    orthogonalGenuineLimitOperator s = 0 ∧
      complexifiedAlignedGreenLimitOperator p q s ≠ 0 := by
  have hgenuine : genuineContinuation s = 0 :=
    (isNativeCarryRealOperatorZero_three_iff_genuineContinuation_zero hs).1
      hzero
  refine ⟨(orthogonalGenuineLimitOperator_eq_zero_iff s).2 hgenuine, ?_⟩
  intro hgreen
  have hcenter : criticalDisplacement s.re = 0 :=
    (complexifiedAlignedGreenLimitOperator_eq_zero_iff_criticalDisplacement_eq_zero
      p q hp hq hs).1 hgreen
  apply hoff
  unfold criticalDisplacement at hcenter
  linarith

/--
If a native/Genuine zero lies away from equilibrium, the zero remains valid
and the completed operator is nonzero precisely because its Green channel
detects the tilt.
-/
theorem nativeZero_has_nonzero_greenCompletedOperator_of_re_ne_half
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (_hzero : IsNativeCarryRealOperatorZero 3 s.re s.im)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    genuineGreenCompletedLimitOperator p q s ≠ 0 :=
  genuineGreenCompletedLimitOperator_ne_zero_of_re_ne_half
    p q hp hq hs hoff

/--
At every native/Genuine zero, the finite completed operators converge to the
explicit two-channel limit.  No equilibrium assumption is used.
-/
theorem finiteGenuineGreenCompletedOperator_tendsto_apply_of_nativeZero
    (p q : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : IsNativeCarryRealOperatorZero 3 s.re s.im)
    (v : GenuineGreenCompletedSpace) :
    Tendsto
      (fun L : ℕ => finiteGenuineGreenCompletedOperator p q L s v)
      atTop
      (nhds (genuineGreenCompletedLimitOperator p q s v)) := by
  apply finiteGenuineGreenCompletedOperator_tendsto_apply_of_genuine_zero
    p q hp hpodd hq hqodd hs
  exact
    (isNativeCarryRealOperatorZero_three_iff_genuineContinuation_zero hs).1
      hzero

/--
The preceding limit is zero only after the separate Green-equilibrium datum
is supplied.
-/
theorem finiteGenuineGreenCompletedOperator_tendsto_zero_of_nativeZero_and_re_eq_half
    (p q : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : IsNativeCarryRealOperatorZero 3 s.re s.im)
    (hhalf : s.re = (1 : ℝ) / 2)
    (v : GenuineGreenCompletedSpace) :
    Tendsto
      (fun L : ℕ => finiteGenuineGreenCompletedOperator p q L s v)
      atTop (nhds 0) := by
  have hlimit :=
    finiteGenuineGreenCompletedOperator_tendsto_apply_of_nativeZero
      p q hp hpodd hq hqodd hs hzero v
  have hop : genuineGreenCompletedLimitOperator p q s = 0 :=
    (genuineGreenCompletedLimitOperator_eq_zero_iff_nativeZero_and_re_eq_half
      p q hp hq hs).2 ⟨hzero, hhalf⟩
  simpa [hop] using hlimit

end

end CPFormal.Analytic.Cp
