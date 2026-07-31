import CPFormal.Analytic.CpNativeGenuineGreenCompletedCrosswalk
import CPFormal.Analytic.CpGenuineGreenKernelInclusion
import CPFormal.Analytic.CpGenuineRealPlaneReconstruction
import Mathlib.Tactic.Linarith

/-!
# Frontier of raw Genuine-zero confinement

The direct kernel probe

```text
genuineContinuation s = 0 -> IsNativeCarryRealOperatorZero 3 s.re s.im
```

reduces exactly to the unsolved radial goal `s.re = 1 / 2`.  This module
removes the failing probe and records the strongest assumption-transparent
composition accepted by the kernel.

It proves that promoting every raw Genuine zero to a full native zero is
equivalent to each of the following formulations:

* inclusion of the raw Genuine kernel in the cross-prime Green limit kernel;
* closure of the completed Genuine--Green operator at every Genuine zero;
* reconstruction of a pre-compression lift from every raw boundary closure;
* strong nonvanishing of the Genuine continuation off the critical line.

No instance of these equivalent global propositions is declared.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-- The exact global arrow requested by the confinement attempt. -/
def GenuineZerosPromoteToNativeZeros : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    genuineContinuation s = 0 →
      IsNativeCarryRealOperatorZero 3 s.re s.im

/--
Pointwise frontier: a full native zero is exactly a raw Genuine zero together
with vanishing of the orthogonal Green limit vector.
-/
theorem isNativeCarryRealOperatorZero_three_iff_genuine_zero_and_greenLimit_zero
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    IsNativeCarryRealOperatorZero 3 s.re s.im ↔
      genuineContinuation s = 0 ∧
        crossPrimeAlignedGreenLimitVector p q s = 0 := by
  constructor
  · intro hnative
    have hdata :=
      (isNativeCarryRealOperatorZero_three_iff_genuineContinuation_zero_and_re_eq_half
        hs).1 hnative
    exact
      ⟨hdata.1,
        nativeCarryRealOperatorZero_three_to_crossPrimeAlignedGreenLimitVector_zero
          p q hp hq hs hnative⟩
  · rintro ⟨hzero, hgreen⟩
    have hcritical : criticalDisplacement s.re = 0 :=
      (crossPrimeAlignedGreenLimitVector_eq_zero_iff_criticalDisplacement_eq_zero
        p q hp hq hs).1 hgreen
    apply
      (isNativeCarryRealOperatorZero_three_iff_genuineContinuation_zero_and_re_eq_half
        hs).2
    refine ⟨hzero, ?_⟩
    unfold criticalDisplacement at hcritical
    linarith

/--
Globally, the missing raw-Genuine-to-native arrow is exactly inclusion of the
Genuine kernel in the Green limit kernel.
-/
theorem genuineZerosPromoteToNativeZeros_iff_greenLimitKernel
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    GenuineZerosPromoteToNativeZeros ↔
      GenuineKernelIncludedInGreenLimitKernel p q := by
  constructor
  · intro hpromote s hzero hs
    exact
      ((isNativeCarryRealOperatorZero_three_iff_genuine_zero_and_greenLimit_zero
        p q hp hq hs).1 (hpromote hs hzero)).2
  · intro hgreen s hs hzero
    apply
      (isNativeCarryRealOperatorZero_three_iff_genuine_zero_and_greenLimit_zero
        p q hp hq hs).2
    exact ⟨hzero, hgreen hzero hs⟩

/--
The same arrow is exactly closure of the completed Genuine--Green operator at
every raw Genuine zero.
-/
theorem genuineZerosPromoteToNativeZeros_iff_completedOperator
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    GenuineZerosPromoteToNativeZeros ↔
      GenuineKernelClosesCompletedLimitOperator p q := by
  calc
    GenuineZerosPromoteToNativeZeros ↔
        GenuineKernelIncludedInGreenLimitKernel p q :=
      genuineZerosPromoteToNativeZeros_iff_greenLimitKernel p q hp hq
    _ ↔ GenuineKernelClosesCompletedLimitOperator p q :=
      genuineKernelIncludedInGreenLimitKernel_iff_completedOperator
        p q hp hq

/--
The direct promotion arrow is also exactly reconstruction of the retained
pre-compression state from every raw real-plane boundary closure.
-/
theorem genuineZerosPromoteToNativeZeros_iff_precompressionLift :
    GenuineZerosPromoteToNativeZeros ↔
      NativeCarryRealPlaneBoundaryClosureLiftsToPrecompression := by
  constructor
  · intro hpromote
    apply
      (boundaryClosureLiftsToPrecompression_iff_zeroRigidity).2
    intro sigma time hsigma0 hsigma1 hclose
    let s : ℂ := nativeCarryRealPlaneParameter sigma time
    have hs : s ∈ genuineCriticalStrip := by
      constructor
      · simpa [s] using hsigma0
      · simpa [s] using hsigma1
    have hoperatorAt :
        NativeCarryRealOperatorBoundaryClosesAt 3 sigma time :=
      (nativeCarryRealOperatorBoundaryClosesAt_three sigma time).2 hclose
    have hoperator :
        NativeCarryRealOperatorBoundaryClosesAt 3 s.re s.im := by
      simpa [s] using hoperatorAt
    have hzero : genuineContinuation s = 0 :=
      (nativeCarryRealBoundaryClosure_iff_genuineContinuation_zero hs).1
        hoperator
    have hnative := hpromote hs hzero
    simpa [s] using
      (nativeCarryRealOperatorZero_sigma_eq_half hnative)
  · intro hlift s hs hzero
    have hoperator :
        NativeCarryRealOperatorBoundaryClosesAt 3 s.re s.im :=
      (nativeCarryRealBoundaryClosure_iff_genuineContinuation_zero hs).2 hzero
    have hclose :
        NativeCarryRealPlaneBoundaryClosesAt s.re s.im :=
      (nativeCarryRealOperatorBoundaryClosesAt_three s.re s.im).1 hoperator
    have hprecompression :
        NativeCarryRealPlaneBoundaryClosureHasPrecompressionLift s.re s.im :=
      hlift hs.1 hs.2 hclose
    exact
      ⟨boundaryClosurePrecompressionLift_massCompatible hprecompression,
        hoperator⟩

/-- The requested promotion is equivalent to strong off-critical nonvanishing. -/
theorem genuineZerosPromoteToNativeZeros_iff_strongNonvanishing :
    GenuineZerosPromoteToNativeZeros ↔
      GenuineStrongNonvanishingInStrip := by
  constructor
  · intro hpromote s hs hoff hzero
    exact
      hoff
        (nativeCarryRealOperatorZero_sigma_eq_half
          (hpromote hs hzero))
  · intro hstrong s hs hzero
    apply
      (isNativeCarryRealOperatorZero_three_iff_genuineContinuation_zero_and_re_eq_half
        hs).2
    refine ⟨hzero, ?_⟩
    by_contra hoff
    exact (hstrong hs hoff) hzero

/--
Once any one of the equivalent Green-kernel formulations is supplied, all
remaining arrows compose to the full native zero.
-/
theorem genuineContinuation_zero_to_nativeCarryRealOperatorZero_three_of_greenKernel
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hgreen : GenuineKernelIncludedInGreenLimitKernel p q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    IsNativeCarryRealOperatorZero 3 s.re s.im :=
  (genuineZerosPromoteToNativeZeros_iff_greenLimitKernel p q hp hq).2
    hgreen hs hzero

/-- The preceding composition reaches the desired confinement conclusion. -/
theorem genuineContinuation_zero_re_eq_half_of_greenKernel
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hgreen : GenuineKernelIncludedInGreenLimitKernel p q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    s.re = (1 : ℝ) / 2 :=
  nativeCarryRealOperatorZero_sigma_eq_half
    (genuineContinuation_zero_to_nativeCarryRealOperatorZero_three_of_greenKernel
      p q hp hq hgreen hs hzero)

end

end CPFormal.Analytic.Cp
