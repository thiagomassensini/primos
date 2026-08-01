import CPFormal.Analytic.CpGenuineNativeRealBoundaryCrosswalk
import CPFormal.Analytic.CpGenuineGreenCompletedOperator
import CPFormal.Analytic.CpNativeCarryRealOperatorConfinement

/-!
# Certified frontier: an off-critical Genuine zero cannot carry native mass

This file preserves the exact diagnostic discovered by the red draft probe,
but turns it into a kernel-checked conditional theorem.

Assume simultaneously:

* the unique real/Genuine operator closes;
* the radial coordinate is off the quadratic carry shell;
* the Green-completed operator therefore remains nonzero.

The theorem transports the Genuine zero to the identical real camera closure
and uses an explicit native mass-compatibility hypothesis.  It uses no unsafe
declaration or proof placeholder.  The old red CI result identified precisely
this hypothesis; raw scalar closure alone still does not supply it.
-/

open scoped Topology

namespace CPFormal.Analytic.Cp

noncomputable section

/--
Direct off-critical carry-cost contradiction.

The first two channels are already available:

```text
genuineContinuation s = 0
  -> real camera-three boundary closure

s.re != 1/2
  -> the Genuine--Green completed operator is nonzero.
```

To contradict the second statement through the native identity, the theorem
retains the pre-compression mass law as an explicit typed input.  This is the
exact datum exposed by the former diagnostic stop.
-/
theorem genuine_zero_off_critical_cost_contradiction_probe
    {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hmass : NativeCarryRealPlaneMassCompatible s.re s.im)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    False := by
  have hreal :
      NativeCarryRealOperatorBoundaryClosesAt 3 s.re s.im :=
    (nativeCarryRealBoundaryClosure_iff_genuineContinuation_zero hs).2 hzero

  have hcompleted_ne :
      genuineGreenCompletedLimitOperator 3 5 s ≠ 0 :=
    genuine_zero_has_nonzero_completed_limitOperator_of_re_ne_half
      3 5 (by norm_num) (by norm_num) hs hzero hoff

  have hnative :
      IsNativeCarryRealOperatorZero 3 s.re s.im := by
    exact ⟨hmass, hreal⟩

  have hcritical : s.re = (1 : ℝ) / 2 :=
    nativeCarryRealOperatorZero_sigma_eq_half hnative

  have hcompleted_zero :
      genuineGreenCompletedLimitOperator 3 5 s = 0 :=
    (genuineGreenCompletedLimitOperator_eq_zero_iff_re_eq_half
      3 5 (by norm_num) (by norm_num) hs).2 ⟨hzero, hcritical⟩

  exact hcompleted_ne hcompleted_zero

end

end CPFormal.Analytic.Cp
