import CPFormal.Analytic.CpGenuineNativeRealBoundaryCrosswalk
import CPFormal.Analytic.CpGenuineGreenCompletedOperator
import CPFormal.Analytic.CpNativeCarryRealOperatorConfinement
import Mathlib.Tactic.Aesop

/-!
# Diagnostic probe: can an off-critical Genuine zero survive the carry cost?

This file intentionally asks the Lean kernel for the direct contradiction
suggested by the native carry architecture.

Assume simultaneously:

* the unique real/Genuine operator closes;
* the radial coordinate is off the quadratic carry shell;
* the Green-completed operator therefore remains nonzero.

The probe transports the Genuine zero to the identical real camera closure and
then tries to use the native/completed identity.  It contains no axiom, `sorry`
or `admit`.  The expected red CI result is the exact proposition that the
current library still cannot derive from raw closure.

This is a diagnostic draft probe, not a claimed theorem.
-/

open scoped Topology

namespace CPFormal.Analytic.Cp

noncomputable section

/--
Direct off-critical contradiction probe.

The first two channels are already available:

```text
genuineContinuation s = 0
  -> real camera-three boundary closure

s.re != 1/2
  -> the Genuine--Green completed operator is nonzero.
```

To contradict the second statement through the native identity, Lean must
construct the complete native zero from the same real closure.  The unfinished
subgoal emitted by the kernel records exactly what datum is still missing.
-/
theorem genuine_zero_off_critical_cost_contradiction_probe
    {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
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
    constructor
    · aesop
    · exact hreal

  have hcritical : s.re = (1 : ℝ) / 2 :=
    nativeCarryRealOperatorZero_sigma_eq_half hnative

  have hcompleted_zero :
      genuineGreenCompletedLimitOperator 3 5 s = 0 :=
    (genuineGreenCompletedLimitOperator_eq_zero_iff_re_eq_half
      3 5 (by norm_num) (by norm_num) hs).2 ⟨hzero, hcritical⟩

  exact hcompleted_ne hcompleted_zero

end

end CPFormal.Analytic.Cp
