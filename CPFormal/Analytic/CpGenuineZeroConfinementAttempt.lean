import CPFormal.Analytic.CpNativeGenuineGreenCompletedCrosswalk

/-!
# Direct Genuine-zero confinement probe

This file asks Lean for the exact arrow requested in the audit:

```text
raw Genuine zero -> full native zero -> critical line.
```

The first CI pass deliberately presents the direct composition to the kernel,
without adding axioms or replacing the missing radial datum.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

theorem genuineContinuation_zero_to_nativeCarryRealOperatorZero_three_probe
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    IsNativeCarryRealOperatorZero 3 s.re s.im := by
  rw [
    isNativeCarryRealOperatorZero_three_iff_genuineContinuation_zero_and_re_eq_half
      hs
  ]
  exact ⟨hzero, by aesop⟩

end

end CPFormal.Analytic.Cp
