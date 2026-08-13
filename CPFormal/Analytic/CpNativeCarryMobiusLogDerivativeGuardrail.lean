import CPFormal.Analytic.CpNativeCarryRealOperatorZero
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Mobius / log-derivative guardrail for native carry

This module records, in the Lean kernel, the exact arithmetic circuit behind
the prime-power signal used by the logarithmic derivative of Riemann zeta.

There are three logically separate facts:

* positional carry fixes the unique quadratic mass-equilibrium shell before
  any zero or arithmetic projection is considered;
* a native zero means boundary vanishing and does not include that equilibrium
  condition in its definition;
* the von Mangoldt signal is obtained from the logarithm on all positive
  integers by Dirichlet convolution with Mobius, and its L-series is the
  negative logarithmic derivative of Riemann zeta on `re(s) > 1`.

The convolution by the arithmetic zeta function reconstructs the original
integer logarithm exactly. Thus the prime-power support is an invertible
arithmetic resolution of the logarithmic field, not a source of the quadratic
carry equilibrium and not a restriction inserted into the zero predicate.

This file does not formalize the classical explicit formula and does not claim
logical circularity of that formula. It isolates the reversible Mobius
round-trip and keeps it separate from both carry equilibrium and boundary
vanishing.
-/

open scoped BigOperators LSeries.notation

namespace CPFormal.Analytic.Cp

noncomputable section

/-- The prime-power logarithmic signal is the Mobius deconvolution of the
logarithm on all positive integers. -/
theorem integerLog_mul_moebius_eq_primePowerSignal :
    ArithmeticFunction.log *
        (ArithmeticFunction.moebius : ArithmeticFunction ℝ) =
      ArithmeticFunction.vonMangoldt :=
  ArithmeticFunction.log_mul_moebius_eq_vonMangoldt

/-- Summing the prime-power signal over divisors reconstructs the integer
logarithm exactly. -/
theorem primePowerSignal_mul_zeta_eq_integerLog :
    ArithmeticFunction.vonMangoldt *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) =
      ArithmeticFunction.log :=
  ArithmeticFunction.vonMangoldt_mul_zeta

/-- The full arithmetic round-trip is exact: extract the prime-power signal by
Mobius and reconstruct the original integer logarithm by divisor summation. -/
theorem integerLog_roundTrip_through_primePowerSignal :
    (ArithmeticFunction.log *
        (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) =
      ArithmeticFunction.log := by
  rw [integerLog_mul_moebius_eq_primePowerSignal,
    primePowerSignal_mul_zeta_eq_integerLog]

/-- Pointwise form of the reconstruction identity. -/
theorem primePowerSignal_divisorSum_eq_integerLog (n : ℕ) :
    (∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d) =
      Real.log n :=
  ArithmeticFunction.vonMangoldt_sum

/-- The extracted signal is supported exactly on prime powers. -/
theorem primePowerSignal_ne_zero_iff_primePower {n : ℕ} :
    ArithmeticFunction.vonMangoldt n ≠ 0 ↔ IsPrimePow n :=
  ArithmeticFunction.vonMangoldt_ne_zero_iff

/-- On the half-plane of absolute convergence, the L-series of the extracted
prime-power signal is exactly the negative logarithmic derivative of Riemann
zeta. -/
theorem primePowerSignal_lSeries_eq_riemannZeta_logDerivative
    {s : ℂ} (hs : 1 < s.re) :
    L (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      -deriv riemannZeta s / riemannZeta s := by
  simpa using
    (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs)

/--
Kernel-level separation checkpoint. The quadratic carry equilibrium and the
arithmetic log-derivative readout hold side by side, before any zero predicate
is used.
-/
theorem quadraticCarryEquilibrium_and_primePowerReadout
    (sigma time : ℝ) {s : ℂ} (hs : 1 < s.re) :
    (NativeCarryRealPlaneMassCompatible sigma time ↔
        sigma = (1 : ℝ) / 2) ∧
      (L (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s =
        -deriv riemannZeta s / riemannZeta s) := by
  exact
    ⟨nativeCarryRealPlaneMassCompatible_iff sigma time,
      primePowerSignal_lSeries_eq_riemannZeta_logDerivative hs⟩

end

end CPFormal.Analytic.Cp
