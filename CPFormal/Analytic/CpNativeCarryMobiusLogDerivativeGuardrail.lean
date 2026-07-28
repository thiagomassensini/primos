import CPFormal.Analytic.CpNativeCarryRealOperatorConfinement
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Mobius / log-derivative guardrail for native carry

This module records, in the Lean kernel, the exact arithmetic circuit behind
the prime-power signal used by the logarithmic derivative of Riemann zeta.

There are two logically separate layers:

* the native carry operator has its real zero set confined by quadratic mass
  compatibility, before any arithmetic projection;
* the von Mangoldt signal is obtained from the logarithm on all positive
  integers by Dirichlet convolution with Mobius, and its L-series is the
  negative logarithmic derivative of Riemann zeta on `re(s) > 1`.

The convolution by the arithmetic zeta function reconstructs the original
integer logarithm exactly.  Thus the prime-power support is an invertible
arithmetic resolution of the logarithmic field, not an additional source of
the already-proved native carry confinement.

This file does not formalize the classical explicit formula and does not claim
logical circularity of that formula.  It isolates the reversible Mobius
round-trip and keeps it separate from the native carry zero theorem.
-/

open scoped BigOperators
  ArithmeticFunction.zeta
  ArithmeticFunction.Moebius
  ArithmeticFunction.vonMangoldt
  LSeries.notation

namespace CPFormal.Analytic.Cp

open ArithmeticFunction

noncomputable section

/-- The prime-power logarithmic signal is the Mobius deconvolution of the
logarithm on all positive integers. -/
theorem integerLog_mul_moebius_eq_primePowerSignal :
    ArithmeticFunction.log * (μ : ArithmeticFunction ℝ) = Λ :=
  ArithmeticFunction.log_mul_moebius_eq_vonMangoldt

/-- Summing the prime-power signal over divisors reconstructs the integer
logarithm exactly. -/
theorem primePowerSignal_mul_zeta_eq_integerLog :
    Λ * (ζ : ArithmeticFunction ℝ) = ArithmeticFunction.log :=
  ArithmeticFunction.vonMangoldt_mul_zeta

/-- The full arithmetic round-trip is exact: extract the prime-power signal by
Mobius and reconstruct the original integer logarithm by divisor summation. -/
theorem integerLog_roundTrip_through_primePowerSignal :
    (ArithmeticFunction.log * (μ : ArithmeticFunction ℝ)) *
        (ζ : ArithmeticFunction ℝ) =
      ArithmeticFunction.log := by
  rw [integerLog_mul_moebius_eq_primePowerSignal,
    primePowerSignal_mul_zeta_eq_integerLog]

/-- Pointwise form of the reconstruction identity. -/
theorem primePowerSignal_divisorSum_eq_integerLog (n : ℕ) :
    (∑ d ∈ n.divisors, Λ d) = Real.log n :=
  ArithmeticFunction.vonMangoldt_sum

/-- The extracted signal is supported exactly on prime powers. -/
theorem primePowerSignal_ne_zero_iff_primePower {n : ℕ} :
    Λ n ≠ 0 ↔ IsPrimePow n :=
  ArithmeticFunction.vonMangoldt_ne_zero_iff

/-- On the half-plane of absolute convergence, the L-series of the extracted
prime-power signal is exactly the negative logarithmic derivative of Riemann
zeta. -/
theorem primePowerSignal_lSeries_eq_riemannZeta_logDerivative
    {s : ℂ} (hs : 1 < s.re) :
    L ↗Λ s = -deriv riemannZeta s / riemannZeta s :=
  ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

/-- Kernel-level separation checkpoint.  The native carry confinement theorem
and the arithmetic log-derivative readout hold side by side; no implication in
either direction is inserted into their definitions. -/
theorem nativeCarryConfinement_and_primePowerReadout
    (camera : ℕ) (sigma time : ℝ) {s : ℂ} (hs : 1 < s.re) :
    (IsNativeCarryRealOperatorZero camera sigma time ↔
        sigma = (1 : ℝ) / 2 ∧
          IsNativeCarryRealOperatorResonance camera time) ∧
      (L ↗Λ s = -deriv riemannZeta s / riemannZeta s) := by
  exact
    ⟨isNativeCarryRealOperatorZero_iff camera sigma time,
      primePowerSignal_lSeries_eq_riemannZeta_logDerivative hs⟩

end

end CPFormal.Analytic.Cp
