import CPFormal.Analytic.CpC2GpreGreenActivationGuard
import CPFormal.Analytic.CpConnectedC2Defect
import CPFormal.Analytic.CpGenuineZeroConfinementAttempt
import Mathlib.Tactic.Linarith

/-!
# Quadratic C2 frontier for raw Genuine zeros

The direct CI probe first proved the available scalar statement

```text
genuineContinuation s = 0
  -> Tendsto (tagged C2/Gpre synthesis at s) 0
```

and then left exactly

```text
crossPrimeRadialC2Detector p q (criticalDisplacement s.re) = 0
```

as an unsolved goal.  Thus the scalar tagged synthesis and the positive
quadratic radial detector are not identified by the current library.

This module removes the failing probe and records the exact missing activation
map.  For every fixed tagged atlas family, activation of the radial C2
detector is equivalent to:

* closure of that detector on the raw Genuine kernel;
* activation of the aligned Green closure;
* strong off-critical nonvanishing of the Genuine continuation;
* promotion of every raw Genuine zero to a full native operator zero.

No instance of the activation proposition is declared.
-/

open scoped Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/--
The exact quadratic activation requested by the direct probe: the already
proved scalar tagged-synthesis closure must force closure of the positive
radial C2 detector.
-/
def C2GpreTaggedSynthesisActivatesRadialC2Detector
    (verticalRatio : ℝ) {p q : ℕ}
    (family : C2GpreActiveCofinalAtlasFamily p q) : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    genuineContinuation s = 0 →
    Tendsto
      (fun L : ℕ =>
        c2GpreNormalizedCofinalTaggedSynthesis
          verticalRatio family L s)
      atTop (nhds 0) →
    crossPrimeRadialC2Detector p q
      (criticalDisplacement s.re) = 0

/--
Because the scalar tagged synthesis already closes at every Genuine zero, its
quadratic activation is exactly closure of the radial C2 detector on the
Genuine kernel.
-/
theorem c2GpreTaggedSynthesisActivatesRadialC2Detector_iff_kernelClosure
    (verticalRatio : ℝ) {p q : ℕ}
    (family : C2GpreActiveCofinalAtlasFamily p q)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q) :
    C2GpreTaggedSynthesisActivatesRadialC2Detector
        verticalRatio family ↔
      GenuineKernelClosesRadialC2Detector p q := by
  constructor
  · intro hactivate s hzero hs
    exact hactivate hs hzero
      (c2GpreNormalizedCofinalTaggedSynthesis_tendsto_zero_of_genuine_zero
        verticalRatio family hp hpodd hq hqodd hs hzero)
  · intro hkernel s hs hzero _hscalar
    exact hkernel hzero hs

/-- The missing quadratic activation has exactly the strength of the desired
strong nonvanishing theorem. -/
theorem c2GpreTaggedSynthesisActivatesRadialC2Detector_iff_strongNonvanishing
    (verticalRatio : ℝ) {p q : ℕ}
    (family : C2GpreActiveCofinalAtlasFamily p q)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q) :
    C2GpreTaggedSynthesisActivatesRadialC2Detector
        verticalRatio family ↔
      GenuineStrongNonvanishingInStrip := by
  calc
    C2GpreTaggedSynthesisActivatesRadialC2Detector
          verticalRatio family ↔
        GenuineKernelClosesRadialC2Detector p q :=
      c2GpreTaggedSynthesisActivatesRadialC2Detector_iff_kernelClosure
        verticalRatio family hp hpodd hq hqodd
    _ ↔ GenuineStrongNonvanishingInStrip :=
      genuineKernelClosesRadialC2Detector_iff_strongNonvanishing
        p q hp hq

/--
Activating the radial C2 detector and activating the aligned Green channel are
the same missing map, not two independent hypotheses.
-/
theorem c2GpreTaggedRadialC2Activation_iff_greenActivation
    (verticalRatio : ℝ) {p q : ℕ}
    (family : C2GpreActiveCofinalAtlasFamily p q)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q) :
    C2GpreTaggedSynthesisActivatesRadialC2Detector
        verticalRatio family ↔
      C2GpreTaggedSynthesisActivatesGreenClosure
        verticalRatio family := by
  calc
    C2GpreTaggedSynthesisActivatesRadialC2Detector
          verticalRatio family ↔
        GenuineStrongNonvanishingInStrip :=
      c2GpreTaggedSynthesisActivatesRadialC2Detector_iff_strongNonvanishing
        verticalRatio family hp hpodd hq hqodd
    _ ↔ C2GpreTaggedSynthesisActivatesGreenClosure
          verticalRatio family :=
      (c2GpreTaggedSynthesisActivatesGreenClosure_iff_strongNonvanishing
        verticalRatio family hp hpodd hq hqodd).symm

/--
The requested quadratic activation is also exactly promotion of raw Genuine
zeros to full native zeros from the preceding confinement-frontier module.
-/
theorem c2GpreTaggedRadialC2Activation_iff_genuineZerosPromoteToNativeZeros
    (verticalRatio : ℝ) {p q : ℕ}
    (family : C2GpreActiveCofinalAtlasFamily p q)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q) :
    C2GpreTaggedSynthesisActivatesRadialC2Detector
        verticalRatio family ↔
      GenuineZerosPromoteToNativeZeros := by
  calc
    C2GpreTaggedSynthesisActivatesRadialC2Detector
          verticalRatio family ↔
        GenuineStrongNonvanishingInStrip :=
      c2GpreTaggedSynthesisActivatesRadialC2Detector_iff_strongNonvanishing
        verticalRatio family hp hpodd hq hqodd
    _ ↔ GenuineZerosPromoteToNativeZeros :=
      genuineZerosPromoteToNativeZeros_iff_strongNonvanishing.symm

/-- Conditional composition of the proved scalar closure with the exact
quadratic activation map. -/
theorem genuineContinuation_zero_to_radialC2Detector_zero_of_taggedActivation
    (verticalRatio : ℝ) {p q : ℕ}
    (family : C2GpreActiveCofinalAtlasFamily p q)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    (hactivate :
      C2GpreTaggedSynthesisActivatesRadialC2Detector
        verticalRatio family)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    crossPrimeRadialC2Detector p q
      (criticalDisplacement s.re) = 0 :=
  hactivate hs hzero
    (c2GpreNormalizedCofinalTaggedSynthesis_tendsto_zero_of_genuine_zero
      verticalRatio family hp hpodd hq hqodd hs hzero)

/-- Pointwise, at a Genuine zero, radial C2 closure and aligned Green closure
have the same zero locus. -/
theorem radialC2Detector_zero_iff_crossPrimeAlignedGreenClosure
    (p q : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    crossPrimeRadialC2Detector p q
        (criticalDisplacement s.re) = 0 ↔
      CrossPrimeAlignedGreenClosure p q s := by
  calc
    crossPrimeRadialC2Detector p q
          (criticalDisplacement s.re) = 0 ↔
        criticalDisplacement s.re = 0 :=
      crossPrimeRadialC2Detector_eq_zero_iff
        p q hp hq (criticalDisplacement s.re)
    _ ↔ CrossPrimeAlignedGreenClosure p q s :=
      (crossPrimeAlignedGreenClosure_iff_criticalDisplacement_eq_zero
        p q hp hpodd hq hqodd hs hzero).symm

/-- Once the exact activation is supplied, the connected detector forces the
critical displacement to vanish. -/
theorem criticalDisplacement_eq_zero_of_taggedRadialC2Activation
    (verticalRatio : ℝ) {p q : ℕ}
    (family : C2GpreActiveCofinalAtlasFamily p q)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    (hactivate :
      C2GpreTaggedSynthesisActivatesRadialC2Detector
        verticalRatio family)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    criticalDisplacement s.re = 0 :=
  (crossPrimeRadialC2Detector_eq_zero_iff
    p q hp hq (criticalDisplacement s.re)).1
      (genuineContinuation_zero_to_radialC2Detector_zero_of_taggedActivation
        verticalRatio family hp hpodd hq hqodd hactivate hs hzero)

/-- Hence the conditional C2 route reaches the critical line. -/
theorem genuineContinuation_zero_re_eq_half_of_taggedRadialC2Activation
    (verticalRatio : ℝ) {p q : ℕ}
    (family : C2GpreActiveCofinalAtlasFamily p q)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    (hactivate :
      C2GpreTaggedSynthesisActivatesRadialC2Detector
        verticalRatio family)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    s.re = (1 : ℝ) / 2 := by
  have hdelta :=
    criticalDisplacement_eq_zero_of_taggedRadialC2Activation
      verticalRatio family hp hpodd hq hqodd hactivate hs hzero
  unfold criticalDisplacement at hdelta
  linarith

/-- The same conditional chain promotes the raw Genuine zero to the native
operator zero used by the already proved confinement theorem. -/
theorem genuineContinuation_zero_to_nativeOperatorZero_of_taggedRadialC2Activation
    (verticalRatio : ℝ) {p q : ℕ}
    (family : C2GpreActiveCofinalAtlasFamily p q)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    (hactivate :
      C2GpreTaggedSynthesisActivatesRadialC2Detector
        verticalRatio family)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    IsNativeCarryRealOperatorZero 3 s.re s.im := by
  apply
    (isNativeCarryRealOperatorZero_three_iff_genuineContinuation_zero_and_re_eq_half
      hs).2
  exact
    ⟨hzero,
      genuineContinuation_zero_re_eq_half_of_taggedRadialC2Activation
        verticalRatio family hp hpodd hq hqodd hactivate hs hzero⟩

end

end CPFormal.Analytic.Cp
