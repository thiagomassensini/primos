import CPFormal.Analytic.CpGenuineNativeRealBoundaryCrosswalk
import CPFormal.Analytic.CpGenuineGreenCompletedOperator
import Mathlib.Tactic.Linarith

/-!
# Native, Genuine, Green, and completed-operator crosswalk

This module composes the already audited layers without strengthening any of
them.

For the canonical real camera `3`, the raw primitive boundary closes exactly
when the scalar Genuine continuation vanishes.  A zero of the full native
operator retains one additional datum: compatibility with the quadratic carry
mass.  The Green channel of the completed operator retains exactly this radial
datum.

Inside the open Genuine strip, for native camera `3` and prime Green blocks
`p,q`, the kernel proves

```text
native zero
  <-> Genuine zero and re(s) = 1/2
  <-> Genuine zero and cross-prime Green closure
  <-> completed Genuine--Green operator zero.
```

This is an equality of the parameter loci where the full native predicate
holds and where the completed endomorphism is the zero map.  It is not an
equality or intertwiner of the operators themselves, and it does not assert
that a raw scalar Genuine zero reconstructs the mass discarded by scalar
compression.
-/

open scoped Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/--
The full native zero is the raw Genuine zero together with the quadratic carry
shell already present in the native operator domain.
-/
theorem isNativeCarryRealOperatorZero_three_iff_genuineContinuation_zero_and_re_eq_half
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    IsNativeCarryRealOperatorZero 3 s.re s.im ↔
      genuineContinuation s = 0 ∧ s.re = (1 : ℝ) / 2 := by
  unfold IsNativeCarryRealOperatorZero
  rw [nativeCarryRealPlaneMassCompatible_iff s.re s.im,
    nativeCarryRealBoundaryClosure_iff_genuineContinuation_zero hs]
  constructor <;> rintro ⟨h₁, h₂⟩
  · exact ⟨h₂, h₁⟩
  · exact ⟨h₂, h₁⟩

/--
Every native zero closes the two aligned Green coordinates separately.  The
scalar Genuine component supplies the raw boundary zero, while the native mass
component supplies the vanishing radial displacement.
-/
theorem nativeCarryRealOperatorZero_three_to_crossPrimeAlignedGreenClosure
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : IsNativeCarryRealOperatorZero 3 s.re s.im) :
    CrossPrimeAlignedGreenClosure p q s := by
  have hdata :=
    (isNativeCarryRealOperatorZero_three_iff_genuineContinuation_zero_and_re_eq_half
      hs).1 hzero
  have hcritical : criticalDisplacement s.re = 0 := by
    unfold criticalDisplacement
    linarith [hdata.2]
  exact crossPrimeAlignedGreenClosure_of_critical
    p q hp hq hs hdata.1 hcritical

/--
The Green limit vector vanishes at every full native zero.  This is the
operator-level form of retaining the quadratic mass after scalar synthesis.
-/
theorem nativeCarryRealOperatorZero_three_to_crossPrimeAlignedGreenLimitVector_zero
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : IsNativeCarryRealOperatorZero 3 s.re s.im) :
    crossPrimeAlignedGreenLimitVector p q s = 0 := by
  have hdata :=
    (isNativeCarryRealOperatorZero_three_iff_genuineContinuation_zero_and_re_eq_half
      hs).1 hzero
  apply
    (crossPrimeAlignedGreenLimitVector_eq_zero_iff_criticalDisplacement_eq_zero
      p q hp hq hs).2
  unfold criticalDisplacement
  linarith [hdata.2]

/--
The full native zero is equivalently a raw Genuine zero whose two aligned
Green coordinates close.  Neither conjunct may be dropped.
-/
theorem isNativeCarryRealOperatorZero_three_iff_genuineContinuation_zero_and_greenClosure
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    IsNativeCarryRealOperatorZero 3 s.re s.im ↔
      genuineContinuation s = 0 ∧ CrossPrimeAlignedGreenClosure p q s := by
  constructor
  · intro hzero
    have hdata :=
      (isNativeCarryRealOperatorZero_three_iff_genuineContinuation_zero_and_re_eq_half
        hs).1 hzero
    exact
      ⟨hdata.1,
        nativeCarryRealOperatorZero_three_to_crossPrimeAlignedGreenClosure
          p q hp hq hs hzero⟩
  · rintro ⟨hgenuine, hgreen⟩
    have hvector :
        crossPrimeAlignedGreenLimitVector p q s = 0 :=
      (crossPrimeAlignedGreenClosure_iff_limitVector_eq_zero
        p q hp hq hs hgenuine).1 hgreen
    have hcritical : criticalDisplacement s.re = 0 :=
      (crossPrimeAlignedGreenLimitVector_eq_zero_iff_criticalDisplacement_eq_zero
        p q hp hq hs).1 hvector
    apply
      (isNativeCarryRealOperatorZero_three_iff_genuineContinuation_zero_and_re_eq_half
        hs).2
    refine ⟨hgenuine, ?_⟩
    unfold criticalDisplacement at hcritical
    linarith

/--
Exact identity between the native zero locus and the parameter locus where the
Genuine--Green completed limit endomorphism is the zero map.
-/
theorem isNativeCarryRealOperatorZero_three_iff_genuineGreenCompletedLimitOperator_zero
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    IsNativeCarryRealOperatorZero 3 s.re s.im ↔
      genuineGreenCompletedLimitOperator p q s = 0 := by
  calc
    IsNativeCarryRealOperatorZero 3 s.re s.im ↔
        genuineContinuation s = 0 ∧ s.re = (1 : ℝ) / 2 :=
      isNativeCarryRealOperatorZero_three_iff_genuineContinuation_zero_and_re_eq_half
        hs
    _ ↔ genuineGreenCompletedLimitOperator p q s = 0 :=
      (genuineGreenCompletedLimitOperator_eq_zero_iff_re_eq_half
        p q hp hq hs).symm

/--
At a native zero, every finite completed operator converges strongly to zero.
The finite operators retain both the scalar Genuine channel and the Green
channel throughout the limit.
-/
theorem finiteGenuineGreenCompletedOperator_tendsto_zero_of_nativeCarryRealOperatorZero
    (p q : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : IsNativeCarryRealOperatorZero 3 s.re s.im)
    (v : GenuineGreenCompletedSpace) :
    Tendsto
      (fun L : ℕ => finiteGenuineGreenCompletedOperator p q L s v)
      atTop (nhds 0) := by
  have hdata :=
    (isNativeCarryRealOperatorZero_three_iff_genuineContinuation_zero_and_re_eq_half
      hs).1 hzero
  have hoperator :
      genuineGreenCompletedLimitOperator p q s = 0 :=
    (isNativeCarryRealOperatorZero_three_iff_genuineGreenCompletedLimitOperator_zero
      p q hp hq hs).1 hzero
  have hlimit :=
    finiteGenuineGreenCompletedOperator_tendsto_apply_of_genuine_zero
      p q hp hpodd hq hqodd hs hdata.1 v
  simpa [hoperator] using hlimit

end

end CPFormal.Analytic.Cp
