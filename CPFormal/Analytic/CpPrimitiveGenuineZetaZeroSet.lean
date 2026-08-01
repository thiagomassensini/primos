import CPFormal.Analytic.CpGenuineNativeRealBoundaryCrosswalk
import CPFormal.Analytic.CpGenuineRiemannZetaIdentification

/-!
# The primitive, Genuine and Riemann-zeta zero sets

The primitive camera-three zero is defined here by boundary closure alone.
No carry-mass or energy-compatibility condition is part of this predicate.

The existing real/complex packaging crosswalk proves that this primitive
closure is exactly a zero of `genuineContinuation` in the open critical
strip.  The existing Riemann-zeta identification, whose proof uses Mathlib's
analytic identity principle, then makes it exactly a zero of `riemannZeta`.

Consequently the primitive zero-rigidity statement is equivalent to
Riemann-zeta zero confinement on the open critical strip.  This module proves
that equivalence; it does not assume either side.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-- The energy-free zero predicate of the primitive camera-three operator. -/
def IsPrimitiveNativeCarryRealOperatorZero
    (sigma time : ℝ) : Prop :=
  NativeCarryRealOperatorBoundaryClosesAt 3 sigma time

/-- Native real coordinates with `0 < sigma < 1` give a point of the open
critical strip. -/
theorem nativeCarryRealPlaneParameter_mem_genuineCriticalStrip
    {sigma time : ℝ}
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    nativeCarryRealPlaneParameter sigma time ∈ genuineCriticalStrip := by
  exact ⟨hsigma0, hsigma1⟩

/-- The primitive real operator and the canonical Genuine continuation have
literally the same zeros in the open critical strip. -/
theorem isPrimitiveNativeCarryRealOperatorZero_iff_genuineContinuation_zero
    (sigma time : ℝ)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    IsPrimitiveNativeCarryRealOperatorZero sigma time ↔
      genuineContinuation
          (nativeCarryRealPlaneParameter sigma time) = 0 := by
  simpa [IsPrimitiveNativeCarryRealOperatorZero] using
    (nativeCarryRealBoundaryClosure_iff_genuineContinuation_zero
      (s := nativeCarryRealPlaneParameter sigma time)
      (nativeCarryRealPlaneParameter_mem_genuineCriticalStrip
        hsigma0 hsigma1))

/-- The identity-principle identification makes Genuine and Riemann zeta have
literally the same zeros throughout the open critical strip. -/
theorem genuineContinuation_zero_iff_riemannZeta_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    genuineContinuation s = 0 ↔ riemannZeta s = 0 := by
  rw [genuineContinuation_eq_riemannZeta hs]

/-- Direct zero-set identity between the energy-free primitive operator and
Mathlib's Riemann zeta. -/
theorem isPrimitiveNativeCarryRealOperatorZero_iff_riemannZeta_zero
    (sigma time : ℝ)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    IsPrimitiveNativeCarryRealOperatorZero sigma time ↔
      riemannZeta (nativeCarryRealPlaneParameter sigma time) = 0 := by
  calc
    IsPrimitiveNativeCarryRealOperatorZero sigma time ↔
        genuineContinuation
            (nativeCarryRealPlaneParameter sigma time) = 0 :=
      isPrimitiveNativeCarryRealOperatorZero_iff_genuineContinuation_zero
        sigma time hsigma0 hsigma1
    _ ↔ riemannZeta
          (nativeCarryRealPlaneParameter sigma time) = 0 :=
      genuineContinuation_zero_iff_riemannZeta_zero
        (nativeCarryRealPlaneParameter_mem_genuineCriticalStrip
          hsigma0 hsigma1)

/-- Confinement of every energy-free primitive zero to `sigma = 1/2`. -/
def PrimitiveNativeCarryRealZeroConfinement : Prop :=
  ∀ {sigma time : ℝ}, 0 < sigma → sigma < 1 →
    IsPrimitiveNativeCarryRealOperatorZero sigma time →
      sigma = (1 : ℝ) / 2

/-- Riemann-zeta zero confinement on the open critical strip. -/
def RiemannZetaZeroConfinementOnOpenCriticalStrip : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    riemannZeta s = 0 →
      s.re = (1 : ℝ) / 2

/-- Removing mass compatibility does not produce a weaker auxiliary theorem:
primitive zero confinement is exactly Riemann-zeta zero confinement. -/
theorem primitiveNativeCarryRealZeroConfinement_iff_riemannZeta :
    PrimitiveNativeCarryRealZeroConfinement ↔
      RiemannZetaZeroConfinementOnOpenCriticalStrip := by
  constructor
  · intro hprimitive s hs hzero
    have hparameter :
        nativeCarryRealPlaneParameter s.re s.im = s := by
      apply Complex.ext <;> rfl
    have hprimitiveZero :
        IsPrimitiveNativeCarryRealOperatorZero s.re s.im := by
      apply
        (isPrimitiveNativeCarryRealOperatorZero_iff_riemannZeta_zero
          s.re s.im hs.1 hs.2).2
      rw [hparameter]
      exact hzero
    exact hprimitive hs.1 hs.2 hprimitiveZero
  · intro hzeta sigma time hsigma0 hsigma1 hprimitiveZero
    have hzero :
        riemannZeta
            (nativeCarryRealPlaneParameter sigma time) = 0 :=
      (isPrimitiveNativeCarryRealOperatorZero_iff_riemannZeta_zero
        sigma time hsigma0 hsigma1).1 hprimitiveZero
    have hre :=
      hzeta
        (nativeCarryRealPlaneParameter_mem_genuineCriticalStrip
          hsigma0 hsigma1)
        hzero
    simpa using hre

/-- The energy-free primitive confinement proposition is definitionally the
real-plane zero-rigidity target already isolated by the repository. -/
theorem primitiveNativeCarryRealZeroConfinement_iff_zeroRigidity :
    PrimitiveNativeCarryRealZeroConfinement ↔
      NativeCarryRealPlaneZeroRigidity := by
  rfl

/-- Therefore the repository's remaining native zero-rigidity target is
equivalent to Riemann-zeta zero confinement in the open critical strip. -/
theorem nativeCarryRealPlaneZeroRigidity_iff_riemannZeta :
    NativeCarryRealPlaneZeroRigidity ↔
      RiemannZetaZeroConfinementOnOpenCriticalStrip :=
  primitiveNativeCarryRealZeroConfinement_iff_zeroRigidity.symm.trans
    primitiveNativeCarryRealZeroConfinement_iff_riemannZeta

end

end CPFormal.Analytic.Cp
