import CPFormal.Analytic.CpGenuineNativeRealBoundaryCrosswalk
import CPFormal.Analytic.CpNativeCarryRealPrecompressionBoundaryWitness

/-!
# Reconstruction guardrails for the Genuine/native boundary crosswalk

The exact raw-boundary crosswalk is supplied by
`CpGenuineNativeRealBoundaryCrosswalk`.  This module retains only the two
logically distinct consequences from the earlier reconstruction route.

Both theorems keep their reconstruction premise explicit.  Neither derives
quadratic mass compatibility or a pre-compression witness from scalar closure
alone.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Once raw boundary closure reconstructs the native quadratic mass, every
off-critical scalar Genuine value is nonzero. -/
theorem genuineContinuation_ne_zero_off_critical_of_quadratic_mass_reconstruction
    {sigma time : ℝ}
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hoff : sigma ≠ (1 : ℝ) / 2)
    (hmass :
      NativeCarryRealPlaneBoundaryClosesAt sigma time →
        NativeCarryRealPlaneMassCompatible sigma time) :
    genuineContinuation
        (((sigma : ℂ) + (time : ℂ) * Complex.I)) ≠ 0 := by
  intro hzero
  let s : ℂ := (sigma : ℂ) + (time : ℂ) * Complex.I
  have hs : s ∈ genuineCriticalStrip := by
    constructor
    · simpa [s] using hsigma0
    · simpa [s] using hsigma1
  have hcloseAtS :
      NativeCarryRealOperatorBoundaryClosesAt 3 s.re s.im :=
    (nativeCarryRealBoundaryClosure_iff_genuineContinuation_zero hs).2 hzero
  have hcloseCamera :
      NativeCarryRealOperatorBoundaryClosesAt 3 sigma time := by
    simpa [s] using hcloseAtS
  have hclose :
      NativeCarryRealPlaneBoundaryClosesAt sigma time :=
    (nativeCarryRealOperatorBoundaryClosesAt_three sigma time).1 hcloseCamera
  exact hoff
    ((nativeCarryRealPlaneMassCompatible_iff sigma time).1
      (hmass hclose))

/-- A retained pre-compression witness supplies the quadratic-mass
reconstruction premise without a completed operator. -/
theorem genuineContinuation_ne_zero_off_critical_of_precompression_reconstruction
    {sigma time : ℝ}
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hoff : sigma ≠ (1 : ℝ) / 2)
    (hreconstruct :
      NativeCarryRealPlaneBoundaryClosesAt sigma time →
        NativeCarryRealPlaneBoundaryClosureHasPrecompressionLift sigma time) :
    genuineContinuation
        (((sigma : ℂ) + (time : ℂ) * Complex.I)) ≠ 0 := by
  apply
    genuineContinuation_ne_zero_off_critical_of_quadratic_mass_reconstruction
      hsigma0 hsigma1 hoff
  intro hclose
  exact boundaryClosurePrecompressionLift_massCompatible
    (hreconstruct hclose)

end

end CPFormal.Analytic.Cp
