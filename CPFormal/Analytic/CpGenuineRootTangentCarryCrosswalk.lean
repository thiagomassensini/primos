import CPFormal.Analytic.CpGenuineRiemannZetaIdentification
import CPFormal.Analytic.CpGenuinePrimeCarryDefectUniformBessel
import CPFormal.Analytic.CpGenuineGprePrimeVerticalTraceGate

/-!
# Root-tangent crosswalk from the Genuine camera product to the carry Green bulk

For every prime camera the analytic chart factors on the open critical strip as

`cameraProduct_p(z) = cpChartFactor p z * genuineContinuation z`.

At a simple Genuine zero, differentiating this product removes the term carrying
`deriv(cpChartFactor)` and leaves

`deriv(cameraProduct_p)(s) = cpChartFactor p s * deriv(genuineContinuation)(s)`.

Thus the ratio of camera tangent to root tangent recovers the camera factor
without defining it from the target Green coefficient.  Taking the difference
between the ratios at `s` and at the reflected zero, then applying the native
phase normalizer and the two critical carry factors, gives exactly the radial
prime Green profile.  Multiplication by the common reflected gradient energy
recovers the finite Green bulk and hence the enriched log-jet readout.

This constructs the already square-summable *mass* state from root-tangent data.
It does not assert that the native vertical trace of that state is globally in
`ell^2`; that amplitude-upgrade domain remains exactly the critical localization
gate.
-/

open scoped BigOperators Topology ENNReal

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Analytic product whose value is the bracketed chart on the strip. -/
def genuinePrimeCameraProduct (p : ℕ) (z : ℂ) : ℂ :=
  cpChartFactor p z * genuineContinuation z

/-- The camera product is the bracketed prime chart on the open strip. -/
theorem genuinePrimeCameraProduct_eq_bracketedDirichletChart
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    genuinePrimeCameraProduct p s = bracketedDirichletChart p s := by
  rw [genuinePrimeCameraProduct,
    bracketedDirichletChart_eq_cpChartFactor_mul_genuineContinuation
      p hp hpodd hs]

/-- The root derivative of the camera product contains only the common root
slope multiplied by the camera factor. -/
theorem deriv_genuinePrimeCameraProduct_eq_factor_mul_deriv_of_zero
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    deriv (genuinePrimeCameraProduct p) s =
      cpChartFactor p s * deriv genuineContinuation s := by
  have hfactor : DifferentiableAt ℂ (cpChartFactor p) s :=
    (differentiable_cpChartFactor p hp).differentiableAt
  have hgenuine : DifferentiableAt ℂ genuineContinuation s :=
    (analyticOnNhd_genuineContinuation_genuineCriticalStrip s hs).differentiableAt
  unfold genuinePrimeCameraProduct
  rw [deriv_fun_mul hfactor hgenuine, hzero]
  ring

/-- Camera tangent divided by the common root tangent. -/
def genuineRootCameraTangentRatio (p : ℕ) (s : ℂ) : ℂ :=
  deriv (genuinePrimeCameraProduct p) s /
    deriv genuineContinuation s

/-- At a simple root the tangent ratio recovers the camera factor exactly. -/
theorem genuineRootCameraTangentRatio_eq_factor
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hsimple : deriv genuineContinuation s ≠ 0) :
    genuineRootCameraTangentRatio p s = cpChartFactor p s := by
  rw [genuineRootCameraTangentRatio,
    deriv_genuinePrimeCameraProduct_eq_factor_mul_deriv_of_zero
      p hp hs hzero]
  field_simp [hsimple]

/-- Phase-normalized reflected difference of two camera factors, dressed by
both critical carry amplitudes needed to pass from camera scale to Green scale. -/
def normalizedReflectedCameraFactorGap
    (p : Nat.Primes) (s : ℂ) : ℂ :=
  (((primeCarryAmplitudeRatio p : ℝ) : ℂ) *
      cpPhaseNormalizer (p : ℕ) s / ((p : ℕ) : ℂ)) *
    (cpChartFactor (p : ℕ) s -
      cpChartFactor (p : ℕ) (reflectedParameter s))

/-- The normalized reflected camera-factor gap is exactly the real
critical-amplitude Green radial profile. -/
theorem normalizedReflectedCameraFactorGap_eq_greenRadial
    (p : Nat.Primes) (s : ℂ) :
    normalizedReflectedCameraFactorGap p s =
      ((primeCarryGreenRadialProfile
        (criticalDisplacement s.re) p : ℝ) : ℂ) := by
  have hpC : ((p : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast p.prop.ne_zero
  have hfactor :
      cpChartFactor (p : ℕ) s -
          cpChartFactor (p : ℕ) (reflectedParameter s) =
        ((p : ℕ) : ℂ) *
          (natDirichletTerm (reflectedParameter s) (p : ℕ) -
            natDirichletTerm s (p : ℕ)) := by
    unfold cpChartFactor
    rw [← prime_mul_dirichletTerm_eq_cpow_one_sub
        (p : ℕ) p.prop s,
      ← prime_mul_dirichletTerm_eq_cpow_one_sub
        (p : ℕ) p.prop (reflectedParameter s)]
    simp only [natDirichletTerm]
    ring
  have hnormal :
      cpPhaseNormalizer (p : ℕ) (reflectedParameter s) =
        cpPhaseNormalizer (p : ℕ) s := by
    simp [cpPhaseNormalizer]
  have hsRadial :=
    cpPhaseNormalizer_mul_eigenvalue (p : ℕ) p.prop s
  have hrefRadial :=
    cpPhaseNormalizer_mul_eigenvalue
      (p : ℕ) p.prop (reflectedParameter s)
  rw [hnormal, criticalDisplacement_reflectedParameter] at hrefRadial
  simp only [neg_neg] at hrefRadial
  unfold normalizedReflectedCameraFactorGap
  rw [hfactor]
  field_simp [hpC]
  calc
    (((primeCarryAmplitudeRatio p : ℝ) : ℂ) *
          cpPhaseNormalizer (p : ℕ) s *
            natDirichletTerm (reflectedParameter s) (p : ℕ) -
        ((primeCarryAmplitudeRatio p : ℝ) : ℂ) *
          cpPhaseNormalizer (p : ℕ) s *
            natDirichletTerm s (p : ℕ)) =
      ((primeCarryAmplitudeRatio p : ℝ) : ℂ) *
        (cpPhaseNormalizer (p : ℕ) s *
            natDirichletTerm (reflectedParameter s) (p : ℕ) -
          cpPhaseNormalizer (p : ℕ) s *
            natDirichletTerm s (p : ℕ)) := by ring
    _ = ((primeCarryAmplitudeRatio p : ℝ) : ℂ) *
        ((((p : ℝ) ^ (criticalDisplacement s.re) : ℝ) : ℂ) -
          (((p : ℝ) ^ (-criticalDisplacement s.re) : ℝ) : ℂ)) := by
            rw [hrefRadial, hsRadial]
    _ = ((primeCarryGreenRadialProfile
          (criticalDisplacement s.re) p : ℝ) : ℂ) := by
            unfold primeCarryGreenRadialProfile cpRadialDifference
            push_cast
            ring

/-- The same radial coefficient reconstructed only from the two simple-root
camera tangent ratios. -/
def genuineRootTangentGreenRadialProfile
    (p : Nat.Primes) (s : ℂ) : ℂ :=
  (((primeCarryAmplitudeRatio p : ℝ) : ℂ) *
      cpPhaseNormalizer (p : ℕ) s / ((p : ℕ) : ℂ)) *
    (genuineRootCameraTangentRatio (p : ℕ) s -
      genuineRootCameraTangentRatio
        (p : ℕ) (reflectedParameter s))

/-- At a reflected pair of simple Genuine zeros, root tangents reconstruct the
prime Green radial profile exactly. -/
theorem genuineRootTangentGreenRadialProfile_eq
    (p : Nat.Primes) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hsimple : deriv genuineContinuation s ≠ 0)
    (hsimpleSharp :
      deriv genuineContinuation (reflectedParameter s) ≠ 0) :
    genuineRootTangentGreenRadialProfile p s =
      ((primeCarryGreenRadialProfile
        (criticalDisplacement s.re) p : ℝ) : ℂ) := by
  have hsSharp := reflectedParameter_mem_genuineCriticalStrip_zeta hs
  have hzeroSharp :=
    genuineContinuation_reflectedParameter_eq_zero_of_zero hs hzero
  unfold genuineRootTangentGreenRadialProfile
  rw [genuineRootCameraTangentRatio_eq_factor
      (p : ℕ) p.prop hs hzero hsimple,
    genuineRootCameraTangentRatio_eq_factor
      (p : ℕ) p.prop hsSharp hzeroSharp hsimpleSharp]
  exact normalizedReflectedCameraFactorGap_eq_greenRadial p s

/-- Root-tangent reconstruction of the finite prime Green bulk. -/
def genuineRootTangentGreenBulk
    (p : Nat.Primes) (M : ℕ) (s : ℂ) : ℝ :=
  (genuineRootTangentGreenRadialProfile p s).re *
    (finiteReflectedGradientPairing M s).re

/-- At a reflected simple-root pair, the root-tangent bulk is the existing
critical-amplitude Green bulk. -/
theorem genuineRootTangentGreenBulk_eq
    (p : Nat.Primes) (M : ℕ) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hsimple : deriv genuineContinuation s ≠ 0)
    (hsimpleSharp :
      deriv genuineContinuation (reflectedParameter s) ≠ 0) :
    genuineRootTangentGreenBulk p M s =
      primeCarryGreenBulkCutoffProfile M s p := by
  rw [genuineRootTangentGreenBulk,
    genuineRootTangentGreenRadialProfile_eq
      p hs hzero hsimple hsimpleSharp]
  simp only [Complex.ofReal_re]
  exact (primeCarryGreenBulkCutoffProfile_eq M s p).symm

/-- The provenance-preserving enriched log-jet readout is therefore a literal
root-tangent bulk at every finite cutoff. -/
theorem finiteEnrichedNativeGpreLogJetGreenBulkReadout_eq_rootTangent
    (p : Nat.Primes) (M : ℕ)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hsimple : deriv genuineContinuation s ≠ 0)
    (hsimpleSharp :
      deriv genuineContinuation (reflectedParameter s) ≠ 0) :
    finiteEnrichedNativeGpreLogJetGreenBulkReadout
        p M kappa omega s =
      genuineRootTangentGreenBulk p (3 * M) s := by
  rw [finiteEnrichedNativeGpreLogJetGreenBulkReadout_eq
      p M hkappa omega homega s,
    genuineRootTangentGreenBulk_eq
      p (3 * M) hs hzero hsimple hsimpleSharp]

/-- The globally square-summable mass state is also reconstructed from the
root tangent, but its native trace remains an unbounded amplitude upgrade. -/
theorem primeMassGreenVerticalTraceFluxProfile_eq_rootTangent
    (p : Nat.Primes) (M : ℕ) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hsimple : deriv genuineContinuation s ≠ 0)
    (hsimpleSharp :
      deriv genuineContinuation (reflectedParameter s) ≠ 0) :
    primeMassGreenVerticalTraceFluxProfile M s p =
      genuineRootTangentGreenBulk p M s := by
  rw [primeMassGreenVerticalTraceFluxProfile_eq,
    genuineRootTangentGreenBulk_eq
      p M hs hzero hsimple hsimpleSharp]

/-- Scope guard for the root-tangent route: even for a reflected simple-root
pair, global square summability of the upgraded tangent profile is exactly the
half-abscissa. -/
theorem summable_genuineRootTangentGreenBulk_sq_iff
    (M : ℕ) (hM : 0 < M) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hsimple : deriv genuineContinuation s ≠ 0)
    (hsimpleSharp :
      deriv genuineContinuation (reflectedParameter s) ≠ 0) :
    Summable (fun p : Nat.Primes =>
      (genuineRootTangentGreenBulk p M s) ^ 2) ↔
        criticalDisplacement s.re = 0 := by
  have hfun :
      (fun p : Nat.Primes =>
        (genuineRootTangentGreenBulk p M s) ^ 2) =
      (fun p : Nat.Primes =>
        (primeCarryGreenBulkCutoffProfile M s p) ^ 2) := by
    funext p
    rw [genuineRootTangentGreenBulk_eq
      p M hs hzero hsimple hsimpleSharp]
  rw [hfun]
  exact summable_primeCarryGreenBulkCutoffProfile_sq_iff M hM hs

end

end CPFormal.Analytic.Cp
