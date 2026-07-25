import CPFormal.Analytic.CpGenuineGreenKernelInclusion
import CPFormal.Analytic.CpRealSpectralGenerator

/-!
# Native carry spectrum and complex-time exhaustion

The carry geometry fixes the critical amplitude before any complex extension is
introduced.  The remaining real parameter `t` is the unitary phase time and the
native readout is

`realSpectralGenuine t = genuineContinuation (1 / 2 + t * I)`.

This module rewrites an arbitrary complex parameter as the same critical state
observed at a **complex time**.  If

`z = t - I * (re(s) - 1/2)`,

then

`1/2 + z * I = s`.

Consequently, localization of all Genuine zeros on the half-abscissa is exactly
the statement that the complex-time continuation of the native carry readout
has no resonances away from real time.

The completed Genuine--Green operator already satisfies this zero rigidity
without any extra premise.  For the scalar Genuine channel, the corresponding
exhaustion statement is proved equivalent to the existing strong
nonvanishing target.  No Riemann-zeta identification is used here.
-/

open scoped Topology

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Complex time for the carry orbit.  Real `z = t` gives the native unitary
orbit; a nonzero imaginary part changes the radial amplitude. -/
def carryComplexTimeParameter (z : ℂ) : ℂ :=
  ((1 / 2 : ℝ) : ℂ) + z * Complex.I

@[simp] theorem carryComplexTimeParameter_re (z : ℂ) :
    (carryComplexTimeParameter z).re = (1 : ℝ) / 2 - z.im := by
  simp [carryComplexTimeParameter]

@[simp] theorem carryComplexTimeParameter_im (z : ℂ) :
    (carryComplexTimeParameter z).im = z.re := by
  simp [carryComplexTimeParameter]

/-- On real time, the complex-time parameter is literally the already defined
critical-line parameter. -/
@[simp] theorem carryComplexTimeParameter_ofReal (t : ℝ) :
    carryComplexTimeParameter (t : ℂ) = criticalLineParameter t := by
  simp [carryComplexTimeParameter, criticalLineParameter]

/-- Every complex parameter is the critical carry amplitude observed at one
complex time. -/
def carryComplexTimeOfParameter (s : ℂ) : ℂ :=
  (s.im : ℂ) - (criticalDisplacement s.re : ℂ) * Complex.I

@[simp] theorem carryComplexTimeOfParameter_re (s : ℂ) :
    (carryComplexTimeOfParameter s).re = s.im := by
  simp [carryComplexTimeOfParameter]

@[simp] theorem carryComplexTimeOfParameter_im (s : ℂ) :
    (carryComplexTimeOfParameter s).im = -criticalDisplacement s.re := by
  simp [carryComplexTimeOfParameter]

/-- Passing from a parameter to complex time and back changes only notation. -/
@[simp] theorem carryComplexTimeParameter_ofParameter (s : ℂ) :
    carryComplexTimeParameter (carryComplexTimeOfParameter s) = s := by
  apply Complex.ext <;>
    simp [carryComplexTimeParameter, carryComplexTimeOfParameter,
      criticalDisplacement] <;> ring

/-- The two coordinate changes are inverse in the other direction as well. -/
@[simp] theorem carryComplexTimeOfParameter_ofTime (z : ℂ) :
    carryComplexTimeOfParameter (carryComplexTimeParameter z) = z := by
  apply Complex.ext <;>
    simp [carryComplexTimeParameter, carryComplexTimeOfParameter,
      criticalDisplacement] <;> ring

/-- Transverse displacement is exactly minus the imaginary part of complex
carry time. -/
@[simp] theorem criticalDisplacement_carryComplexTimeParameter_re (z : ℂ) :
    criticalDisplacement (carryComplexTimeParameter z).re = -z.im := by
  simp [criticalDisplacement]

/-- The scalar Genuine readout written in the intrinsic complex-time
coordinate of the carry orbit. -/
def carryComplexTimeGenuine (z : ℂ) : ℂ :=
  genuineContinuation (carryComplexTimeParameter z)

@[simp] theorem carryComplexTimeGenuine_ofReal (t : ℝ) :
    carryComplexTimeGenuine (t : ℂ) = realSpectralGenuine t := by
  simp [carryComplexTimeGenuine, realSpectralGenuine]

/-- A resonance of the holomorphic complex-time continuation of the native
carry readout. -/
def IsNativeCarryComplexTimeResonance (z : ℂ) : Prop :=
  carryComplexTimeGenuine z = 0

@[simp] theorem isNativeCarryComplexTimeResonance_ofReal_iff (t : ℝ) :
    IsNativeCarryComplexTimeResonance (t : ℂ) ↔
      IsRealSpectralResonance t := by
  simp [IsNativeCarryComplexTimeResonance, IsRealSpectralResonance]

/-- Native spectral exhaustion: every zero of the continued Genuine readout is
already one of the real-time resonances produced after the carry amplitude has
been fixed. -/
def NativeCarrySpectrumExhaustsGenuine : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    genuineContinuation s = 0 →
      ∃ t : ℝ, s = criticalLineParameter t ∧ IsRealSpectralResonance t

/-- The same target in its shortest intrinsic form: complex carry time can
resonate only when it is real. -/
def NativeCarryComplexTimeZeroRigidity : Prop :=
  ∀ {z : ℂ}, carryComplexTimeParameter z ∈ genuineCriticalStrip →
    IsNativeCarryComplexTimeResonance z → z.im = 0

/-- Exhaustion of the continued zero set is exactly the strong scalar
nonvanishing statement, expressed without any external function. -/
theorem nativeCarrySpectrumExhaustsGenuine_iff_strongNonvanishing :
    NativeCarrySpectrumExhaustsGenuine ↔ GenuineStrongNonvanishingInStrip := by
  constructor
  · intro hexhaust s hs hoff hzero
    rcases hexhaust hs hzero with ⟨t, hst, _hres⟩
    apply hoff
    calc
      s.re = (criticalLineParameter t).re := congrArg Complex.re hst
      _ = (1 : ℝ) / 2 := criticalLineParameter_re t
  · intro hstrong s hs hzero
    have hre : s.re = (1 : ℝ) / 2 := by
      by_contra hoff
      exact (hstrong hs hoff) hzero
    let t : ℝ := s.im
    have hst : s = criticalLineParameter t := by
      apply Complex.ext <;> simp [criticalLineParameter, t, hre]
    refine ⟨t, hst, ?_⟩
    unfold IsRealSpectralResonance realSpectralGenuine
    rw [← hst]
    exact hzero

/-- In complex-time coordinates, absence of new nonreal resonances is again
exactly the strong scalar target. -/
theorem nativeCarryComplexTimeZeroRigidity_iff_strongNonvanishing :
    NativeCarryComplexTimeZeroRigidity ↔ GenuineStrongNonvanishingInStrip := by
  constructor
  · intro hrigid s hs hoff hzero
    let z : ℂ := carryComplexTimeOfParameter s
    have hzmem : carryComplexTimeParameter z ∈ genuineCriticalStrip := by
      simpa [z] using hs
    have hzres : IsNativeCarryComplexTimeResonance z := by
      unfold IsNativeCarryComplexTimeResonance carryComplexTimeGenuine
      simpa [z] using hzero
    have him : z.im = 0 := hrigid hzmem hzres
    have hdelta : criticalDisplacement s.re = 0 := by
      have hneg : -criticalDisplacement s.re = 0 := by
        simpa [z] using him
      linarith
    apply hoff
    unfold criticalDisplacement at hdelta
    linarith
  · intro hstrong z hz hres
    by_contra him
    have hoff : (carryComplexTimeParameter z).re ≠ (1 : ℝ) / 2 := by
      intro hre
      apply him
      have hformula := carryComplexTimeParameter_re z
      linarith
    change carryComplexTimeGenuine z = 0 at hres
    exact (hstrong hz hoff) hres

/-- The two native formulations are literally the same theorem. -/
theorem nativeCarrySpectrumExhaustsGenuine_iff_complexTimeZeroRigidity :
    NativeCarrySpectrumExhaustsGenuine ↔
      NativeCarryComplexTimeZeroRigidity := by
  rw [nativeCarrySpectrumExhaustsGenuine_iff_strongNonvanishing,
    nativeCarryComplexTimeZeroRigidity_iff_strongNonvanishing]

/-- The completed carry operator already has no nonreal complex-time zeros.
Its zero is exactly a native real-time Genuine resonance. -/
theorem genuineGreenCompletedCarryComplexTime_zero_iff
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    {z : ℂ} (hz : carryComplexTimeParameter z ∈ genuineCriticalStrip) :
    genuineGreenCompletedLimitOperator p q (carryComplexTimeParameter z) = 0 ↔
      z.im = 0 ∧ IsRealSpectralResonance z.re := by
  rw [genuineGreenCompletedLimitOperator_eq_zero_iff p q hp hq hz]
  constructor
  · rintro ⟨hzero, hdelta⟩
    have him : z.im = 0 := by
      rw [criticalDisplacement_carryComplexTimeParameter_re] at hdelta
      linarith
    refine ⟨him, ?_⟩
    have hparam :
        carryComplexTimeParameter z = criticalLineParameter z.re := by
      apply Complex.ext <;>
        simp [carryComplexTimeParameter, criticalLineParameter, him]
    unfold IsRealSpectralResonance realSpectralGenuine
    rw [← hparam]
    exact hzero
  · rintro ⟨him, hres⟩
    have hparam :
        carryComplexTimeParameter z = criticalLineParameter z.re := by
      apply Complex.ext <;>
        simp [carryComplexTimeParameter, criticalLineParameter, him]
    constructor
    · unfold IsRealSpectralResonance realSpectralGenuine at hres
      rw [hparam]
      exact hres
    · rw [criticalDisplacement_carryComplexTimeParameter_re, him]
      simp

/-- Direct root-level consequence already certified for the completed native
operator: a nonreal complex time cannot be a zero. -/
theorem genuineGreenCompletedCarryComplexTime_ne_zero_of_im_ne_zero
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    {z : ℂ} (hz : carryComplexTimeParameter z ∈ genuineCriticalStrip)
    (him : z.im ≠ 0) :
    genuineGreenCompletedLimitOperator p q (carryComplexTimeParameter z) ≠ 0 := by
  intro hzero
  exact him
    ((genuineGreenCompletedCarryComplexTime_zero_iff p q hp hq hz).1 hzero).1

end

end CPFormal.Analytic.Cp
