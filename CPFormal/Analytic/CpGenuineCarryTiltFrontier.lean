import CPFormal.Analytic.CpReflectedGreenBridge
import CPFormal.Analytic.CpTiltRigidity
import CPFormal.Analytic.CpGenuineGreenKernelInclusion

/-!
# Carry-first formulation of the Genuine confinement frontier

The half-abscissa is selected before any Hilbert-space realization: for every
odd prime camera and every admissible center, convexity/concavity of the carry
profile proves that the bracket tilt vanishes exactly at `sigma = 1/2`.

This module records the remaining logical arrow without changing that causal
order.  It also proves that both proposed zero-side formulations -- vanishing
of the carry tilt and vanishing of the reflected Green flux -- have exactly the
strength of strong Genuine nonvanishing off the half-abscissa.

No axiom, `sorry`, `admit`, or choice of a state from the target conclusion is
used.
-/

namespace CPFormal.Analytic.Cp

open CPFormal.Genuine.Cp

noncomputable section

/-- Every Genuine zero annihilates the carry tilt for one fixed camera and
center.  The tilt is the primitive object; no Hilbert state occurs here. -/
def GenuineZerosAnnihilateCarryTilt (p : ℕ) (center : ℝ) : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    genuineContinuation s = 0 →
      cpTiltAtSigma p s.re center = 0

/-- Pointwise, at every nonempty cutoff in the strip, vanishing of the pure
reflected Green bulk is exactly vanishing of the carry tilt.  No Genuine-zero
hypothesis is needed: both observables have the same unique radial zero. -/
theorem finitePhaseNormalizedCpGreenFlux_eq_zero_iff_carryTilt_eq_zero
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (center : ℝ) (hcenter : (halfRange p : ℝ) < center)
    (hM : 0 < M) {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    finitePhaseNormalizedCpGreenFlux p M s = 0 ↔
      cpTiltAtSigma p s.re center = 0 := by
  constructor
  · intro hflux
    have hhalf : s.re = (1 : ℝ) / 2 :=
      re_eq_half_of_flux_zero_of_pairing_ne p hp hflux
        (finiteReflectedGradientPairing_ne_zero hM hs)
    exact
      (cpTiltAtSigma_eq_zero_iff_half p hp hpodd hs.1 hcenter).2
        hhalf
  · intro htilt
    have hhalf : s.re = (1 : ℝ) / 2 :=
      (cpTiltAtSigma_eq_zero_iff_half p hp hpodd hs.1 hcenter).1
        htilt
    rw [finitePhaseNormalizedCpGreenFlux_eq_radialDifference_mul_pairing
      p M hp s]
    simp [criticalDisplacement, hhalf]

/-- Because the carry tilt has its unique zero at `1/2`, transferring every
Genuine zero to a zero of that tilt is exactly the desired strong
nonvanishing statement. -/
theorem genuineZerosAnnihilateCarryTilt_iff_strongNonvanishing
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (center : ℝ) (hcenter : (halfRange p : ℝ) < center) :
    GenuineZerosAnnihilateCarryTilt p center ↔
      GenuineStrongNonvanishingInStrip := by
  constructor
  · intro htilt s hs hoff hzero
    have hzeroTilt := htilt hs hzero
    have hhalf :=
      (cpTiltAtSigma_eq_zero_iff_half p hp hpodd hs.1 hcenter).1
        hzeroTilt
    exact hoff hhalf
  · intro hstrong s hs hzero
    apply
      (cpTiltAtSigma_eq_zero_iff_half p hp hpodd hs.1 hcenter).2
    by_contra hoff
    exact (hstrong hs hoff) hzero

/-- Canonical camera-three instance of the carry-first frontier. -/
theorem genuineZerosAnnihilateCarryTilt_three_two_iff_strongNonvanishing :
    GenuineZerosAnnihilateCarryTilt 3 2 ↔
      GenuineStrongNonvanishingInStrip := by
  exact genuineZerosAnnihilateCarryTilt_iff_strongNonvanishing
    3 (by norm_num) (by norm_num) 2 (by norm_num [halfRange])

/-- For every nonempty reflected cutoff, requiring the Green flux to vanish
at every Genuine zero is likewise equivalent to strong nonvanishing.  The
forward implication uses positive reflected energy and radial rigidity; the
reverse implication substitutes the already-forced half-abscissa into the
exact finite factorization. -/
theorem greenFluxVanishesAtGenuineZeros_iff_strongNonvanishing
    (p M : ℕ) (hp : Nat.Prime p) (hM : 0 < M) :
    GreenFluxVanishesAtGenuineZeros p M ↔
      GenuineStrongNonvanishingInStrip := by
  constructor
  · intro hflux s hs hoff hzero
    exact hoff
      (re_eq_half_of_greenFluxVanishes p M hp hM hflux hzero hs)
  · intro hstrong s hzero hs
    have hhalf : s.re = (1 : ℝ) / 2 := by
      by_contra hoff
      exact (hstrong hs hoff) hzero
    rw [finitePhaseNormalizedCpGreenFlux_eq_radialDifference_mul_pairing
      p M hp s]
    simp [criticalDisplacement, hhalf]

/-- The reflected-flux and carry-tilt formulations are the same remaining
frontier, although their finite observables are different objects. -/
theorem greenFluxVanishesAtGenuineZeros_iff_carryTilt
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (center : ℝ) (hcenter : (halfRange p : ℝ) < center)
    (hM : 0 < M) :
    GreenFluxVanishesAtGenuineZeros p M ↔
      GenuineZerosAnnihilateCarryTilt p center := by
  rw [greenFluxVanishesAtGenuineZeros_iff_strongNonvanishing p M hp hM,
    genuineZerosAnnihilateCarryTilt_iff_strongNonvanishing
      p hp hpodd center hcenter]

end


end CPFormal.Analytic.Cp
