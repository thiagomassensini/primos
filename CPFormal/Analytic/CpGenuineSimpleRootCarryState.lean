import CPFormal.Analytic.CpGenuineRootTangentCarryAtlas
import CPFormal.Analytic.CpGenuinePrimeCarryDefectUniformBound
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Multiplicity-one Genuine roots and the global mass state

This module closes the parts of the root-tangent route which use only a
multiplicity-one Genuine zero.

* simplicity is transported automatically to the reflected zero;
* the reflected tangent hypothesis is removed from all finite-atlas
  crosswalks;
* one global square-summable **mass** state is constructed directly from the
  root tangents;
* its native primewise vertical trace is exactly the critical-amplitude Green
  readout.

The last distinction remains explicit.  The mass state belongs to the global
Hilbert space throughout the open strip, while simultaneous square summability
of its trace outputs is equivalent to critical localization.  Thus no
zero-to-trace-domain or zero-to-centered-carry-state instance is declared.
Zeros of higher multiplicity are not treated in this module.
-/

open scoped BigOperators ENNReal Topology ComplexConjugate

namespace CPFormal.Analytic.Cp

open Filter Set Complex

noncomputable section

/-- A Genuine zero of multiplicity one in the open critical strip. -/
def IsSimpleGenuineZeroInStrip (s : ℂ) : Prop :=
  s ∈ genuineCriticalStrip ∧
    genuineContinuation s = 0 ∧
      deriv genuineContinuation s ≠ 0

/-- The open critical strip is an open subset of the complex plane. -/
theorem isOpen_genuineCriticalStrip : IsOpen genuineCriticalStrip := by
  change IsOpen ({s : ℂ | 0 < s.re} ∩ {s : ℂ | s.re < 1})
  exact
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)

/-- Conjugation preserves the open critical strip. -/
theorem conj_mem_genuineCriticalStrip
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    (starRingEnd ℂ) s ∈ genuineCriticalStrip := by
  simpa [genuineCriticalStrip] using hs

/-- On the strip, the derivative of the canonical Genuine continuation is the
ordinary derivative of Mathlib's Riemann zeta function. -/
theorem deriv_genuineContinuation_eq_deriv_riemannZeta
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    deriv genuineContinuation s = deriv riemannZeta s := by
  apply EventuallyEq.deriv_eq
  filter_upwards [isOpen_genuineCriticalStrip.mem_nhds hs] with z hz
  exact genuineContinuation_eq_riemannZeta hz

/-- Conjugation transports the derivative of Riemann zeta. -/
theorem deriv_riemannZeta_conj (s : ℂ) :
    deriv riemannZeta ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (deriv riemannZeta s) := by
  have hfun :
      (starRingEnd ℂ) ∘ riemannZeta ∘ (starRingEnd ℂ) =
        riemannZeta := by
    funext z
    simp [Function.comp_def, riemannZeta_conj]
  have hder := congrArg deriv hfun
  rw [deriv_conj_conj] at hder
  have hpoint := congrFun hder ((starRingEnd ℂ) s)
  simpa only [Function.comp_apply, star_star] using hpoint.symm

/-- On the open strip the completed zeta function is the product of the
Deligne real Gamma factor and Riemann zeta. -/
theorem completedRiemannZeta_eq_GammaR_mul_riemannZeta
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre
    linarith [hs.1]
  have hgamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs.1
  rw [riemannZeta_def_of_ne_zero hs0]
  field_simp [hgamma]

/-- The Deligne real Gamma factor is differentiable at every point of positive
real part. -/
theorem differentiableAt_GammaR_of_re_pos
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Gammaℝ s := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  letI : NeZero (Real.pi : ℂ) := ⟨hpi⟩
  have hpow : DifferentiableAt ℂ
      (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s :=
    ((differentiable_const_cpow_of_neZero (Real.pi : ℂ)).comp
      (differentiable_id.neg.div_const 2)).differentiableAt
  have hgammaArg : ∀ n : ℕ, s / 2 ≠ -(n : ℂ) := by
    intro n hneg
    have hre := congrArg Complex.re hneg
    norm_num at hre
    linarith
  have hgamma : DifferentiableAt ℂ (fun z : ℂ => Gamma (z / 2)) s :=
    (differentiableAt_Gamma (s / 2) hgammaArg).comp s
      (differentiableAt_id.div_const 2)
  change DifferentiableAt ℂ
    (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Gamma (z / 2)) s
  exact hpow.mul hgamma

/-- At a zeta zero in the strip, the derivative of the completed zeta function
is the nonzero Gamma factor times the zeta derivative. -/
theorem deriv_completedRiemannZeta_eq_GammaR_mul_deriv_of_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : riemannZeta s = 0) :
    deriv completedRiemannZeta s =
      Gammaℝ s * deriv riemannZeta s := by
  have hs1 : s ≠ 1 := by
    intro hone
    have hre := congrArg Complex.re hone
    norm_num at hre
    linarith [hs.2]
  have hevent :
      completedRiemannZeta =ᶠ[𝓝 s]
        (fun z : ℂ => Gammaℝ z * riemannZeta z) := by
    filter_upwards [isOpen_genuineCriticalStrip.mem_nhds hs] with z hz
    exact completedRiemannZeta_eq_GammaR_mul_riemannZeta hz
  rw [EventuallyEq.deriv_eq hevent]
  rw [deriv_fun_mul
    (differentiableAt_GammaR_of_re_pos hs.1)
    (differentiableAt_riemannZeta hs1), hzero]
  ring

/-- Differentiating the symmetric completed functional equation transports a
nonzero tangent from `s` to `1-s`. -/
theorem deriv_completedRiemannZeta_one_sub (s : ℂ) :
    deriv completedRiemannZeta (1 - s) =
      -deriv completedRiemannZeta s := by
  have hfun :
      (fun z : ℂ => completedRiemannZeta (1 - z)) =
        completedRiemannZeta := by
    funext z
    exact completedRiemannZeta_one_sub z
  have hder := congrArg deriv hfun
  have hpoint := congrFun hder s
  have hneg :
      -deriv completedRiemannZeta (1 - s) =
        deriv completedRiemannZeta s := by
    simpa [deriv_comp_const_sub] using hpoint
  exact (neg_eq_iff_eq_neg).1 hneg

/-- A simple Genuine zero has a simple reflected zero.  Hence the second
simplicity hypothesis used by the first root-tangent crosswalk is redundant. -/
theorem deriv_genuineContinuation_reflectedParameter_ne_zero_of_simple_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hsimple : deriv genuineContinuation s ≠ 0) :
    deriv genuineContinuation (reflectedParameter s) ≠ 0 := by
  have hzeta : riemannZeta s = 0 := by
    rw [← genuineContinuation_eq_riemannZeta hs]
    exact hzero
  have hdzeta : deriv riemannZeta s ≠ 0 := by
    rw [← deriv_genuineContinuation_eq_deriv_riemannZeta hs]
    exact hsimple
  have hsConj : (starRingEnd ℂ) s ∈ genuineCriticalStrip :=
    conj_mem_genuineCriticalStrip hs
  have hzetaConj : riemannZeta ((starRingEnd ℂ) s) = 0 := by
    rw [riemannZeta_conj, hzeta, map_zero]
  have hdzetaConj : deriv riemannZeta ((starRingEnd ℂ) s) ≠ 0 := by
    rw [deriv_riemannZeta_conj]
    simpa using hdzeta
  have hcompletedConj :
      deriv completedRiemannZeta ((starRingEnd ℂ) s) ≠ 0 := by
    rw [deriv_completedRiemannZeta_eq_GammaR_mul_deriv_of_zero
      hsConj hzetaConj]
    exact mul_ne_zero (Gammaℝ_ne_zero_of_re_pos hsConj.1) hdzetaConj
  have hcompletedReflected :
      deriv completedRiemannZeta (reflectedParameter s) ≠ 0 := by
    unfold reflectedParameter
    rw [deriv_completedRiemannZeta_one_sub]
    exact neg_ne_zero.mpr hcompletedConj
  have hsReflected := reflectedParameter_mem_genuineCriticalStrip_zeta hs
  have hzeroReflected :=
    genuineContinuation_reflectedParameter_eq_zero_of_zero hs hzero
  have hzetaReflected : riemannZeta (reflectedParameter s) = 0 := by
    rw [← genuineContinuation_eq_riemannZeta hsReflected]
    exact hzeroReflected
  have hcompletedEq :=
    deriv_completedRiemannZeta_eq_GammaR_mul_deriv_of_zero
      hsReflected hzetaReflected
  have hdzetaReflected :
      deriv riemannZeta (reflectedParameter s) ≠ 0 := by
    intro hzeroDeriv
    apply hcompletedReflected
    rw [hcompletedEq, hzeroDeriv, mul_zero]
  rw [deriv_genuineContinuation_eq_deriv_riemannZeta hsReflected]
  exact hdzetaReflected

/-- Reflection preserves multiplicity-one Genuine zero data. -/
theorem isSimpleGenuineZeroInStrip_reflected
    {s : ℂ} (hroot : IsSimpleGenuineZeroInStrip s) :
    IsSimpleGenuineZeroInStrip (reflectedParameter s) := by
  rcases hroot with ⟨hs, hzero, hsimple⟩
  exact ⟨
    reflectedParameter_mem_genuineCriticalStrip_zeta hs,
    genuineContinuation_reflectedParameter_eq_zero_of_zero hs hzero,
    deriv_genuineContinuation_reflectedParameter_ne_zero_of_simple_zero
      hs hzero hsimple⟩

/-- For a multiplicity-one zero, one root tangent already suffices to recover
the prime Green bulk; reflected simplicity is derived internally. -/
theorem genuineRootTangentGreenBulk_eq_of_simple_zero
    (p : Nat.Primes) (M : ℕ) {s : ℂ}
    (hroot : IsSimpleGenuineZeroInStrip s) :
    genuineRootTangentGreenBulk p M s =
      primeCarryGreenBulkCutoffProfile M s p := by
  rcases hroot with ⟨hs, hzero, hsimple⟩
  exact genuineRootTangentGreenBulk_eq
    p M hs hzero hsimple
      (deriv_genuineContinuation_reflectedParameter_ne_zero_of_simple_zero
        hs hzero hsimple)

/-- Every finite multiplicity-one root-tangent atlas is the canonical
centered-carry provenance atlas, with no separate reflected-root premise. -/
theorem genuineRootTangentPrimeCarryDefectAtlasState_eq_canonical_of_simple_zero
    (M : ℕ) (S : Finset Nat.Primes) {s : ℂ}
    (hroot : IsSimpleGenuineZeroInStrip s) :
    genuineRootTangentPrimeCarryDefectAtlasState M s S =
      canonicalEnrichedPrimeCarryDefectProvenanceState M s S := by
  rcases hroot with ⟨hs, hzero, hsimple⟩
  exact genuineRootTangentPrimeCarryDefectAtlasState_eq_canonical
    M S hs hzero hsimple
      (deriv_genuineContinuation_reflectedParameter_ne_zero_of_simple_zero
        hs hzero hsimple)

/-- Local mass fiber reconstructed from the multiplicity-one root tangent. -/
def genuineRootTangentMassVerticalFiberState
    (p : Nat.Primes) (M : ℕ) (s : ℂ) : CarryVerticalL2 :=
  lp.single 2 1
    ((primeCarryAmplitudeRatio p * genuineRootTangentGreenBulk p M s : ℝ) : ℂ)

/-- At a simple root the root-tangent mass fiber is the previously certified
mass Green fiber. -/
theorem genuineRootTangentMassVerticalFiberState_eq_massFiber
    (p : Nat.Primes) (M : ℕ) {s : ℂ}
    (hroot : IsSimpleGenuineZeroInStrip s) :
    genuineRootTangentMassVerticalFiberState p M s =
      primeMassGreenVerticalFiberState M s p := by
  unfold genuineRootTangentMassVerticalFiberState
    primeMassGreenVerticalFiberState
  congr 2
  rw [genuineRootTangentGreenBulk_eq_of_simple_zero p M hroot]
  exact (primeMassGreenBulkCutoffProfile_eq_amplitude_mul M s p).symm

/-- The globally square-summable mass state associated with a simple Genuine
root.  Its coordinate formula below shows that it is reconstructed by the root
tangents, although the existing mass-state constructor supplies the Hilbert
membership proof. -/
def genuineSimpleRootMassVerticalGlobalState
    (M : ℕ) (s : ℂ) (hroot : IsSimpleGenuineZeroInStrip s) :
    PrimeCarryVerticalHilbert :=
  primeMassGreenVerticalGlobalState M s hroot.1

/-- Prime coordinates of the global mass state are the root-tangent mass
fibers. -/
theorem genuineSimpleRootMassVerticalGlobalState_apply
    (M : ℕ) (s : ℂ) (hroot : IsSimpleGenuineZeroInStrip s)
    (p : Nat.Primes) :
    genuineSimpleRootMassVerticalGlobalState M s hroot p =
      genuineRootTangentMassVerticalFiberState p M s := by
  rw [genuineSimpleRootMassVerticalGlobalState,
    primeMassGreenVerticalGlobalState_apply,
    genuineRootTangentMassVerticalFiberState_eq_massFiber p M hroot]

/-- The native vertical trace of the global root-derived mass state recovers
exactly the root-tangent Green bulk in every prime camera. -/
theorem primeCarryWeightedVerticalTrace_simpleRootMassState
    (M : ℕ) (s : ℂ) (hroot : IsSimpleGenuineZeroInStrip s)
    (p : Nat.Primes) :
    primeCarryWeightedVerticalTrace (p : ℕ)
        (genuineSimpleRootMassVerticalGlobalState M s hroot p) =
      (0, (genuineRootTangentGreenBulk p M s : ℂ)) := by
  rw [genuineSimpleRootMassVerticalGlobalState_apply,
    genuineRootTangentMassVerticalFiberState_eq_massFiber p M hroot,
    primeCarryWeightedVerticalTrace_massFiber,
    genuineRootTangentGreenBulk_eq_of_simple_zero p M hroot]

/-- Global trace-domain condition for the root-derived multiplicity-one mass
state. -/
def SimpleRootMassVerticalGlobalTraceDomainAt
    (M : ℕ) (s : ℂ) (hroot : IsSimpleGenuineZeroInStrip s) : Prop :=
  Summable (fun p : Nat.Primes =>
    ((primeCarryWeightedVerticalTrace (p : ℕ)
      (genuineSimpleRootMassVerticalGlobalState M s hroot p)).2.re) ^ 2)

/-- Exact endpoint of the multiplicity-one construction: the root-derived mass
state always exists globally, but its simultaneous trace belongs to `ell^2`
exactly on the half-abscissa. -/
theorem simpleRootMassVerticalGlobalTraceDomainAt_iff
    (M : ℕ) (hM : 0 < M) {s : ℂ}
    (hroot : IsSimpleGenuineZeroInStrip s) :
    SimpleRootMassVerticalGlobalTraceDomainAt M s hroot ↔
      criticalDisplacement s.re = 0 := by
  unfold SimpleRootMassVerticalGlobalTraceDomainAt
  have hfun :
      (fun p : Nat.Primes =>
        ((primeCarryWeightedVerticalTrace (p : ℕ)
          (genuineSimpleRootMassVerticalGlobalState M s hroot p)).2.re) ^ 2) =
      (fun p : Nat.Primes =>
        (primeCarryGreenBulkCutoffProfile M s p) ^ 2) := by
    funext p
    rw [primeCarryWeightedVerticalTrace_simpleRootMassState,
      genuineRootTangentGreenBulk_eq_of_simple_zero p M hroot]
    simp
  rw [hfun]
  exact summable_primeCarryGreenBulkCutoffProfile_sq_iff
    M hM hroot.1

/-- The multiplicity-one strong statement, separated from possible higher
multiplicity zeros. -/
def GenuineSimpleZerosAreCritical : Prop :=
  ∀ {s : ℂ}, IsSimpleGenuineZeroInStrip s →
    criticalDisplacement s.re = 0

/-- Global centered-carry-state formulation restricted to multiplicity-one
zeros. -/
def GenuineSimpleZerosAdmitGlobalCenteredCarryReadoutState : Prop :=
  ∀ {s : ℂ}, IsSimpleGenuineZeroInStrip s →
    ∃ x : PrimeCarryDefectGlobalHilbert,
      IsCanonicalEnrichedPrimeCarryDefectReadoutRealization 1 s x

/-- For multiplicity-one zeros, the global state construction and critical
localization are exactly equivalent.  This scope guard leaves the final
uniform completion premise visible rather than declaring it from simplicity. -/
theorem genuineSimpleZerosAdmitGlobalCenteredCarryReadoutState_iff_critical :
    GenuineSimpleZerosAdmitGlobalCenteredCarryReadoutState ↔
      GenuineSimpleZerosAreCritical := by
  constructor
  · intro hstate s hroot
    exact
      (exists_globalCarryDefectReadoutRealization_iff
        1 (by norm_num) hroot.1).1 (hstate hroot)
  · intro hcritical s hroot
    exact
      (exists_globalCarryDefectReadoutRealization_iff
        1 (by norm_num) hroot.1).2 (hcritical hroot)

end

end CPFormal.Analytic.Cp
