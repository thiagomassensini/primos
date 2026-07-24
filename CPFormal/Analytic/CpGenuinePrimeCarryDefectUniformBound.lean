import CPFormal.Analytic.CpPrimeCarryDefectReadoutCrosswalk
import CPFormal.Analytic.CpFiniteGenuineOneSidedGreenBudget
import CPFormal.Analytic.CpGenuineGprePrimeMomentCrosswalk
import CPFormal.Analytic.CpGenuineGprePrimeVerticalTraceGate

/-!
# Global centered-carry realization and the final uniform-bound gate

For every finite prime atlas, the enriched log-jet Green readouts have already
been realized by the canonical centered-carry provenance state.  This module
proves a variational fact which is important for the last step: that state has
minimal Hilbert norm among all states producing the same active readout
coefficients.  Consequently, no alternative realization can hide an
unbounded prime ledger in unused orthogonal directions.

The final uniform estimate can therefore be supplied by constructing one
single global state, independent of the finite atlas, whose centered-carry
moments are the enriched Green readouts.  The norm of that state is then the
required uniform constant.

The module also crosswalks this global-state formulation with the previously
isolated fixed-time `G_pre` moment condition, the global vertical-trace domain,
and the one-sided angular correction closure.  At a Genuine zero all these
formulations are equivalent to critical localization.  No zero-to-state or
zero-to-bound instance is declared.
-/

open scoped BigOperators ENNReal Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-- A state realizes the enriched Green readouts on one finite prime atlas. -/
def IsCanonicalEnrichedPrimeCarryDefectReadoutRealizationOn
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes)
    (x : PrimeCarryDefectGlobalHilbert) : Prop :=
  ∀ p : Nat.Primes, p ∈ S →
    inner ℝ (primeCriticalCenteredCarryGlobalAxis p) x =
      finiteEnrichedNativeGpreLogJetGreenBulkReadout
        p M 1 (fun _ => 1) s

/-- A single global state realizes every prime-camera readout. -/
def IsCanonicalEnrichedPrimeCarryDefectReadoutRealization
    (M : ℕ) (s : ℂ)
    (x : PrimeCarryDefectGlobalHilbert) : Prop :=
  ∀ p : Nat.Primes,
    inner ℝ (primeCriticalCenteredCarryGlobalAxis p) x =
      finiteEnrichedNativeGpreLogJetGreenBulkReadout
        p M 1 (fun _ => 1) s

/-- Local Riesz lower bound: the canonical dual-axis vector has the least
possible norm among all vectors with the prescribed centered-carry moment. -/
theorem finiteEnrichedPrimeCarryDefectProvenanceState_norm_sq_le_of_inner_eq
    (p : Nat.Primes) (M : ℕ) (s : ℂ)
    (x : PrimeCarryResidueHilbert p)
    (hinner :
      inner ℝ (primeCriticalCenteredCarryAxis p) x =
        finiteEnrichedNativeGpreLogJetGreenBulkReadout
          p M 1 (fun _ => 1) s) :
    ‖finiteEnrichedPrimeCarryDefectProvenanceState
        p M 1 (fun _ => 1) s‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  let P : ℝ := (p : ℝ)
  let r : ℝ := finiteEnrichedNativeGpreLogJetGreenBulkReadout
    p M 1 (fun _ => 1) s
  have hP0 : 0 < P := by
    dsimp [P]
    exact_mod_cast p.prop.pos
  have hP1 : 0 < P - 1 := by
    dsimp [P]
    have hpone : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    linarith
  have hcs := abs_real_inner_le_norm
    (primeCriticalCenteredCarryAxis p) x
  rw [hinner] at hcs
  have hleft0 : 0 ≤ |r| := abs_nonneg _
  have hright0 :
      0 ≤ ‖primeCriticalCenteredCarryAxis p‖ * ‖x‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsq := (sq_le_sq₀ hleft0 hright0).2 hcs
  rw [sq_abs, mul_pow, primeCriticalCenteredCarryAxis_norm_sq] at hsq
  have hscaled := mul_le_mul_of_nonneg_left hsq hP0.le
  have hratio :
      P * (((P - 1) / P) * ‖x‖ ^ 2) = (P - 1) * ‖x‖ ^ 2 := by
    field_simp [ne_of_gt hP0]
  rw [hratio] at hscaled
  rw [finiteEnrichedPrimeCarryDefectProvenanceState_norm_sq]
  dsimp [P, r] at hscaled ⊢
  rw [show
    ((p : ℝ) / ((p : ℝ) - 1)) *
          (finiteEnrichedNativeGpreLogJetGreenBulkReadout
            p M 1 (fun _ => 1) s) ^ 2 =
        (((p : ℝ) *
          (finiteEnrichedNativeGpreLogJetGreenBulkReadout
            p M 1 (fun _ => 1) s) ^ 2) /
          ((p : ℝ) - 1)) by ring]
  apply (div_le_iff₀ hP1).2
  nlinarith

/-- Variational theorem on a finite atlas: the canonical provenance state has
minimal norm among all common states producing the same active coefficients. -/
theorem canonicalProvenanceState_norm_sq_le_of_realizesOn
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes)
    (x : PrimeCarryDefectGlobalHilbert)
    (hrealizes :
      IsCanonicalEnrichedPrimeCarryDefectReadoutRealizationOn M s S x) :
    ‖canonicalEnrichedPrimeCarryDefectProvenanceState M s S‖ ^ 2 ≤
      ‖x‖ ^ 2 := by
  rw [canonicalEnrichedPrimeCarryDefectProvenanceState_norm_sq]
  calc
    (∑ p ∈ S,
        ((p : ℝ) / ((p : ℝ) - 1)) *
          (finiteEnrichedNativeGpreLogJetGreenBulkReadout
            p M 1 (fun _ => 1) s) ^ 2) ≤
      ∑ p ∈ S, ‖x p‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro p hp
        have hlocal :
            inner ℝ (primeCriticalCenteredCarryAxis p) (x p) =
              finiteEnrichedNativeGpreLogJetGreenBulkReadout
                p M 1 (fun _ => 1) s := by
          have h := hrealizes p hp
          rw [inner_primeCriticalCenteredCarryGlobalAxis] at h
          exact h
        simpa [finiteEnrichedPrimeCarryDefectProvenanceState_norm_sq] using
          finiteEnrichedPrimeCarryDefectProvenanceState_norm_sq_le_of_inner_eq
            p M s (x p) hlocal
    _ ≤ ‖x‖ ^ 2 := by
      simpa using
        (lp.sum_rpow_le_norm_rpow
          (E := fun p : Nat.Primes => PrimeCarryResidueHilbert p)
          (p := (2 : ℝ≥0∞)) (by norm_num) x S)

/-- A single global realization immediately supplies the required uniform
atlas bound, with the squared norm of the realizing state as constant. -/
theorem canonicalProvenanceStatesBounded_of_global_realization
    (M : ℕ) (s : ℂ)
    {x : PrimeCarryDefectGlobalHilbert}
    (hrealizes :
      IsCanonicalEnrichedPrimeCarryDefectReadoutRealization M s x) :
    CanonicalEnrichedPrimeCarryDefectProvenanceStatesBounded M s := by
  refine ⟨‖x‖ ^ 2, ?_⟩
  intro S
  exact canonicalProvenanceState_norm_sq_le_of_realizesOn
    M s S x (fun p hp => hrealizes p)

/-- At the critical displacement every enriched Green bulk readout vanishes. -/
theorem finiteEnrichedNativeGpreLogJetGreenBulkReadout_eq_zero_of_critical
    (p : Nat.Primes) (M : ℕ) {s : ℂ}
    (hcritical : criticalDisplacement s.re = 0) :
    finiteEnrichedNativeGpreLogJetGreenBulkReadout
        p M 1 (fun _ => 1) s = 0 := by
  rw [finiteEnrichedNativeGpreLogJetGreenBulkReadout_eq
    p M (by norm_num) (fun _ => 1) (by intro m; norm_num) s,
    primeCarryGreenBulkCutoffProfile_eq]
  unfold primeCarryGreenRadialProfile
  rw [hcritical]
  simp [cpRadialDifference]

/-- On the half-abscissa the zero vector realizes all centered-carry readouts. -/
theorem zero_is_globalCarryDefectReadoutRealization_of_critical
    (M : ℕ) {s : ℂ}
    (hcritical : criticalDisplacement s.re = 0) :
    IsCanonicalEnrichedPrimeCarryDefectReadoutRealization
      M s (0 : PrimeCarryDefectGlobalHilbert) := by
  intro p
  rw [inner_zero_right,
    finiteEnrichedNativeGpreLogJetGreenBulkReadout_eq_zero_of_critical
      p M hcritical]

/-- Existence of one global centered-carry realization is exactly critical
localization at every nonempty cutoff. -/
theorem exists_globalCarryDefectReadoutRealization_iff
    (M : ℕ) (hM : 0 < M) {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    (∃ x : PrimeCarryDefectGlobalHilbert,
      IsCanonicalEnrichedPrimeCarryDefectReadoutRealization M s x) ↔
      criticalDisplacement s.re = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    have hbounded :=
      canonicalProvenanceStatesBounded_of_global_realization M s hx
    exact
      (canonicalEnrichedPrimeCarryDefectProvenanceStatesBounded_iff
        M hM hs).1 hbounded
  · intro hcritical
    exact ⟨0, zero_is_globalCarryDefectReadoutRealization_of_critical
      M hcritical⟩

/-- The centered-carry global-state formulation is the same fixed-time moment
gate already isolated in the native `G_pre` tower. -/
theorem exists_globalCarryDefectReadoutRealization_iff_fixedTimeMomentState
    (M : ℕ) (hM : 0 < M) {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    (∃ x : PrimeCarryDefectGlobalHilbert,
      IsCanonicalEnrichedPrimeCarryDefectReadoutRealization M s x) ↔
      NativeGpreReflectedGapHasFixedTimeMomentStateAt (3 * M) s := by
  rw [exists_globalCarryDefectReadoutRealization_iff M hM hs,
    nativeGpreReflectedGapHasFixedTimeMomentStateAt_iff_critical
      (3 * M) (by omega) hs]

/-- The same global-state gate is exactly membership in the global native
primewise vertical-trace domain. -/
theorem exists_globalCarryDefectReadoutRealization_iff_verticalTraceDomain
    (M : ℕ) (hM : 0 < M) {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    (∃ x : PrimeCarryDefectGlobalHilbert,
      IsCanonicalEnrichedPrimeCarryDefectReadoutRealization M s x) ↔
      PrimeMassGreenVerticalGlobalTraceDomainAt (3 * M) s := by
  rw [exists_globalCarryDefectReadoutRealization_iff M hM hs,
    primeMassGreenVerticalGlobalTraceDomainAt_iff
      (3 * M) (by omega) hs]

/-- At a Genuine zero, the global centered-carry realization and the one-sided
angular correction closure are exactly the same final obligation. -/
theorem exists_globalCarryDefectReadoutRealization_iff_scaledCorrectionCloses
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    (∃ x : PrimeCarryDefectGlobalHilbert,
      IsCanonicalEnrichedPrimeCarryDefectReadoutRealization 1 s x) ↔
      Tendsto
        (fun M : ℕ =>
          ((cpRadialDifference p (criticalDisplacement s.re) : ℝ) : ℂ) *
            finiteCanonicalAngularGreenCorrection M s)
        atTop (nhds 0) := by
  constructor
  · intro hexists
    have hcritical :=
      (exists_globalCarryDefectReadoutRealization_iff
        1 (by norm_num) hs).1 hexists
    have hradial :
        cpRadialDifference p (criticalDisplacement s.re) = 0 :=
      (cpRadialDifference_eq_zero_iff
        p hp (criticalDisplacement s.re)).2 hcritical
    simpa [hradial] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (nhds 0))
  · intro hcorrection
    have hcritical :=
      criticalDisplacement_eq_zero_of_genuine_zero_of_scaled_correction
        hp hzero hs hcorrection
    exact
      (exists_globalCarryDefectReadoutRealization_iff
        1 (by norm_num) hs).2 hcritical

/-- Global zero-to-state formulation of the final uniform-bound problem. -/
def GenuineZerosAdmitGlobalCenteredCarryReadoutState : Prop :=
  ∀ {s : ℂ}, genuineContinuation s = 0 →
    s ∈ genuineCriticalStrip →
      ∃ x : PrimeCarryDefectGlobalHilbert,
        IsCanonicalEnrichedPrimeCarryDefectReadoutRealization 1 s x

/-- Scope guard: constructing the single global state at every Genuine zero
has exactly the strength of strong off-critical nonvanishing. -/
theorem genuineZerosAdmitGlobalCenteredCarryReadoutState_iff_strongNonvanishing :
    GenuineZerosAdmitGlobalCenteredCarryReadoutState ↔
      GenuineStrongNonvanishingInStrip := by
  constructor
  · intro hstate s hs hoff hzero
    have hexists := hstate hzero hs
    have hcritical :=
      (exists_globalCarryDefectReadoutRealization_iff
        1 (by norm_num) hs).1 hexists
    apply hoff
    unfold criticalDisplacement at hcritical
    linarith
  · intro hstrong s hzero hs
    apply
      (exists_globalCarryDefectReadoutRealization_iff
        1 (by norm_num) hs).2
    by_contra hdelta
    have hoff : s.re ≠ (1 : ℝ) / 2 := by
      intro hhalf
      apply hdelta
      unfold criticalDisplacement
      rw [hhalf]
      ring
    exact (hstrong hs hoff) hzero

end

end CPFormal.Analytic.Cp
