import CPFormal.Analytic.CpGenuineGprePrimeAmplitudeGraph
import CPFormal.Analytic.CpCarryWeightedVerticalBracketTrace

/-!
# Primewise vertical TFVD trace and the last graph-domain gate

The prime-amplitude upgrade is not an artificial multiplier.  On a vertical
fiber whose only active coordinate is the first positive carry level, the
native trace

`Tr_q(x) = (x_0, q^(-1) x_1 - x_0)`

performs exactly the upgrade from complete mass `p^(-1)` to critical amplitude
`p^(-1/2)`.  This module realizes the mass Green profile as a global
prime-indexed family of vertical fibers and proves that its primewise trace
flux is exactly the critical Green bulk.

The mass family belongs to the global Hilbert space everywhere in the open
strip.  Membership in the domain of the global trace-flux family is equivalent
to the half-abscissa.  No zero-to-domain implication is declared.
-/

open scoped BigOperators ENNReal

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Hilbert direct sum of the vertical carry fibers of all prime cameras. -/
abbrev PrimeCarryVerticalHilbert :=
  lp (fun _ : Nat.Primes => CarryVerticalL2) 2

/-- The mass Green value placed at the first positive level of one prime
vertical fiber. -/
def primeMassGreenVerticalFiberState
    (M : ℕ) (s : ℂ) (p : Nat.Primes) : CarryVerticalL2 :=
  lp.single 2 1
    (primeMassGreenBulkCutoffProfile M s p : ℂ)

@[simp] theorem primeMassGreenVerticalFiberState_zero
    (M : ℕ) (s : ℂ) (p : Nat.Primes) :
    primeMassGreenVerticalFiberState M s p 0 = 0 := by
  simp [primeMassGreenVerticalFiberState, lp.single_apply]

@[simp] theorem primeMassGreenVerticalFiberState_one
    (M : ℕ) (s : ℂ) (p : Nat.Primes) :
    primeMassGreenVerticalFiberState M s p 1 =
      (primeMassGreenBulkCutoffProfile M s p : ℂ) := by
  simp [primeMassGreenVerticalFiberState, lp.single_apply]

/-- Exact fiber norm: no loss occurs when the mass readout is inserted at the
first positive level. -/
theorem primeMassGreenVerticalFiberState_norm_sq
    (M : ℕ) (s : ℂ) (p : Nat.Primes) :
    ‖primeMassGreenVerticalFiberState M s p‖ ^ 2 =
      (primeMassGreenBulkCutoffProfile M s p) ^ 2 := by
  unfold primeMassGreenVerticalFiberState
  rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  simp [Real.norm_eq_abs, sq_abs]

/-- The global mass Green family is a legitimate Hilbert state throughout the
whole open critical strip. -/
def primeMassGreenVerticalGlobalState
    (M : ℕ) (s : ℂ) (hs : s ∈ genuineCriticalStrip) :
    PrimeCarryVerticalHilbert :=
  let f : PreLp (fun _ : Nat.Primes => CarryVerticalL2) :=
    fun p => primeMassGreenVerticalFiberState M s p
  ⟨f, by
    change Memℓp f 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    have hsum := summable_primeMassGreenBulkCutoffProfile_sq M hs
    exact hsum.congr fun p => by
      rw [primeMassGreenVerticalFiberState_norm_sq]
      rfl⟩

@[simp] theorem primeMassGreenVerticalGlobalState_apply
    (M : ℕ) (s : ℂ) (hs : s ∈ genuineCriticalStrip)
    (p : Nat.Primes) :
    primeMassGreenVerticalGlobalState M s hs p =
      primeMassGreenVerticalFiberState M s p := rfl

/-- The material vertical trace of a mass fiber has zero value coordinate and
critical-amplitude Green bulk as its flux coordinate. -/
theorem primeCarryWeightedVerticalTrace_massFiber
    (M : ℕ) (s : ℂ) (p : Nat.Primes) :
    primeCarryWeightedVerticalTrace (p : ℕ)
        (primeMassGreenVerticalFiberState M s p) =
      (0, (primeCarryGreenBulkCutoffProfile M s p : ℂ)) := by
  rw [primeCarryWeightedVerticalTrace, carryWeightedVerticalTrace_apply]
  apply Prod.ext
  · simp
  · simp only [primeMassGreenVerticalFiberState_zero,
      primeMassGreenVerticalFiberState_one, sub_zero]
    norm_cast
    exact primeAmplitudeUpgrade_massBulk_eq_carryBulk M s p

/-- Real flux profile produced by the primewise material traces. -/
def primeMassGreenVerticalTraceFluxProfile
    (M : ℕ) (s : ℂ) (p : Nat.Primes) : ℝ :=
  (primeCarryWeightedVerticalTrace (p : ℕ)
    (primeMassGreenVerticalFiberState M s p)).2.re

/-- The primewise vertical trace is exactly the previously constructed critical
Green bulk profile. -/
theorem primeMassGreenVerticalTraceFluxProfile_eq
    (M : ℕ) (s : ℂ) (p : Nat.Primes) :
    primeMassGreenVerticalTraceFluxProfile M s p =
      primeCarryGreenBulkCutoffProfile M s p := by
  rw [primeMassGreenVerticalTraceFluxProfile,
    primeCarryWeightedVerticalTrace_massFiber]
  simp

/-- Domain of the global primewise vertical trace on the concrete mass state. -/
def PrimeMassGreenVerticalGlobalTraceDomainAt
    (M : ℕ) (s : ℂ) : Prop :=
  Summable (fun p : Nat.Primes =>
    (primeMassGreenVerticalTraceFluxProfile M s p) ^ 2)

/-- Exact domain threshold for the native vertical trace. -/
theorem primeMassGreenVerticalGlobalTraceDomainAt_iff
    (M : ℕ) (hM : 0 < M) {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    PrimeMassGreenVerticalGlobalTraceDomainAt M s ↔
      criticalDisplacement s.re = 0 := by
  unfold PrimeMassGreenVerticalGlobalTraceDomainAt
  have hfun :
      (fun p : Nat.Primes =>
        (primeMassGreenVerticalTraceFluxProfile M s p) ^ 2) =
      (fun p : Nat.Primes =>
        (primeCarryGreenBulkCutoffProfile M s p) ^ 2) := by
    funext p
    rw [primeMassGreenVerticalTraceFluxProfile_eq]
  rw [hfun]
  exact summable_primeCarryGreenBulkCutoffProfile_sq_iff M hM hs

/-- Final obligation stated directly in the native TFVD trace language. -/
def GenuineZerosLieInPrimeVerticalTraceDomain : Prop :=
  ∀ {s : ℂ}, genuineContinuation s = 0 →
    s ∈ genuineCriticalStrip →
      PrimeMassGreenVerticalGlobalTraceDomainAt 1 s

/-- Scope guard: closing the global vertical trace at every Genuine zero is
exactly strong nonvanishing off the half-abscissa. -/
theorem genuineZerosLieInPrimeVerticalTraceDomain_iff_strongNonvanishing :
    GenuineZerosLieInPrimeVerticalTraceDomain ↔
      GenuineStrongNonvanishingInStrip := by
  constructor
  · intro htrace s hs hoff hzero
    have hcritical :=
      (primeMassGreenVerticalGlobalTraceDomainAt_iff
        1 (by norm_num) hs).1 (htrace hzero hs)
    apply hoff
    unfold criticalDisplacement at hcritical
    linarith
  · intro hstrong s hzero hs
    apply
      (primeMassGreenVerticalGlobalTraceDomainAt_iff
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
