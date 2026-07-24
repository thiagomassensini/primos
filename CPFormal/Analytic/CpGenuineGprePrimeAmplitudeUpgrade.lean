import CPFormal.Analytic.CpGenuineGpreLogJetGreenBulkReadout
import Mathlib.Analysis.PSeries

/-!
# Prime mass profile and the closed amplitude-upgrade gate

The enriched log-jet commutator already reads the Green bulk after inserting
one critical carry amplitude `p^(-1/2)`.  This module separates that dressing
into two canonical stages.

* The native `G_pre` mass profile uses the full first-level mass `p^(-1)`.
  Its square is summable over all prime cameras throughout the open strip.
* The prime amplitude-upgrade multiplies the mass profile by `sqrt(p)`,
  recovering the previously defined critical-amplitude Green profile.

Thus the final observability obligation is a domain-regularity statement for a
closed diagonal multiplier, rather than the construction of the Green bulk
itself.  No zero-to-domain theorem is declared here.
-/

open scoped BigOperators ENNReal

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Green radial coefficient dressed by the complete first-level mass `1/p`.
The two terms display the reflected Dirichlet exponents directly. -/
def primeMassGreenRadialProfile
    (delta : ℝ) (p : Nat.Primes) : ℝ :=
  (p : ℝ) ^ (delta - 1) - (p : ℝ) ^ (-delta - 1)

/-- The mass profile is the critical-amplitude profile dressed by one more
critical amplitude. -/
theorem primeMassGreenRadialProfile_eq_amplitude_mul
    (delta : ℝ) (p : Nat.Primes) :
    primeMassGreenRadialProfile delta p =
      primeCarryAmplitudeRatio p * primeCarryGreenRadialProfile delta p := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  unfold primeMassGreenRadialProfile primeCarryGreenRadialProfile
  rw [← mul_assoc, ← pow_two,
    primeCarryAmplitudeRatio_sq_eq_inv (p : ℕ)]
  unfold cpRadialDifference
  rw [mul_sub, ← Real.rpow_neg_one,
    ← Real.rpow_add hp0, ← Real.rpow_add hp0]
  congr 1 <;> ring

/-- Squared mass-radial profiles are summable over all prime cameras for every
transverse displacement in `(-1/2,1/2)`. -/
theorem summable_primeMassGreenRadialProfile_sq
    {delta : ℝ} (hdeltaLower : -(1 : ℝ) / 2 < delta)
    (hdeltaUpper : delta < (1 : ℝ) / 2) :
    Summable (fun p : Nat.Primes =>
      (primeMassGreenRadialProfile delta p) ^ 2) := by
  let primeToNat : Nat.Primes → ℕ := fun p => (p : ℕ)
  have hinjective : Function.Injective primeToNat := by
    intro p q hpq
    exact Nat.Primes.coe_nat_injective hpq
  have hplusNat :
      Summable (fun n : ℕ => (n : ℝ) ^ (2 * delta - 2)) :=
    (Real.summable_nat_rpow).2 (by linarith)
  have hminusNat :
      Summable (fun n : ℕ => (n : ℝ) ^ (-2 * delta - 2)) :=
    (Real.summable_nat_rpow).2 (by linarith)
  have hplus : Summable (fun p : Nat.Primes =>
      (p : ℝ) ^ (2 * delta - 2)) := by
    simpa [primeToNat, Function.comp_def] using
      hplusNat.comp_injective hinjective
  have hminus : Summable (fun p : Nat.Primes =>
      (p : ℝ) ^ (-2 * delta - 2)) := by
    simpa [primeToNat, Function.comp_def] using
      hminusNat.comp_injective hinjective
  have hmajor : Summable (fun p : Nat.Primes =>
      2 * (p : ℝ) ^ (2 * delta - 2) +
        2 * (p : ℝ) ^ (-2 * delta - 2)) :=
    (hplus.mul_left 2).add (hminus.mul_left 2)
  exact Summable.of_nonneg_of_le
    (fun p => sq_nonneg _)
    (fun p => by
      have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
      let x : ℝ := (p : ℝ) ^ (delta - 1)
      let y : ℝ := (p : ℝ) ^ (-delta - 1)
      have hx : x ^ 2 = (p : ℝ) ^ (2 * delta - 2) := by
        dsimp [x]
        rw [← Real.rpow_mul_natCast hp0]
        congr 1
        ring
      have hy : y ^ 2 = (p : ℝ) ^ (-2 * delta - 2) := by
        dsimp [y]
        rw [← Real.rpow_mul_natCast hp0]
        congr 1
        ring
      unfold primeMassGreenRadialProfile
      change (x - y) ^ 2 ≤ _
      rw [← hx, ← hy]
      nlinarith [sq_nonneg (x + y)])
    hmajor

/-- Finite-cutoff Green bulk with the complete first-level mass dressing. -/
def primeMassGreenBulkCutoffProfile
    (M : ℕ) (s : ℂ) (p : Nat.Primes) : ℝ :=
  primeMassGreenRadialProfile (criticalDisplacement s.re) p *
    (finiteReflectedGradientPairing M s).re

/-- The mass-dressed bulk is one extra critical amplitude times the existing
critical-amplitude bulk. -/
theorem primeMassGreenBulkCutoffProfile_eq_amplitude_mul
    (M : ℕ) (s : ℂ) (p : Nat.Primes) :
    primeMassGreenBulkCutoffProfile M s p =
      primeCarryAmplitudeRatio p *
        primeCarryGreenBulkCutoffProfile M s p := by
  rw [primeMassGreenBulkCutoffProfile,
    primeMassGreenRadialProfile_eq_amplitude_mul,
    primeCarryGreenBulkCutoffProfile_eq]
  ring

/-- Unlike the amplitude-upgraded profile, the native mass profile is square
summable throughout the complete open critical strip. -/
theorem summable_primeMassGreenBulkCutoffProfile_sq
    (M : ℕ) {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Summable (fun p : Nat.Primes =>
      (primeMassGreenBulkCutoffProfile M s p) ^ 2) := by
  have hdelta :
      -(1 : ℝ) / 2 < criticalDisplacement s.re ∧
        criticalDisplacement s.re < (1 : ℝ) / 2 := by
    constructor <;> unfold criticalDisplacement <;> linarith [hs.1, hs.2]
  have hradial := summable_primeMassGreenRadialProfile_sq hdelta.1 hdelta.2
  have hscaled := hradial.mul_left
    ((finiteReflectedGradientPairing M s).re ^ 2)
  simpa [primeMassGreenBulkCutoffProfile, mul_pow, mul_comm, mul_left_comm,
    mul_assoc] using hscaled

/-- Domain of the diagonal prime-amplitude upgrade.  It asks that multiplying
one more time by `p^(1/2)` still gives an `ell^2` prime profile. -/
def PrimeAmplitudeUpgradeDomain
    (v : Nat.Primes → ℝ) : Prop :=
  Summable (fun p : Nat.Primes =>
    ((primeCarryAmplitudeRatio p)⁻¹ * v p) ^ 2)

/-- The amplitude upgrade recovers the critical Green bulk exactly. -/
theorem primeAmplitudeUpgrade_massBulk_eq_carryBulk
    (M : ℕ) (s : ℂ) (p : Nat.Primes) :
    (primeCarryAmplitudeRatio p)⁻¹ *
        primeMassGreenBulkCutoffProfile M s p =
      primeCarryGreenBulkCutoffProfile M s p := by
  rw [primeMassGreenBulkCutoffProfile_eq_amplitude_mul]
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hsqrtPos : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 hp0
  have hratio : primeCarryAmplitudeRatio p ≠ 0 := by
    unfold primeCarryAmplitudeRatio
    exact inv_ne_zero hsqrtPos.ne'
  field_simp [hratio]

/-- Exact domain threshold: the always-existing mass profile can be upgraded
to the critical-amplitude Hilbert profile exactly on the half-abscissa. -/
theorem primeMassGreenBulkCutoffProfile_mem_upgradeDomain_iff
    (M : ℕ) (hM : 0 < M) {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    PrimeAmplitudeUpgradeDomain
        (primeMassGreenBulkCutoffProfile M s) ↔
      criticalDisplacement s.re = 0 := by
  unfold PrimeAmplitudeUpgradeDomain
  have hfun :
      (fun p : Nat.Primes =>
        ((primeCarryAmplitudeRatio p)⁻¹ *
          primeMassGreenBulkCutoffProfile M s p) ^ 2) =
      (fun p : Nat.Primes =>
        (primeCarryGreenBulkCutoffProfile M s p) ^ 2) := by
    funext p
    rw [primeAmplitudeUpgrade_massBulk_eq_carryBulk]
  rw [hfun]
  exact summable_primeCarryGreenBulkCutoffProfile_sq_iff M hM hs

/-- The mass-normalized enriched log-jet readout. -/
def finiteEnrichedNativeGpreMassLogJetGreenBulkReadout
    (p : Nat.Primes) (M : ℕ)
    (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) : ℝ :=
  primeCarryAmplitudeRatio p *
    finiteEnrichedNativeGpreLogJetGreenBulkReadout
      p M kappa omega s

/-- The enriched readout with mass normalization is exactly the universally
square-summable mass Green profile. -/
theorem finiteEnrichedNativeGpreMassLogJetGreenBulkReadout_eq
    (p : Nat.Primes) (M : ℕ)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    finiteEnrichedNativeGpreMassLogJetGreenBulkReadout
        p M kappa omega s =
      primeMassGreenBulkCutoffProfile (3 * M) s p := by
  unfold finiteEnrichedNativeGpreMassLogJetGreenBulkReadout
  rw [finiteEnrichedNativeGpreLogJetGreenBulkReadout_eq
    p M hkappa omega homega s,
    primeMassGreenBulkCutoffProfile_eq_amplitude_mul]

/-- At a nonempty enriched cutoff, domain regularity of the mass-normalized
readout is exactly critical localization. -/
theorem finiteEnrichedNativeGpreMassReadout_mem_upgradeDomain_iff
    (M : ℕ) (hM : 0 < M)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    PrimeAmplitudeUpgradeDomain
        (fun p : Nat.Primes =>
          finiteEnrichedNativeGpreMassLogJetGreenBulkReadout
            p M kappa omega s) ↔
      criticalDisplacement s.re = 0 := by
  have hprofile :
      (fun p : Nat.Primes =>
        finiteEnrichedNativeGpreMassLogJetGreenBulkReadout
          p M kappa omega s) =
      primeMassGreenBulkCutoffProfile (3 * M) s := by
    funext p
    exact finiteEnrichedNativeGpreMassLogJetGreenBulkReadout_eq
      p M hkappa omega homega s
  rw [hprofile]
  exact primeMassGreenBulkCutoffProfile_mem_upgradeDomain_iff
    (3 * M) (by omega) hs

/-- Final obligation in graph-domain form. -/
def GenuineZerosPutMassReadoutInPrimeAmplitudeDomain : Prop :=
  ∀ {s : ℂ}, genuineContinuation s = 0 →
    s ∈ genuineCriticalStrip →
      PrimeAmplitudeUpgradeDomain
        (primeMassGreenBulkCutoffProfile 1 s)

/-- Scope guard: proving the domain regularity from every Genuine zero has
exactly the strength of strong off-critical nonvanishing. -/
theorem genuineZerosPutMassReadoutInPrimeAmplitudeDomain_iff_strongNonvanishing :
    GenuineZerosPutMassReadoutInPrimeAmplitudeDomain ↔
      GenuineStrongNonvanishingInStrip := by
  constructor
  · intro hdomain s hs hoff hzero
    have hcritical :=
      (primeMassGreenBulkCutoffProfile_mem_upgradeDomain_iff
        1 (by norm_num) hs).1 (hdomain hzero hs)
    apply hoff
    unfold criticalDisplacement at hcritical
    linarith
  · intro hstrong s hzero hs
    apply
      (primeMassGreenBulkCutoffProfile_mem_upgradeDomain_iff
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
