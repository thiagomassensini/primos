import CPFormal.Analytic.CpGenuineGprePrimeAmplitudeUpgrade

/-!
# Hilbert graph of the prime-amplitude upgrade

The mass-normalized Green profile is a genuine vector of the prime-camera
Hilbert space at every point of the open strip.  This module constructs that
vector, formulates the diagonal multiplication by `sqrt(p)` as a graph
relation, and identifies graph-liftability of the mass state with critical
localization.

The same statement is also expressed through uniformly bounded finite prime
atlases.  No zero-to-graph-lift theorem is assumed.
-/

open scoped BigOperators ENNReal

namespace CPFormal.Analytic.Cp

noncomputable section

/-- The globally square-summable mass-normalized Green state. -/
def primeMassGreenBulkState
    (M : ℕ) (s : ℂ) (hs : s ∈ genuineCriticalStrip) :
    PrimeGreenCameraHilbert :=
  let f : PreLp (fun _ : Nat.Primes => ℝ) :=
    fun p => primeMassGreenBulkCutoffProfile M s p
  ⟨f, by
    change Memℓp f 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    simpa [f, Real.norm_eq_abs, sq_abs] using
      summable_primeMassGreenBulkCutoffProfile_sq M hs⟩

@[simp] theorem primeMassGreenBulkState_apply
    (M : ℕ) (s : ℂ) (hs : s ∈ genuineCriticalStrip)
    (p : Nat.Primes) :
    primeMassGreenBulkState M s hs p =
      primeMassGreenBulkCutoffProfile M s p := rfl

/-- Graph relation for the diagonal upgrade by the inverse critical amplitude,
i.e. by `sqrt(p)`. -/
def IsPrimeAmplitudeUpgradeGraphPair
    (mass amplitude : PrimeGreenCameraHilbert) : Prop :=
  ∀ p : Nat.Primes,
    amplitude p = (primeCarryAmplitudeRatio p)⁻¹ * mass p

/-- A mass state has an amplitude-upgraded Hilbert partner exactly when its
coordinate function belongs to the previously defined domain. -/
theorem exists_primeAmplitudeUpgradeGraphPair_iff
    (mass : PrimeGreenCameraHilbert) :
    (∃ amplitude : PrimeGreenCameraHilbert,
        IsPrimeAmplitudeUpgradeGraphPair mass amplitude) ↔
      PrimeAmplitudeUpgradeDomain mass := by
  constructor
  · rintro ⟨amplitude, hgraph⟩
    have hsum := (lp.memℓp amplitude).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    have hsum' : Summable (fun p : Nat.Primes => (amplitude p) ^ 2) := by
      simpa [Real.norm_eq_abs, sq_abs] using hsum
    unfold PrimeAmplitudeUpgradeDomain
    exact hsum'.congr fun p => by rw [hgraph p]
  · intro hdomain
    let f : PreLp (fun _ : Nat.Primes => ℝ) :=
      fun p => (primeCarryAmplitudeRatio p)⁻¹ * mass p
    have hf : Memℓp f 2 := by
      rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
      apply hdomain.congr
      intro p
      dsimp [f]
      simp only [Real.norm_eq_abs, mul_pow, inv_pow, sq_abs]
    refine ⟨⟨f, hf⟩, ?_⟩
    intro p
    rfl

/-- Graph-liftability of the concrete mass state is exactly the
half-abscissa condition. -/
theorem exists_primeAmplitudeUpgradeGraphPair_massState_iff
    (M : ℕ) (hM : 0 < M) {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    (∃ amplitude : PrimeGreenCameraHilbert,
        IsPrimeAmplitudeUpgradeGraphPair
          (primeMassGreenBulkState M s hs) amplitude) ↔
      criticalDisplacement s.re = 0 := by
  rw [exists_primeAmplitudeUpgradeGraphPair_iff]
  have hfun :
      (primeMassGreenBulkState M s hs : Nat.Primes → ℝ) =
        primeMassGreenBulkCutoffProfile M s := by
    funext p
    rfl
  rw [hfun]
  exact primeMassGreenBulkCutoffProfile_mem_upgradeDomain_iff M hM hs

/-- Finite-atlas truncation of the always-existing mass state. -/
def primeMassGreenBulkFiniteState
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) :
    PrimeGreenCameraHilbert :=
  ∑ p ∈ S,
    lp.single 2 p (primeMassGreenBulkCutoffProfile M s p)

/-- Finite-atlas truncation after applying the amplitude upgrade. -/
def primeAmplitudeUpgradedMassFiniteState
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) :
    PrimeGreenCameraHilbert :=
  ∑ p ∈ S,
    lp.single 2 p
      ((primeCarryAmplitudeRatio p)⁻¹ *
        primeMassGreenBulkCutoffProfile M s p)

/-- On every finite atlas, the upgraded mass state is literally the existing
critical-amplitude Green state. -/
theorem primeAmplitudeUpgradedMassFiniteState_eq_greenBulkFiniteState
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) :
    primeAmplitudeUpgradedMassFiniteState M s S =
      primeGreenBulkFiniteState M s S := by
  unfold primeAmplitudeUpgradedMassFiniteState primeGreenBulkFiniteState
  apply Finset.sum_congr rfl
  intro p hp
  rw [primeAmplitudeUpgrade_massBulk_eq_carryBulk]

/-- Exact norm ledger for a finite upgraded atlas. -/
theorem primeAmplitudeUpgradedMassFiniteState_norm_sq
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) :
    ‖primeAmplitudeUpgradedMassFiniteState M s S‖ ^ 2 =
      ∑ p ∈ S,
        ((primeCarryAmplitudeRatio p)⁻¹ *
          primeMassGreenBulkCutoffProfile M s p) ^ 2 := by
  calc
    ‖primeAmplitudeUpgradedMassFiniteState M s S‖ ^ 2 =
        ∑ p ∈ S,
          ‖(primeCarryAmplitudeRatio p)⁻¹ *
            primeMassGreenBulkCutoffProfile M s p‖ ^ 2 := by
      simpa [primeAmplitudeUpgradedMassFiniteState] using
        (lp.norm_sum_single
          (E := fun _ : Nat.Primes => ℝ)
          (p := (2 : ℝ≥0∞)) (by norm_num)
          (fun p : Nat.Primes =>
            (primeCarryAmplitudeRatio p)⁻¹ *
              primeMassGreenBulkCutoffProfile M s p) S)
    _ = ∑ p ∈ S,
          ((primeCarryAmplitudeRatio p)⁻¹ *
            primeMassGreenBulkCutoffProfile M s p) ^ 2 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Real.norm_eq_abs, sq_abs]

/-- Uniform graph control over all finite prime atlases. -/
def PrimeAmplitudeUpgradedMassFiniteStatesBounded
    (M : ℕ) (s : ℂ) : Prop :=
  ∃ C : ℝ, ∀ S : Finset Nat.Primes,
    ‖primeAmplitudeUpgradedMassFiniteState M s S‖ ^ 2 ≤ C

/-- Uniform boundedness of the finite graph outputs is exactly critical
localization. -/
theorem primeAmplitudeUpgradedMassFiniteStatesBounded_iff
    (M : ℕ) (hM : 0 < M) {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    PrimeAmplitudeUpgradedMassFiniteStatesBounded M s ↔
      criticalDisplacement s.re = 0 := by
  constructor
  · rintro ⟨C, hC⟩
    apply (primeGreenBulkFiniteStatesBounded_iff M hM hs).1
    refine ⟨C, ?_⟩
    intro S
    rw [← primeAmplitudeUpgradedMassFiniteState_eq_greenBulkFiniteState]
    exact hC S
  · intro hcritical
    rcases (primeGreenBulkFiniteStatesBounded_iff M hM hs).2 hcritical with
      ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro S
    rw [primeAmplitudeUpgradedMassFiniteState_eq_greenBulkFiniteState]
    exact hC S

/-- Final zero-to-graph-boundedness obligation. -/
def GenuineZerosBoundPrimeAmplitudeUpgradeGraph : Prop :=
  ∀ {s : ℂ}, genuineContinuation s = 0 →
    s ∈ genuineCriticalStrip →
      PrimeAmplitudeUpgradedMassFiniteStatesBounded 1 s

/-- The graph-boundedness formulation has exactly the strength of strong
Genuine nonvanishing. -/
theorem genuineZerosBoundPrimeAmplitudeUpgradeGraph_iff_strongNonvanishing :
    GenuineZerosBoundPrimeAmplitudeUpgradeGraph ↔
      GenuineStrongNonvanishingInStrip := by
  constructor
  · intro hgraph s hs hoff hzero
    have hcritical :=
      (primeAmplitudeUpgradedMassFiniteStatesBounded_iff
        1 (by norm_num) hs).1 (hgraph hzero hs)
    apply hoff
    unfold criticalDisplacement at hcritical
    linarith
  · intro hstrong s hzero hs
    apply
      (primeAmplitudeUpgradedMassFiniteStatesBounded_iff
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
