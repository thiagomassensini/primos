import CPFormal.Analytic.CpPrimeCarryDefectBessel
import CPFormal.Analytic.CpGenuineGprePrimeVerticalTraceAtlas

/-!
# Crosswalk from enriched Green readouts to centered carry axes

The centered carry axis of a prime camera has squared norm `(p - 1) / p`.
This module constructs its canonical dual axis and uses the enriched TFVD--
`G_pre` log-jet readout as the coefficient of that dual axis.

For every finite prime atlas this gives one common, finitely supported Hilbert
state `X_(M,s,S)` such that

`<psi_p, X_(M,s,S)> = enrichedGreenReadout(p,M,s)`

for every active camera `p in S`.  The state is built from the independently
defined provenance-preserving log-jet readout; the Green bulk theorem is used
only afterwards to identify the recovered coefficient.

The norm ledger is two-sided:

`sum readout_p^2 <= ||X||^2 <= 2 * sum readout_p^2`.

Consequently finite realization is exact, while uniform boundedness as the
prime atlas grows is neither assumed nor obtained for free.  It remains
exactly equivalent to the already isolated critical localization obligation.
-/

open scoped BigOperators ENNReal

namespace CPFormal.Analytic.Cp

noncomputable section

private theorem prime_coe_sub_one_pos (p : Nat.Primes) :
    0 < (p : ℝ) - 1 := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  linarith

/-- Canonical dual of the critically dressed centered carry axis. -/
def primeCriticalCenteredCarryDualAxis
    (p : Nat.Primes) : PrimeCarryResidueHilbert p :=
  ((p : ℝ) / ((p : ℝ) - 1)) • primeCriticalCenteredCarryAxis p

/-- The centered carry axis and its canonical dual have unit pairing. -/
@[simp] theorem inner_primeCriticalCenteredCarryAxis_dualAxis
    (p : Nat.Primes) :
    inner ℝ (primeCriticalCenteredCarryAxis p)
      (primeCriticalCenteredCarryDualAxis p) = 1 := by
  unfold primeCriticalCenteredCarryDualAxis
  rw [inner_smul_right, real_inner_self_eq_norm_sq,
    primeCriticalCenteredCarryAxis_norm_sq]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := ne_of_gt (prime_coe_sub_one_pos p)
  field_simp [hp0, hp1]

/-- Exact squared norm of the dual axis. -/
theorem primeCriticalCenteredCarryDualAxis_norm_sq
    (p : Nat.Primes) :
    ‖primeCriticalCenteredCarryDualAxis p‖ ^ 2 =
      (p : ℝ) / ((p : ℝ) - 1) := by
  have hratio : 0 ≤ (p : ℝ) / ((p : ℝ) - 1) := by
    exact div_nonneg (by positivity) (le_of_lt (prime_coe_sub_one_pos p))
  unfold primeCriticalCenteredCarryDualAxis
  rw [norm_smul, Real.norm_eq_abs, mul_pow,
    abs_of_nonneg hratio, primeCriticalCenteredCarryAxis_norm_sq]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := ne_of_gt (prime_coe_sub_one_pos p)
  field_simp [hp0, hp1]

/-- The dual-axis squared norm is at least one. -/
theorem one_le_primeCriticalCenteredCarryDualAxis_norm_sq
    (p : Nat.Primes) :
    1 ≤ ‖primeCriticalCenteredCarryDualAxis p‖ ^ 2 := by
  rw [primeCriticalCenteredCarryDualAxis_norm_sq]
  apply (le_div_iff₀ (prime_coe_sub_one_pos p)).2
  linarith

/-- Uniform upper bound for every prime dual axis. -/
theorem primeCriticalCenteredCarryDualAxis_norm_sq_le_two
    (p : Nat.Primes) :
    ‖primeCriticalCenteredCarryDualAxis p‖ ^ 2 ≤ 2 := by
  rw [primeCriticalCenteredCarryDualAxis_norm_sq]
  apply (div_le_iff₀ (prime_coe_sub_one_pos p)).2
  have hpTwo : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
  linarith

/-- Local residue-fiber state obtained from the independently defined enriched
log-jet provenance readout. -/
def finiteEnrichedPrimeCarryDefectProvenanceState
    (p : Nat.Primes) (M : ℕ)
    (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) : PrimeCarryResidueHilbert p :=
  finiteEnrichedNativeGpreLogJetGreenBulkReadout
      p M kappa omega s • primeCriticalCenteredCarryDualAxis p

/-- The centered carry axis reads back exactly the enriched log-jet scalar. -/
@[simp] theorem inner_primeCriticalCenteredCarryAxis_provenanceState
    (p : Nat.Primes) (M : ℕ)
    (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) :
    inner ℝ (primeCriticalCenteredCarryAxis p)
      (finiteEnrichedPrimeCarryDefectProvenanceState
        p M kappa omega s) =
      finiteEnrichedNativeGpreLogJetGreenBulkReadout
        p M kappa omega s := by
  unfold finiteEnrichedPrimeCarryDefectProvenanceState
  rw [inner_smul_right,
    inner_primeCriticalCenteredCarryAxis_dualAxis]
  ring

/-- After decoding the enriched coordinates, the recovered carry coefficient is
exactly the centered prime Green bulk. -/
theorem inner_primeCriticalCenteredCarryAxis_provenanceState_eq_greenBulk
    (p : Nat.Primes) (M : ℕ)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    inner ℝ (primeCriticalCenteredCarryAxis p)
      (finiteEnrichedPrimeCarryDefectProvenanceState
        p M kappa omega s) =
      primeCarryGreenBulkCutoffProfile (3 * M) s p := by
  rw [inner_primeCriticalCenteredCarryAxis_provenanceState,
    finiteEnrichedNativeGpreLogJetGreenBulkReadout_eq
      p M hkappa omega homega s]

/-- Exact local norm ledger for the provenance state. -/
theorem finiteEnrichedPrimeCarryDefectProvenanceState_norm_sq
    (p : Nat.Primes) (M : ℕ)
    (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) :
    ‖finiteEnrichedPrimeCarryDefectProvenanceState
        p M kappa omega s‖ ^ 2 =
      ((p : ℝ) / ((p : ℝ) - 1)) *
        (finiteEnrichedNativeGpreLogJetGreenBulkReadout
          p M kappa omega s) ^ 2 := by
  unfold finiteEnrichedPrimeCarryDefectProvenanceState
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    primeCriticalCenteredCarryDualAxis_norm_sq]
  ring

/-- One fixed Hilbert space carrying the residue fibers of all prime cameras. -/
abbrev PrimeCarryDefectGlobalHilbert :=
  lp (fun p : Nat.Primes => PrimeCarryResidueHilbert p) 2

/-- The centered carry axis inserted in its own global prime coordinate. -/
def primeCriticalCenteredCarryGlobalAxis
    (p : Nat.Primes) : PrimeCarryDefectGlobalHilbert :=
  lp.single 2 p (primeCriticalCenteredCarryAxis p)

/-- Coordinate formula for the global centered carry axis. -/
@[simp] theorem inner_primeCriticalCenteredCarryGlobalAxis
    (p : Nat.Primes) (x : PrimeCarryDefectGlobalHilbert) :
    inner ℝ (primeCriticalCenteredCarryGlobalAxis p) x =
      inner ℝ (primeCriticalCenteredCarryAxis p) (x p) := by
  unfold primeCriticalCenteredCarryGlobalAxis
  rw [lp.inner_single_left]

/-- Canonical common state on a finite prime atlas, assembled directly from the
unit-scale enriched TFVD--`G_pre` provenance readouts. -/
def canonicalEnrichedPrimeCarryDefectProvenanceState
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) :
    PrimeCarryDefectGlobalHilbert :=
  ∑ p ∈ S,
    lp.single 2 p
      (finiteEnrichedPrimeCarryDefectProvenanceState
        p M 1 (fun _ => 1) s)

/-- Coordinates of the common finite-atlas provenance state. -/
@[simp] theorem canonicalEnrichedPrimeCarryDefectProvenanceState_apply
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) (p : Nat.Primes) :
    canonicalEnrichedPrimeCarryDefectProvenanceState M s S p =
      if p ∈ S then
        finiteEnrichedPrimeCarryDefectProvenanceState
          p M 1 (fun _ => 1) s
      else 0 := by
  classical
  simp only [canonicalEnrichedPrimeCarryDefectProvenanceState,
    lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single,
    Finset.sum_pi_single]

/-- Every active centered carry axis extracts its own enriched Green readout
from the same common finite-atlas state. -/
theorem inner_globalCarryAxis_canonicalProvenanceState
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes)
    (p : Nat.Primes) (hp : p ∈ S) :
    inner ℝ (primeCriticalCenteredCarryGlobalAxis p)
      (canonicalEnrichedPrimeCarryDefectProvenanceState M s S) =
      finiteEnrichedNativeGpreLogJetGreenBulkReadout
        p M 1 (fun _ => 1) s := by
  rw [inner_primeCriticalCenteredCarryGlobalAxis,
    canonicalEnrichedPrimeCarryDefectProvenanceState_apply,
    if_pos hp,
    inner_primeCriticalCenteredCarryAxis_provenanceState]

/-- The same coefficient is the centered Green bulk at cutoff `3M`. -/
theorem inner_globalCarryAxis_canonicalProvenanceState_eq_greenBulk
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes)
    (p : Nat.Primes) (hp : p ∈ S) :
    inner ℝ (primeCriticalCenteredCarryGlobalAxis p)
      (canonicalEnrichedPrimeCarryDefectProvenanceState M s S) =
      primeCarryGreenBulkCutoffProfile (3 * M) s p := by
  rw [inner_globalCarryAxis_canonicalProvenanceState M s S p hp,
    finiteEnrichedNativeGpreLogJetGreenBulkReadout_eq
      p M (by norm_num) (fun _ => 1) (by intro m; norm_num) s]

/-- Exact squared norm of the common finite-atlas provenance state. -/
theorem canonicalEnrichedPrimeCarryDefectProvenanceState_norm_sq
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) :
    ‖canonicalEnrichedPrimeCarryDefectProvenanceState M s S‖ ^ 2 =
      ∑ p ∈ S,
        ((p : ℝ) / ((p : ℝ) - 1)) *
          (finiteEnrichedNativeGpreLogJetGreenBulkReadout
            p M 1 (fun _ => 1) s) ^ 2 := by
  have hraw :=
    lp.norm_sum_single
      (E := fun p : Nat.Primes => PrimeCarryResidueHilbert p)
      (p := (2 : ℝ≥0∞)) (by norm_num)
      (fun p : Nat.Primes =>
        finiteEnrichedPrimeCarryDefectProvenanceState
          p M 1 (fun _ => 1) s) S
  calc
    ‖canonicalEnrichedPrimeCarryDefectProvenanceState M s S‖ ^ 2 =
        ∑ p ∈ S,
          ‖finiteEnrichedPrimeCarryDefectProvenanceState
            p M 1 (fun _ => 1) s‖ ^ 2 := by
              simpa [canonicalEnrichedPrimeCarryDefectProvenanceState]
                using hraw
    _ = ∑ p ∈ S,
        ((p : ℝ) / ((p : ℝ) - 1)) *
          (finiteEnrichedNativeGpreLogJetGreenBulkReadout
            p M 1 (fun _ => 1) s) ^ 2 := by
              apply Finset.sum_congr rfl
              intro p hp
              rw [finiteEnrichedPrimeCarryDefectProvenanceState_norm_sq]

/-- Bessel analysis estimate for the centered carry axes in the global prime
Hilbert space. -/
theorem sum_sq_inner_primeCriticalCenteredCarryGlobalAxis_le_norm_sq
    (S : Finset Nat.Primes) (x : PrimeCarryDefectGlobalHilbert) :
    (∑ p ∈ S,
      (inner ℝ (primeCriticalCenteredCarryGlobalAxis p) x) ^ 2) ≤
      ‖x‖ ^ 2 := by
  have hpoint : ∀ p : Nat.Primes,
      (inner ℝ (primeCriticalCenteredCarryGlobalAxis p) x) ^ 2 ≤
        ‖x p‖ ^ 2 := by
    intro p
    rw [inner_primeCriticalCenteredCarryGlobalAxis]
    have hinner :=
      abs_real_inner_le_norm (primeCriticalCenteredCarryAxis p) (x p)
    have haxis := primeCriticalCenteredCarryAxis_norm_le_one p
    have hnorm :
        |inner ℝ (primeCriticalCenteredCarryAxis p) (x p)| ≤ ‖x p‖ := by
      calc
        |inner ℝ (primeCriticalCenteredCarryAxis p) (x p)| ≤
            ‖primeCriticalCenteredCarryAxis p‖ * ‖x p‖ := hinner
        _ ≤ 1 * ‖x p‖ :=
          mul_le_mul_of_nonneg_right haxis (norm_nonneg _)
        _ = ‖x p‖ := one_mul _
    have habs0 :
        0 ≤ |inner ℝ (primeCriticalCenteredCarryAxis p) (x p)| :=
      abs_nonneg _
    have hx0 : 0 ≤ ‖x p‖ := norm_nonneg _
    have hsq := (sq_le_sq₀ habs0 hx0).2 hnorm
    simpa [sq_abs] using hsq
  calc
    (∑ p ∈ S,
        (inner ℝ (primeCriticalCenteredCarryGlobalAxis p) x) ^ 2) ≤
        ∑ p ∈ S, ‖x p‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro p hp
          exact hpoint p
    _ ≤ ‖x‖ ^ 2 := by
      simpa using
        (lp.sum_rpow_le_norm_rpow
          (E := fun p : Nat.Primes => PrimeCarryResidueHilbert p)
          (p := (2 : ℝ≥0∞)) (by norm_num) x S)

/-- The common-state norm dominates the complete finite Green readout ledger. -/
theorem sum_sq_enrichedGreenReadout_le_provenanceState_norm_sq
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) :
    (∑ p ∈ S,
      (finiteEnrichedNativeGpreLogJetGreenBulkReadout
        p M 1 (fun _ => 1) s) ^ 2) ≤
      ‖canonicalEnrichedPrimeCarryDefectProvenanceState M s S‖ ^ 2 := by
  have hbessel :=
    sum_sq_inner_primeCriticalCenteredCarryGlobalAxis_le_norm_sq
      S (canonicalEnrichedPrimeCarryDefectProvenanceState M s S)
  convert hbessel using 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [inner_globalCarryAxis_canonicalProvenanceState M s S p hp]

/-- Conversely, the common-state norm loses at most the universal factor two. -/
theorem canonicalProvenanceState_norm_sq_le_two_mul_sum_sq_readout
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) :
    ‖canonicalEnrichedPrimeCarryDefectProvenanceState M s S‖ ^ 2 ≤
      2 * ∑ p ∈ S,
        (finiteEnrichedNativeGpreLogJetGreenBulkReadout
          p M 1 (fun _ => 1) s) ^ 2 := by
  rw [canonicalEnrichedPrimeCarryDefectProvenanceState_norm_sq]
  calc
    (∑ p ∈ S,
        ((p : ℝ) / ((p : ℝ) - 1)) *
          (finiteEnrichedNativeGpreLogJetGreenBulkReadout
            p M 1 (fun _ => 1) s) ^ 2) ≤
      ∑ p ∈ S,
        2 * (finiteEnrichedNativeGpreLogJetGreenBulkReadout
          p M 1 (fun _ => 1) s) ^ 2 := by
            apply Finset.sum_le_sum
            intro p hp
            exact mul_le_mul_of_nonneg_right
              (by
                rw [← primeCriticalCenteredCarryDualAxis_norm_sq]
                exact primeCriticalCenteredCarryDualAxis_norm_sq_le_two p)
              (sq_nonneg _)
    _ = 2 * ∑ p ∈ S,
        (finiteEnrichedNativeGpreLogJetGreenBulkReadout
          p M 1 (fun _ => 1) s) ^ 2 := by
            rw [Finset.mul_sum]

/-- Uniform control of the common centered-carry provenance states. -/
def CanonicalEnrichedPrimeCarryDefectProvenanceStatesBounded
    (M : ℕ) (s : ℂ) : Prop :=
  ∃ C : ℝ, ∀ S : Finset Nat.Primes,
    ‖canonicalEnrichedPrimeCarryDefectProvenanceState M s S‖ ^ 2 ≤ C

/-- Uniform boundedness of the common carry states is equivalent to uniform
boundedness of the scalar enriched Green atlases. -/
theorem canonicalEnrichedPrimeCarryDefectProvenanceStatesBounded_iff_greenAtlasesBounded
    (M : ℕ) (s : ℂ) :
    CanonicalEnrichedPrimeCarryDefectProvenanceStatesBounded M s ↔
      CanonicalEnrichedGpreLogJetGreenAtlasesBounded M s := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro S
    rw [canonicalEnrichedGpreLogJetGreenAtlasState_norm_sq]
    exact
      (sum_sq_enrichedGreenReadout_le_provenanceState_norm_sq M s S).trans
        (hC S)
  · rintro ⟨C, hC⟩
    refine ⟨2 * C, ?_⟩
    intro S
    have hstate :=
      canonicalProvenanceState_norm_sq_le_two_mul_sum_sq_readout M s S
    have hgreen := hC S
    rw [canonicalEnrichedGpreLogJetGreenAtlasState_norm_sq] at hgreen
    nlinarith

/-- At every nonempty cutoff, uniform boundedness of the common centered-carry
states selects exactly the half-abscissa. -/
theorem canonicalEnrichedPrimeCarryDefectProvenanceStatesBounded_iff
    (M : ℕ) (hM : 0 < M) {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    CanonicalEnrichedPrimeCarryDefectProvenanceStatesBounded M s ↔
      criticalDisplacement s.re = 0 := by
  rw [canonicalEnrichedPrimeCarryDefectProvenanceStatesBounded_iff_greenAtlasesBounded,
    canonicalEnrichedGpreLogJetGreenAtlasesBounded_iff M hM hs]

end

end CPFormal.Analytic.Cp
