import CPFormal.Analytic.CpGenuineGprePrimeVerticalTraceWeightedBessel

/-!
# No-go for a purely vertical graph-norm proof of the prime trace gate

The global primewise trace is unbounded for a structural reason.  This module
constructs an explicit family with one full mass `p^(-1)` at the first positive
carry level of each prime fiber.

* the family itself is in the global prime-fiber Hilbert space;
* its dressed centered brackets are square-summable over the primes;
* its trace flux is the critical amplitude `p^(-1/2)`, whose square is `1/p`
  and is not summable over the primes.

Therefore membership of both the state and its vertical bracket in the global
Hilbert space cannot by itself imply membership in the global trace domain.
The final half-amplitude gain must use the arithmetic/provenance content of a
Genuine zero, not only the abstract TFVD reconstruction identity.
-/

open scoped BigOperators ENNReal

namespace CPFormal.Analytic.Cp

noncomputable section

set_option maxHeartbeats 800000

/-- One complete first-level mass in the vertical fiber of a prime camera. -/
def primeVerticalTraceNoGoFiber (p : Nat.Primes) : CarryVerticalL2 :=
  lp.single 2 1 ((p : ℝ)⁻¹ : ℂ)

@[simp] theorem primeVerticalTraceNoGoFiber_zero (p : Nat.Primes) :
    primeVerticalTraceNoGoFiber p 0 = 0 := by
  simp [primeVerticalTraceNoGoFiber, lp.single_apply]

@[simp] theorem primeVerticalTraceNoGoFiber_one (p : Nat.Primes) :
    primeVerticalTraceNoGoFiber p 1 = ((p : ℝ)⁻¹ : ℂ) := by
  simp [primeVerticalTraceNoGoFiber, lp.single_apply]

/-- Exact fiber norm. -/
theorem primeVerticalTraceNoGoFiber_norm_sq (p : Nat.Primes) :
    ‖primeVerticalTraceNoGoFiber p‖ ^ 2 = ((p : ℝ)⁻¹) ^ 2 := by
  unfold primeVerticalTraceNoGoFiber
  rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  simp

/-- The material trace upgrades the complete mass to the critical amplitude. -/
theorem primeCarryWeightedVerticalTrace_noGoFiber
    (p : Nat.Primes) :
    primeCarryWeightedVerticalTrace (p : ℕ)
        (primeVerticalTraceNoGoFiber p) =
      (0, (primeCarryAmplitudeRatio p : ℂ)) := by
  rw [primeCarryWeightedVerticalTrace, carryWeightedVerticalTrace_apply]
  apply Prod.ext
  · simp
  · simp only [primeVerticalTraceNoGoFiber_zero,
      primeVerticalTraceNoGoFiber_one, sub_zero]
    have hq := primeCarryAmplitudeRatio_ne_zero_prime p
    have hsq := primeCarryAmplitudeRatio_sq_eq_inv (p : ℕ)
    norm_cast
    calc
      (primeCarryAmplitudeRatio p)⁻¹ * (p : ℝ)⁻¹ =
          (primeCarryAmplitudeRatio p)⁻¹ *
            (primeCarryAmplitudeRatio p) ^ 2 := by rw [hsq]
      _ = primeCarryAmplitudeRatio p := by field_simp [hq]

/-- Real trace-flux profile of the witness. -/
def primeVerticalTraceNoGoFluxProfile (p : Nat.Primes) : ℝ :=
  (primeCarryWeightedVerticalTrace (p : ℕ)
    (primeVerticalTraceNoGoFiber p)).2.re

@[simp] theorem primeVerticalTraceNoGoFluxProfile_eq
    (p : Nat.Primes) :
    primeVerticalTraceNoGoFluxProfile p = primeCarryAmplitudeRatio p := by
  rw [primeVerticalTraceNoGoFluxProfile,
    primeCarryWeightedVerticalTrace_noGoFiber]
  simp

/-- The upgraded trace flux is not square-summable over the prime cameras. -/
theorem not_summable_primeVerticalTraceNoGoFluxProfile_sq :
    ¬ Summable (fun p : Nat.Primes =>
      (primeVerticalTraceNoGoFluxProfile p) ^ 2) := by
  intro hsum
  have honeDiv : Summable (fun p : Nat.Primes => (1 / (p : ℝ))) := by
    refine hsum.congr ?_
    intro p
    rw [primeVerticalTraceNoGoFluxProfile_eq,
      primeCarryAmplitudeRatio_sq_eq_inv]
    simp [one_div]
  exact Nat.Primes.not_summable_one_div honeDiv

/-- Explicit two-coordinate model for the dressed bracket of the witness. -/
def primeVerticalTraceNoGoBracketModel
    (p : Nat.Primes) : CarryVerticalL2 :=
  lp.single 2 1 (-2 * ((p : ℝ)⁻¹ : ℂ)) +
    lp.single 2 2
      ((primeCarryAmplitudeRatio p : ℂ) * ((p : ℝ)⁻¹ : ℂ))

/-- The dressed centered bracket has only levels `1` and `2` active. -/
theorem primeCarryWeightedVerticalCenteredBracket_noGoFiber
    (p : Nat.Primes) :
    primeCarryWeightedVerticalCenteredBracket (p : ℕ)
        (primeVerticalTraceNoGoFiber p) =
      primeVerticalTraceNoGoBracketModel p := by
  ext n
  cases n with
  | zero =>
      simp [primeCarryWeightedVerticalCenteredBracket,
        primeVerticalTraceNoGoBracketModel, lp.single_apply]
  | succ n =>
      rw [primeCarryWeightedVerticalCenteredBracket,
        carryWeightedVerticalCenteredBracket_succ]
      cases n with
      | zero =>
          simp [primeVerticalTraceNoGoFiber,
            primeVerticalTraceNoGoBracketModel, lp.single_apply]
      | succ n =>
          cases n with
          | zero =>
              simp [primeVerticalTraceNoGoFiber,
                primeVerticalTraceNoGoBracketModel, lp.single_apply]
          | succ n =>
              simp [primeVerticalTraceNoGoFiber,
                primeVerticalTraceNoGoBracketModel, lp.single_apply]

/-- The bracket norm loses no more than a fixed multiple of the full mass. -/
theorem norm_primeVerticalTraceNoGoBracketModel_le
    (p : Nat.Primes) :
    ‖primeVerticalTraceNoGoBracketModel p‖ ≤ 3 * (p : ℝ)⁻¹ := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hq0 : 0 ≤ primeCarryAmplitudeRatio p :=
    primeCarryAmplitudeRatio_nonneg p
  have hq1 : primeCarryAmplitudeRatio p ≤ 1 :=
    (primeCarryAmplitudeRatio_lt_one (p : ℕ) p.prop.two_le).le
  unfold primeVerticalTraceNoGoBracketModel
  calc
    ‖lp.single 2 1 (-2 * ((p : ℝ)⁻¹ : ℂ)) +
        lp.single 2 2
          ((primeCarryAmplitudeRatio p : ℂ) * ((p : ℝ)⁻¹ : ℂ))‖ ≤
      ‖lp.single 2 1 (-2 * ((p : ℝ)⁻¹ : ℂ))‖ +
        ‖lp.single 2 2
          ((primeCarryAmplitudeRatio p : ℂ) * ((p : ℝ)⁻¹ : ℂ))‖ :=
        norm_add_le _ _
    _ = 2 * (p : ℝ)⁻¹ +
        primeCarryAmplitudeRatio p * (p : ℝ)⁻¹ := by
      rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2),
        lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), norm_mul]
      simp [abs_of_nonneg hp0, abs_of_nonneg hq0]
    _ ≤ 2 * (p : ℝ)⁻¹ + 1 * (p : ℝ)⁻¹ := by
      gcongr
    _ = 3 * (p : ℝ)⁻¹ := by ring

/-- The bracket outputs of the witness remain square-summable over all primes. -/
theorem summable_primeVerticalTraceNoGoBracket_sq :
    Summable (fun p : Nat.Primes =>
      ‖primeCarryWeightedVerticalCenteredBracket (p : ℕ)
        (primeVerticalTraceNoGoFiber p)‖ ^ 2) := by
  let primeToNat : Nat.Primes → ℕ := fun p => (p : ℕ)
  have hinjective : Function.Injective primeToNat := by
    intro p q hpq
    exact Nat.Primes.coe_nat_injective hpq
  have hnat : Summable (fun n : ℕ => 9 * (((n : ℝ) ^ 2)⁻¹)) :=
    ((Real.summable_nat_pow_inv (p := 2)).2 (by norm_num)).mul_left 9
  have hprime : Summable (fun p : Nat.Primes =>
      9 * (((p : ℝ) ^ 2)⁻¹)) := by
    simpa [primeToNat, Function.comp_def] using
      hnat.comp_injective hinjective
  refine Summable.of_nonneg_of_le
    (fun p => sq_nonneg _)
    (fun p => ?_) hprime
  rw [primeCarryWeightedVerticalCenteredBracket_noGoFiber]
  have hnorm := norm_primeVerticalTraceNoGoBracketModel_le p
  have hnonneg : 0 ≤ ‖primeVerticalTraceNoGoBracketModel p‖ := norm_nonneg _
  have hmass : 0 ≤ 3 * (p : ℝ)⁻¹ := by positivity
  have hsq : ‖primeVerticalTraceNoGoBracketModel p‖ ^ 2 ≤
      (3 * (p : ℝ)⁻¹) ^ 2 := by nlinarith
  calc
    ‖primeVerticalTraceNoGoBracketModel p‖ ^ 2 ≤
        (3 * (p : ℝ)⁻¹) ^ 2 := hsq
    _ = 9 * (((p : ℝ) ^ 2)⁻¹) := by
      rw [mul_pow, inv_pow]
      ring

/-- The witness itself is a legitimate global prime-fiber Hilbert state. -/
def primeVerticalTraceNoGoGlobalState : PrimeCarryVerticalHilbert :=
  let f : PreLp (fun _ : Nat.Primes => CarryVerticalL2) :=
    fun p => primeVerticalTraceNoGoFiber p
  ⟨f, by
    change Memℓp f 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    change Summable (fun p : Nat.Primes =>
      ‖primeVerticalTraceNoGoFiber p‖ ^ 2)
    let primeToNat : Nat.Primes → ℕ := fun p => (p : ℕ)
    have hinjective : Function.Injective primeToNat := by
      intro p q hpq
      exact Nat.Primes.coe_nat_injective hpq
    have hnat : Summable (fun n : ℕ => (((n : ℝ) ^ 2)⁻¹)) :=
      (Real.summable_nat_pow_inv (p := 2)).2 (by norm_num)
    have hprime : Summable (fun p : Nat.Primes =>
        ((p : ℝ)⁻¹) ^ 2) := by
      simpa [primeToNat, Function.comp_def, inv_pow] using
        hnat.comp_injective hinjective
    simpa only [primeVerticalTraceNoGoFiber_norm_sq] using hprime⟩

@[simp] theorem primeVerticalTraceNoGoGlobalState_apply
    (p : Nat.Primes) :
    primeVerticalTraceNoGoGlobalState p = primeVerticalTraceNoGoFiber p := rfl

/-- Exact formulation of the vertical no-go: global state and global bracket
regularity coexist with failure of global trace regularity. -/
theorem exists_global_primeVertical_state_and_bracket_without_trace :
    (∃ x : PrimeCarryVerticalHilbert,
      (∀ p : Nat.Primes, x p = primeVerticalTraceNoGoFiber p) ∧
      Summable (fun p : Nat.Primes =>
        ‖primeCarryWeightedVerticalCenteredBracket (p : ℕ) (x p)‖ ^ 2)) ∧
    ¬ Summable (fun p : Nat.Primes =>
      (primeVerticalTraceNoGoFluxProfile p) ^ 2) := by
  constructor
  · refine ⟨primeVerticalTraceNoGoGlobalState, ?_, ?_⟩
    · intro p
      rfl
    · simpa only [primeVerticalTraceNoGoGlobalState_apply] using
        summable_primeVerticalTraceNoGoBracket_sq
  · exact not_summable_primeVerticalTraceNoGoFluxProfile_sq

end

end CPFormal.Analytic.Cp
