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

/-- One complete first-level mass in the vertical fiber of a prime camera. -/
def primeVerticalTraceNoGoFiber (p : Nat.Primes) : CarryVerticalL2 :=
  lp.single 2 1 (((p : ℝ)⁻¹ : ℝ) : ℂ)

@[simp] theorem primeVerticalTraceNoGoFiber_zero (p : Nat.Primes) :
    primeVerticalTraceNoGoFiber p 0 = 0 := by
  simp [primeVerticalTraceNoGoFiber, lp.single_apply]

@[simp] theorem primeVerticalTraceNoGoFiber_one (p : Nat.Primes) :
    primeVerticalTraceNoGoFiber p 1 = ((p : ℝ)⁻¹ : ℂ) := by
  simp [primeVerticalTraceNoGoFiber, lp.single_apply]

@[simp] theorem primeVerticalTraceNoGoFiber_apply_ne_one
    (p : Nat.Primes) {n : ℕ} (hn : n ≠ 1) :
    primeVerticalTraceNoGoFiber p n = 0 := by
  simp [primeVerticalTraceNoGoFiber, lp.single_apply, hn]

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

/-- Sparse coefficient function for the dressed bracket witness. -/
def primeVerticalTraceNoGoBracketCoefficient
    (p : Nat.Primes) (n : ℕ) : ℂ :=
  if n = 1 then -2 * ((p : ℝ)⁻¹ : ℂ)
  else if n = 2 then
    (primeCarryAmplitudeRatio p : ℂ) * ((p : ℝ)⁻¹ : ℂ)
  else 0

/-- Explicit two-coordinate model for the dressed bracket of the witness. -/
def primeVerticalTraceNoGoBracketModel
    (p : Nat.Primes) : CarryVerticalL2 :=
  ∑ n ∈ ({1, 2} : Finset ℕ),
    lp.single 2 n (primeVerticalTraceNoGoBracketCoefficient p n)

@[simp] theorem primeVerticalTraceNoGoBracketModel_zero
    (p : Nat.Primes) :
    primeVerticalTraceNoGoBracketModel p 0 = 0 := by
  simp [primeVerticalTraceNoGoBracketModel,
    primeVerticalTraceNoGoBracketCoefficient, lp.single_apply]

@[simp] theorem primeVerticalTraceNoGoBracketModel_one
    (p : Nat.Primes) :
    primeVerticalTraceNoGoBracketModel p 1 =
      -2 * ((p : ℝ)⁻¹ : ℂ) := by
  simp [primeVerticalTraceNoGoBracketModel,
    primeVerticalTraceNoGoBracketCoefficient, lp.single_apply]

@[simp] theorem primeVerticalTraceNoGoBracketModel_two
    (p : Nat.Primes) :
    primeVerticalTraceNoGoBracketModel p 2 =
      (primeCarryAmplitudeRatio p : ℂ) * ((p : ℝ)⁻¹ : ℂ) := by
  simp [primeVerticalTraceNoGoBracketModel,
    primeVerticalTraceNoGoBracketCoefficient, lp.single_apply]

@[simp] theorem primeVerticalTraceNoGoBracketModel_apply_of_three_le
    (p : Nat.Primes) {n : ℕ} (hn : 3 ≤ n) :
    primeVerticalTraceNoGoBracketModel p n = 0 := by
  have hn1 : n ≠ 1 := by omega
  have hn2 : n ≠ 2 := by omega
  simp [primeVerticalTraceNoGoBracketModel,
    primeVerticalTraceNoGoBracketCoefficient, lp.single_apply, hn1, hn2]

/-- The dressed centered bracket has only levels `1` and `2` active. -/
theorem primeCarryWeightedVerticalCenteredBracket_noGoFiber
    (p : Nat.Primes) :
    primeCarryWeightedVerticalCenteredBracket (p : ℕ)
        (primeVerticalTraceNoGoFiber p) =
      primeVerticalTraceNoGoBracketModel p := by
  change carryWeightedVerticalCenteredBracket (primeCarryAmplitudeRatio p)
      (primeVerticalTraceNoGoFiber p) = primeVerticalTraceNoGoBracketModel p
  ext n
  cases n with
  | zero =>
      rw [carryWeightedVerticalCenteredBracket_zero,
        primeVerticalTraceNoGoBracketModel_zero]
  | succ n =>
      rw [carryWeightedVerticalCenteredBracket_succ]
      cases n with
      | zero =>
          rw [primeVerticalTraceNoGoFiber_apply_ne_one p (by norm_num : 2 ≠ 1),
            primeVerticalTraceNoGoFiber_one,
            primeVerticalTraceNoGoFiber_zero,
            primeVerticalTraceNoGoBracketModel_one]
          ring
      | succ n =>
          cases n with
          | zero =>
              rw [primeVerticalTraceNoGoFiber_apply_ne_one p (by norm_num : 3 ≠ 1),
                primeVerticalTraceNoGoFiber_apply_ne_one p (by norm_num : 2 ≠ 1),
                primeVerticalTraceNoGoFiber_one,
                primeVerticalTraceNoGoBracketModel_two]
              ring
          | succ n =>
              rw [primeVerticalTraceNoGoFiber_apply_ne_one p (by omega),
                primeVerticalTraceNoGoFiber_apply_ne_one p (by omega),
                primeVerticalTraceNoGoFiber_apply_ne_one p (by omega),
                primeVerticalTraceNoGoBracketModel_apply_of_three_le p (by omega)]
              simp only [mul_zero, sub_zero, zero_add]

/-- Exact squared norm of the two-coordinate bracket model. -/
theorem primeVerticalTraceNoGoBracketModel_norm_sq
    (p : Nat.Primes) :
    ‖primeVerticalTraceNoGoBracketModel p‖ ^ 2 =
      (2 * (p : ℝ)⁻¹) ^ 2 +
        (primeCarryAmplitudeRatio p * (p : ℝ)⁻¹) ^ 2 := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hq0 : 0 ≤ primeCarryAmplitudeRatio p :=
    primeCarryAmplitudeRatio_nonneg p
  simpa [primeVerticalTraceNoGoBracketModel,
    primeVerticalTraceNoGoBracketCoefficient, Real.norm_eq_abs,
    abs_of_nonneg hp0, abs_of_nonneg hq0, norm_mul] using
    (lp.norm_sum_single
      (E := fun _ : ℕ => ℂ)
      (p := (2 : ℝ≥0∞)) (by norm_num)
      (primeVerticalTraceNoGoBracketCoefficient p)
      ({1, 2} : Finset ℕ))

/-- The bracket norm loses no more than a fixed multiple of the full mass. -/
theorem norm_primeVerticalTraceNoGoBracketModel_le
    (p : Nat.Primes) :
    ‖primeVerticalTraceNoGoBracketModel p‖ ≤ 3 * (p : ℝ)⁻¹ := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hq0 : 0 ≤ primeCarryAmplitudeRatio p :=
    primeCarryAmplitudeRatio_nonneg p
  have hq1 : primeCarryAmplitudeRatio p ≤ 1 :=
    (primeCarryAmplitudeRatio_lt_one (p : ℕ) p.prop.two_le).le
  have hmul : primeCarryAmplitudeRatio p * (p : ℝ)⁻¹ ≤ (p : ℝ)⁻¹ :=
    mul_le_of_le_one_left hp0 hq1
  have hmul0 : 0 ≤ primeCarryAmplitudeRatio p * (p : ℝ)⁻¹ :=
    mul_nonneg hq0 hp0
  have hmulSq :
      (primeCarryAmplitudeRatio p * (p : ℝ)⁻¹) ^ 2 ≤
        ((p : ℝ)⁻¹) ^ 2 := by
    nlinarith
  have hsq : ‖primeVerticalTraceNoGoBracketModel p‖ ^ 2 ≤
      (3 * (p : ℝ)⁻¹) ^ 2 := by
    rw [primeVerticalTraceNoGoBracketModel_norm_sq]
    nlinarith [sq_nonneg ((p : ℝ)⁻¹)]
  have hnorm0 : 0 ≤ ‖primeVerticalTraceNoGoBracketModel p‖ := norm_nonneg _
  have hbound0 : 0 ≤ 3 * (p : ℝ)⁻¹ := by positivity
  nlinarith

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
    exact hprime.congr fun p => by
      simpa [f] using (primeVerticalTraceNoGoFiber_norm_sq p).symm⟩

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
