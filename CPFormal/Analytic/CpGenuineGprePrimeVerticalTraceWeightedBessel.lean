import CPFormal.Analytic.CpGenuineGprePrimeVerticalTraceDualTest

/-!
# Weighted Bessel estimate and the exact half-amplitude loss

The mass-normalized enriched log-jet readout is square-summable over all prime
cameras throughout the open critical strip.  The native vertical trace removes
one critical carry amplitude `p^(-1/2)`.  Consequently, a scalar test of the
trace outputs is controlled a priori by the coefficient norm with weight `p`.

This module proves that weighted Bessel estimate exactly.  It also proves the
finite-atlas version with a constant proportional to the largest prime in the
atlas.  Thus the last zero-to-domain theorem must supply precisely a uniform
half-amplitude smoothing gain: replace `sum p * coeff_p^2` by
`sum coeff_p^2` at a Genuine zero.

No such smoothing gain is assumed here.
-/

open scoped BigOperators ENNReal

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Scalar test formed from the mass-normalized enriched log-jet readouts. -/
def canonicalEnrichedGpreMassLogJetGreenScalarTest
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes)
    (coeff : Nat.Primes → ℝ) : ℝ :=
  ∑ p ∈ S,
    coeff p * finiteEnrichedNativeGpreMassLogJetGreenBulkReadout
      p M 1 (fun _ => 1) s

/-- The critical carry amplitude is nonzero on every prime camera. -/
theorem primeCarryAmplitudeRatio_ne_zero_prime (p : Nat.Primes) :
    primeCarryAmplitudeRatio p ≠ 0 := by
  unfold primeCarryAmplitudeRatio
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  exact inv_ne_zero (Real.sqrt_pos.2 hp0).ne'

/-- Removing the mass dressing transfers the inverse critical amplitude to the
scalar test coefficient. -/
theorem canonicalEnrichedGpreLogJetGreenScalarTest_eq_massTest
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes)
    (coeff : Nat.Primes → ℝ) :
    canonicalEnrichedGpreLogJetGreenScalarTest M s S coeff =
      canonicalEnrichedGpreMassLogJetGreenScalarTest M s S
        (fun p => (primeCarryAmplitudeRatio p)⁻¹ * coeff p) := by
  unfold canonicalEnrichedGpreLogJetGreenScalarTest
    canonicalEnrichedGpreMassLogJetGreenScalarTest
    finiteEnrichedNativeGpreMassLogJetGreenBulkReadout
  apply Finset.sum_congr rfl
  intro p hp
  have hq := primeCarryAmplitudeRatio_ne_zero_prime p
  field_simp [hq]
  ring

/-- Squaring the inverse critical amplitude produces exactly the prime weight. -/
theorem inv_primeCarryAmplitudeRatio_mul_sq
    (p : Nat.Primes) (a : ℝ) :
    ((primeCarryAmplitudeRatio p)⁻¹ * a) ^ 2 =
      (p : ℝ) * a ^ 2 := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
  have hq := primeCarryAmplitudeRatio_ne_zero_prime p
  rw [mul_pow, inv_pow, primeCarryAmplitudeRatio_sq_eq_inv]
  field_simp [hp0]

/-- Uniform square mass of the enriched mass-normalized readouts. -/
def canonicalEnrichedGpreMassReadoutSquareMass
    (M : ℕ) (s : ℂ) : ℝ :=
  ∑' p : Nat.Primes,
    (primeMassGreenBulkCutoffProfile (3 * M) s p) ^ 2

/-- The square mass is nonnegative. -/
theorem canonicalEnrichedGpreMassReadoutSquareMass_nonneg
    (M : ℕ) (s : ℂ) :
    0 ≤ canonicalEnrichedGpreMassReadoutSquareMass M s := by
  unfold canonicalEnrichedGpreMassReadoutSquareMass
  exact tsum_nonneg fun p => sq_nonneg _

/-- Every finite mass-readout atlas is bounded by the complete square mass. -/
theorem sum_finiteEnrichedNativeGpreMassReadout_sq_le_squareMass
    (M : ℕ) {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (S : Finset Nat.Primes) :
    (∑ p ∈ S,
      (finiteEnrichedNativeGpreMassLogJetGreenBulkReadout
        p M 1 (fun _ => 1) s) ^ 2) ≤
      canonicalEnrichedGpreMassReadoutSquareMass M s := by
  have hsum := summable_primeMassGreenBulkCutoffProfile_sq (3 * M) hs
  have hle := hsum.sum_le_tsum S (fun p hp => sq_nonneg _)
  simpa [canonicalEnrichedGpreMassReadoutSquareMass,
    finiteEnrichedNativeGpreMassLogJetGreenBulkReadout_eq
      (kappa := (1 : ℂ)) (omega := fun _ => (1 : ℂ))] using hle

/-- Global weighted Bessel inequality.  The right-hand coefficient norm carries
exactly one factor of `p`, corresponding to the missing half-amplitude gain. -/
theorem canonicalEnrichedGpreLogJetGreenScalarTest_sq_le_primeWeighted
    (M : ℕ) {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (S : Finset Nat.Primes) (coeff : Nat.Primes → ℝ) :
    (canonicalEnrichedGpreLogJetGreenScalarTest M s S coeff) ^ 2 ≤
      canonicalEnrichedGpreMassReadoutSquareMass M s *
        ∑ p ∈ S, (p : ℝ) * (coeff p) ^ 2 := by
  let lifted : Nat.Primes → ℝ := fun p =>
    (primeCarryAmplitudeRatio p)⁻¹ * coeff p
  let massReadout : Nat.Primes → ℝ := fun p =>
    finiteEnrichedNativeGpreMassLogJetGreenBulkReadout
      p M 1 (fun _ => 1) s
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq S lifted massReadout
  have hmass :
      (∑ p ∈ S, (massReadout p) ^ 2) ≤
        canonicalEnrichedGpreMassReadoutSquareMass M s := by
    exact sum_finiteEnrichedNativeGpreMassReadout_sq_le_squareMass M hs S
  have hlifted0 : 0 ≤ ∑ p ∈ S, (lifted p) ^ 2 :=
    Finset.sum_nonneg fun p hp => sq_nonneg _
  rw [canonicalEnrichedGpreLogJetGreenScalarTest_eq_massTest]
  unfold canonicalEnrichedGpreMassLogJetGreenScalarTest
  change (∑ p ∈ S, lifted p * massReadout p) ^ 2 ≤ _
  calc
    (∑ p ∈ S, lifted p * massReadout p) ^ 2 ≤
        (∑ p ∈ S, lifted p ^ 2) *
          ∑ p ∈ S, massReadout p ^ 2 := hCS
    _ ≤ (∑ p ∈ S, lifted p ^ 2) *
          canonicalEnrichedGpreMassReadoutSquareMass M s :=
      mul_le_mul_of_nonneg_left hmass hlifted0
    _ = canonicalEnrichedGpreMassReadoutSquareMass M s *
          ∑ p ∈ S, (p : ℝ) * coeff p ^ 2 := by
      rw [mul_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      exact inv_primeCarryAmplitudeRatio_mul_sq p (coeff p)

/-- If an atlas is contained below a real prime bound `P`, the same estimate is
an ordinary Bessel bound with constant growing linearly in `P`. -/
theorem canonicalEnrichedGpreLogJetGreenScalarTest_sq_le_of_prime_le
    (M : ℕ) {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (S : Finset Nat.Primes) (coeff : Nat.Primes → ℝ)
    (P : ℝ) (hP : ∀ p ∈ S, (p : ℝ) ≤ P) :
    (canonicalEnrichedGpreLogJetGreenScalarTest M s S coeff) ^ 2 ≤
      (canonicalEnrichedGpreMassReadoutSquareMass M s * P) *
        ∑ p ∈ S, (coeff p) ^ 2 := by
  have hweighted :
      (∑ p ∈ S, (p : ℝ) * coeff p ^ 2) ≤
        P * ∑ p ∈ S, coeff p ^ 2 := by
    calc
      (∑ p ∈ S, (p : ℝ) * coeff p ^ 2) ≤
          ∑ p ∈ S, P * coeff p ^ 2 := by
        gcongr with p hp
        exact hP p hp
      _ = P * ∑ p ∈ S, coeff p ^ 2 := by
        rw [Finset.mul_sum]
  have hmass0 := canonicalEnrichedGpreMassReadoutSquareMass_nonneg M s
  calc
    (canonicalEnrichedGpreLogJetGreenScalarTest M s S coeff) ^ 2 ≤
        canonicalEnrichedGpreMassReadoutSquareMass M s *
          ∑ p ∈ S, (p : ℝ) * coeff p ^ 2 :=
      canonicalEnrichedGpreLogJetGreenScalarTest_sq_le_primeWeighted
        M hs S coeff
    _ ≤ canonicalEnrichedGpreMassReadoutSquareMass M s *
          (P * ∑ p ∈ S, coeff p ^ 2) :=
      mul_le_mul_of_nonneg_left hweighted hmass0
    _ = (canonicalEnrichedGpreMassReadoutSquareMass M s * P) *
          ∑ p ∈ S, coeff p ^ 2 := by ring

/-- Named formulation of the precise missing gain: at a Genuine zero the
prime-weighted estimate should improve to an unweighted estimate with a
constant independent of the finite atlas. -/
def GenuineZeroProvidesPrimeHalfAmplitudeSmoothing : Prop :=
  ∀ {s : ℂ}, genuineContinuation s = 0 →
    s ∈ genuineCriticalStrip →
      CanonicalEnrichedGpreLogJetGreenScalarTestsBounded 1 s

/-- The half-amplitude smoothing formulation is the already isolated strong
scalar obligation, now with the universal weighted estimate available on its
left. -/
theorem genuineZeroProvidesPrimeHalfAmplitudeSmoothing_iff_strongNonvanishing :
    GenuineZeroProvidesPrimeHalfAmplitudeSmoothing ↔
      GenuineStrongNonvanishingInStrip :=
  genuineZerosSatisfyCanonicalEnrichedPrimeBesselTests_iff_strongNonvanishing

end

end CPFormal.Analytic.Cp
