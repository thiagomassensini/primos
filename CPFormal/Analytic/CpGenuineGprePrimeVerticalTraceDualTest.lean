import CPFormal.Analytic.CpGenuineGprePrimeVerticalTraceAtlas

/-!
# Dual scalar tests for the enriched prime vertical trace atlas

A uniform Hilbert bound on the prime-camera atlas is equivalent to one scalar
Cauchy--Schwarz estimate for every finitely supported family of prime weights.
This is the useful form for a future `G_pre` proof: instead of constructing the
amplitude-upgraded vector directly, it is enough to bound every weighted sum
of its provenance-preserving log-jet coordinates by the `ell^2` norm of the
weights.

The converse is proved by testing against the readout vector itself.  Hence no
Riesz-representation theorem or hidden compactness assumption is used.
-/

open scoped BigOperators ENNReal

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Scalar test of the enriched log-jet Green atlas against arbitrary real
weights on a finite set of prime cameras. -/
def canonicalEnrichedGpreLogJetGreenScalarTest
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes)
    (coeff : Nat.Primes → ℝ) : ℝ :=
  ∑ p ∈ S,
    coeff p * finiteEnrichedNativeGpreLogJetGreenBulkReadout
      p M 1 (fun _ => 1) s

/-- Uniform dual estimate for all finite prime atlases and all coefficient
families. -/
def CanonicalEnrichedGpreLogJetGreenScalarTestsBounded
    (M : ℕ) (s : ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (S : Finset Nat.Primes) (coeff : Nat.Primes → ℝ),
      (canonicalEnrichedGpreLogJetGreenScalarTest M s S coeff) ^ 2 ≤
        C * ∑ p ∈ S, (coeff p) ^ 2

/-- A uniform Hilbert atlas bound gives all scalar test bounds by finite
Cauchy--Schwarz. -/
theorem canonicalEnrichedGpreLogJetGreenAtlasesBounded_to_scalarTests
    (M : ℕ) (s : ℂ)
    (hbounded : CanonicalEnrichedGpreLogJetGreenAtlasesBounded M s) :
    CanonicalEnrichedGpreLogJetGreenScalarTestsBounded M s := by
  rcases hbounded with ⟨C, hC⟩
  have hC0 : 0 ≤ C := by
    simpa [canonicalEnrichedGpreLogJetGreenAtlasState] using
      hC (∅ : Finset Nat.Primes)
  refine ⟨C, hC0, ?_⟩
  intro S coeff
  let readout : Nat.Primes → ℝ := fun p =>
    finiteEnrichedNativeGpreLogJetGreenBulkReadout
      p M 1 (fun _ => 1) s
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq S coeff readout
  have hreadout :
      (∑ p ∈ S, (readout p) ^ 2) ≤ C := by
    have hnorm := hC S
    rw [canonicalEnrichedGpreLogJetGreenAtlasState_norm_sq] at hnorm
    exact hnorm
  have hcoeff0 : 0 ≤ ∑ p ∈ S, (coeff p) ^ 2 :=
    Finset.sum_nonneg fun p hp => sq_nonneg _
  unfold canonicalEnrichedGpreLogJetGreenScalarTest
  change (∑ p ∈ S, coeff p * readout p) ^ 2 ≤
    C * ∑ p ∈ S, coeff p ^ 2
  calc
    (∑ p ∈ S, coeff p * readout p) ^ 2 ≤
        (∑ p ∈ S, coeff p ^ 2) * ∑ p ∈ S, readout p ^ 2 := hCS
    _ ≤ (∑ p ∈ S, coeff p ^ 2) * C :=
      mul_le_mul_of_nonneg_left hreadout hcoeff0
    _ = C * ∑ p ∈ S, coeff p ^ 2 := by ring

/-- Conversely, testing against the readout vector itself recovers its squared
Hilbert norm, so the scalar test estimate already bounds every atlas. -/
theorem canonicalEnrichedGpreLogJetGreenScalarTests_to_atlasesBounded
    (M : ℕ) (s : ℂ)
    (htests : CanonicalEnrichedGpreLogJetGreenScalarTestsBounded M s) :
    CanonicalEnrichedGpreLogJetGreenAtlasesBounded M s := by
  rcases htests with ⟨C, hC0, htest⟩
  refine ⟨C, ?_⟩
  intro S
  let readout : Nat.Primes → ℝ := fun p =>
    finiteEnrichedNativeGpreLogJetGreenBulkReadout
      p M 1 (fun _ => 1) s
  let Q : ℝ := ∑ p ∈ S, (readout p) ^ 2
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    exact Finset.sum_nonneg fun p hp => sq_nonneg _
  have hself := htest S readout
  have htestEq :
      canonicalEnrichedGpreLogJetGreenScalarTest M s S readout = Q := by
    unfold canonicalEnrichedGpreLogJetGreenScalarTest
    dsimp [Q, readout]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  have hQQ : Q ^ 2 ≤ C * Q := by
    rw [htestEq] at hself
    simpa [Q] using hself
  have hQle : Q ≤ C := by
    nlinarith
  rw [canonicalEnrichedGpreLogJetGreenAtlasState_norm_sq]
  simpa [Q, readout] using hQle

/-- Exact duality between the vector-atlas formulation and scalar weighted
provenance tests. -/
theorem canonicalEnrichedGpreLogJetGreenScalarTestsBounded_iff_atlasesBounded
    (M : ℕ) (s : ℂ) :
    CanonicalEnrichedGpreLogJetGreenScalarTestsBounded M s ↔
      CanonicalEnrichedGpreLogJetGreenAtlasesBounded M s := by
  constructor
  · exact canonicalEnrichedGpreLogJetGreenScalarTests_to_atlasesBounded M s
  · exact canonicalEnrichedGpreLogJetGreenAtlasesBounded_to_scalarTests M s

/-- At a nonempty cutoff, the scalar Bessel-test estimate selects exactly the
half-abscissa. -/
theorem canonicalEnrichedGpreLogJetGreenScalarTestsBounded_iff
    (M : ℕ) (hM : 0 < M) {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    CanonicalEnrichedGpreLogJetGreenScalarTestsBounded M s ↔
      criticalDisplacement s.re = 0 := by
  rw [canonicalEnrichedGpreLogJetGreenScalarTestsBounded_iff_atlasesBounded,
    canonicalEnrichedGpreLogJetGreenAtlasesBounded_iff M hM hs]

/-- The remaining global assertion in dual scalar-test form. -/
def GenuineZerosSatisfyCanonicalEnrichedPrimeBesselTests : Prop :=
  ∀ {s : ℂ}, genuineContinuation s = 0 →
    s ∈ genuineCriticalStrip →
      CanonicalEnrichedGpreLogJetGreenScalarTestsBounded 1 s

/-- Scope guard: a uniform Bessel estimate for every finite weighted prime
readout at every Genuine zero has exactly the strength of strong
nonvanishing. -/
theorem genuineZerosSatisfyCanonicalEnrichedPrimeBesselTests_iff_strongNonvanishing :
    GenuineZerosSatisfyCanonicalEnrichedPrimeBesselTests ↔
      GenuineStrongNonvanishingInStrip := by
  constructor
  · intro htests s hs hoff hzero
    have hcritical :=
      (canonicalEnrichedGpreLogJetGreenScalarTestsBounded_iff
        1 (by norm_num) hs).1 (htests hzero hs)
    apply hoff
    unfold criticalDisplacement at hcritical
    linarith
  · intro hstrong s hzero hs
    apply
      (canonicalEnrichedGpreLogJetGreenScalarTestsBounded_iff
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
