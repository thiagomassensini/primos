import CPFormal.Carry.C2OddCorePushforward
import CPFormal.Analytic.CpSeededTfvdSameSBoundary
import Mathlib.Data.Finset.NatDivisors
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Tactic.LinearCombination

/-!
# Concrete C2 odd-core pushforward in the TFVD port

This module specializes the abstract connected C2 cell to the actual finite
odd-core pushforward.  For two positive cores `p,q`, set

`K_T(p,q) = a_T(pq) - a_T(p) a_T(q)`.

The independently proved dyadic correction

`a_(8M)(r) = 1/2 + (1/2) a_(4M)(r)`

at each of `r = p,q,pq` gives the exact connected Richardson identity

`2 K_(8M)(p,q) - K_(4M)(p,q)
  = (1/2) epsilon_(M,p) epsilon_(M,q)`,

where `epsilon_(M,r) = 1 - a_(4M)(r)`.

The four concrete masses `(a_T(p),a_T(pq);1,a_T(q))` are then encoded in the
existing enriched TFVD port.  After decoding, the visible cell is exactly
`K_T`, while the dormant cell is zero.

The final section keeps only odd support, normalizes the unit coefficient by
`a_T(1)=1`, defines the finite logarithmic extraction by Dirichlet inversion,
and proves its exact coefficient at a squarefree odd semiprime.  This is
finite arithmetic only.  No Genuine zero, Green closure, or off-critical
nonvanishing bridge is assumed.
-/

open scoped BigOperators Pointwise

namespace CPFormal.Analytic.Cp

open ArithmeticFunction

noncomputable section

/-! ## The actual connected cumulant -/

/-- The rational connected cumulant of the concrete odd-core masses. -/
def c2OddCoreConnectedCumulant
    (cutoff p q : ℕ) : ℚ :=
  CPFormal.Carry.C2.oddCoreTruncatedMass cutoff (p * q) -
    CPFormal.Carry.C2.oddCoreTruncatedMass cutoff p *
      CPFormal.Carry.C2.oddCoreTruncatedMass cutoff q

/-- The same connected cumulant in the real carrier used by the TFVD port. -/
def c2OddCoreConnectedCumulantReal
    (cutoff p q : ℕ) : ℝ :=
  (c2OddCoreConnectedCumulant cutoff p q : ℝ)

/-- Concrete mass defect at the lower dyadic cutoff `4M`. -/
def c2OddCoreFourScaleDefect (M m : ℕ) : ℚ :=
  1 - CPFormal.Carry.C2.oddCoreTruncatedMass (4 * M) m

/-- Real form of the concrete mass defect. -/
def c2OddCoreFourScaleDefectReal (M m : ℕ) : ℝ :=
  (c2OddCoreFourScaleDefect M m : ℝ)

/--
Actual connected Richardson identity at the three cores `p`, `q`, and `pq`.
The hypotheses state exactly where the concrete dyadic correction is used.
-/
theorem c2OddCoreConnectedCumulant_richardson_exact
    {M p q : ℕ}
    (hp : 0 < p) (hq : 0 < q)
    (hpM : p ≤ M) (hqM : q ≤ M) (hpqM : p * q ≤ M) :
    2 * c2OddCoreConnectedCumulant (8 * M) p q -
        c2OddCoreConnectedCumulant (4 * M) p q =
      (1 / 2 : ℚ) *
        c2OddCoreFourScaleDefect M p *
          c2OddCoreFourScaleDefect M q := by
  unfold c2OddCoreConnectedCumulant c2OddCoreFourScaleDefect
  rw [
    CPFormal.Carry.C2.oddCoreTruncatedMass_eight_mul_eq
      (Nat.mul_pos hp hq) hpqM,
    CPFormal.Carry.C2.oddCoreTruncatedMass_eight_mul_eq hp hpM,
    CPFormal.Carry.C2.oddCoreTruncatedMass_eight_mul_eq hq hqM]
  ring

/-- Real-cast form of the exact connected Richardson identity. -/
theorem c2OddCoreConnectedCumulantReal_richardson_exact
    {M p q : ℕ}
    (hp : 0 < p) (hq : 0 < q)
    (hpM : p ≤ M) (hqM : q ≤ M) (hpqM : p * q ≤ M) :
    2 * c2OddCoreConnectedCumulantReal (8 * M) p q -
        c2OddCoreConnectedCumulantReal (4 * M) p q =
      (1 / 2 : ℝ) *
        c2OddCoreFourScaleDefectReal M p *
          c2OddCoreFourScaleDefectReal M q := by
  unfold c2OddCoreConnectedCumulantReal
    c2OddCoreFourScaleDefectReal
  have h := congrArg (fun x : ℚ ↦ (x : ℝ))
    (c2OddCoreConnectedCumulant_richardson_exact
      hp hq hpM hqM hpqM)
  norm_num at h
  exact h

/-! ## Exact specialization of the enriched TFVD port -/

/-- Concrete value port carrying the masses at `p` and `pq`. -/
def c2OddCoreMassTfvdValueCoordinate
    (block : ℕ) (kappa omega : ℂ)
    (cutoff p q : ℕ) :
    EnrichedAngularTfvdCoordinate :=
  enrichedAngularTfvdEncode block kappa omega
    ((CPFormal.Carry.C2.oddCoreTruncatedMass cutoff p : ℚ) : ℂ)
    ((CPFormal.Carry.C2.oddCoreTruncatedMass cutoff (p * q) : ℚ) : ℂ)
    0

/-- Concrete companion port carrying the unit seed and the mass at `q`. -/
def c2OddCoreMassTfvdJetCoordinate
    (block : ℕ) (kappa omega : ℂ)
    (cutoff q : ℕ) :
    EnrichedAngularTfvdCoordinate :=
  enrichedAngularTfvdEncode block kappa omega
    1
    ((CPFormal.Carry.C2.oddCoreTruncatedMass cutoff q : ℚ) : ℂ)
    0

/--
Decoding the two concrete mass ports preserves the connected cumulant in the
visible cell and leaves the dormant cell identically zero.
-/
theorem c2OddCoreMassTfvdBoundaryCells_eq
    (block : ℕ) {kappa omega : ℂ}
    (hkappa : kappa ≠ 0) (homega : omega ≠ 0)
    (cutoff p q : ℕ) :
    enrichedTfvdSameSBoundaryCells kappa omega
        (c2OddCoreMassTfvdValueCoordinate
          block kappa omega cutoff p q)
        (c2OddCoreMassTfvdJetCoordinate
          block kappa omega cutoff q) =
      {
        visibleCell :=
          ((c2OddCoreConnectedCumulant cutoff p q : ℚ) : ℂ)
        dormantCell := 0
      } := by
  unfold c2OddCoreMassTfvdValueCoordinate
    c2OddCoreMassTfvdJetCoordinate
  rw [enrichedTfvdSameSBoundaryCells_encode block hkappa homega]
  apply TfvdSameSBoundaryCells.ext
  · unfold c2OddCoreConnectedCumulant sameSEdgeBoundaryWedge
    push_cast
    ring
  · unfold sameSEdgeBoundaryWedge
    ring

/-- Scalar readout of the concrete visible cell. -/
theorem c2OddCoreMassTfvdBoundaryCells_visible_eq
    (block : ℕ) {kappa omega : ℂ}
    (hkappa : kappa ≠ 0) (homega : omega ≠ 0)
    (cutoff p q : ℕ) :
    (enrichedTfvdSameSBoundaryCells kappa omega
        (c2OddCoreMassTfvdValueCoordinate
          block kappa omega cutoff p q)
        (c2OddCoreMassTfvdJetCoordinate
          block kappa omega cutoff q)).visibleCell =
      ((c2OddCoreConnectedCumulant cutoff p q : ℚ) : ℂ) := by
  rw [c2OddCoreMassTfvdBoundaryCells_eq
    block hkappa homega cutoff p q]

/-- Scalar readout of the concrete dormant cell. -/
theorem c2OddCoreMassTfvdBoundaryCells_dormant_eq_zero
    (block : ℕ) {kappa omega : ℂ}
    (hkappa : kappa ≠ 0) (homega : omega ≠ 0)
    (cutoff p q : ℕ) :
    (enrichedTfvdSameSBoundaryCells kappa omega
        (c2OddCoreMassTfvdValueCoordinate
          block kappa omega cutoff p q)
        (c2OddCoreMassTfvdJetCoordinate
          block kappa omega cutoff q)).dormantCell = 0 := by
  rw [c2OddCoreMassTfvdBoundaryCells_eq
    block hkappa homega cutoff p q]

/--
Richardson applied after TFVD encoding returns exactly the product of the two
concrete lower-scale defects.
-/
theorem c2OddCoreMassTfvdBoundaryCells_richardson_exact
    (block : ℕ) {kappa omega : ℂ}
    (hkappa : kappa ≠ 0) (homega : omega ≠ 0)
    {M p q : ℕ}
    (hp : 0 < p) (hq : 0 < q)
    (hpM : p ≤ M) (hqM : q ≤ M) (hpqM : p * q ≤ M) :
    2 *
        (enrichedTfvdSameSBoundaryCells kappa omega
          (c2OddCoreMassTfvdValueCoordinate
            block kappa omega (8 * M) p q)
          (c2OddCoreMassTfvdJetCoordinate
            block kappa omega (8 * M) q)).visibleCell -
      (enrichedTfvdSameSBoundaryCells kappa omega
        (c2OddCoreMassTfvdValueCoordinate
          block kappa omega (4 * M) p q)
        (c2OddCoreMassTfvdJetCoordinate
          block kappa omega (4 * M) q)).visibleCell =
      (((1 / 2 : ℚ) *
        c2OddCoreFourScaleDefect M p *
          c2OddCoreFourScaleDefect M q : ℚ) : ℂ) := by
  rw [
    c2OddCoreMassTfvdBoundaryCells_visible_eq
      block hkappa homega (8 * M) p q,
    c2OddCoreMassTfvdBoundaryCells_visible_eq
      block hkappa homega (4 * M) p q]
  exact_mod_cast
    c2OddCoreConnectedCumulant_richardson_exact
      hp hq hpM hqM hpqM

/-! ## Unit-normalized logarithmic extraction -/

/--
The finite odd-core mass as an arithmetic function.  The seed is normalized
explicitly by `a_T(1)=1`, positive odd non-unit indices use the concrete mass,
and even indices vanish.  Thus this is the seed-normalized odd channel, not
the raw truncated coefficient function at `n = 1`.
-/
def c2OddCoreNormalizedMassArithmetic
    (cutoff : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if n = 0 then 0 else
      if n = 1 then 1 else if Odd n then
        (CPFormal.Carry.C2.oddCoreTruncatedMass cutoff n : ℝ) else 0,
    by simp⟩

@[simp] theorem c2OddCoreNormalizedMassArithmetic_one
    (cutoff : ℕ) :
    c2OddCoreNormalizedMassArithmetic cutoff 1 = 1 := by
  simp [c2OddCoreNormalizedMassArithmetic]

theorem c2OddCoreNormalizedMassArithmetic_eq_mass
    (cutoff : ℕ) {n : ℕ}
    (hn0 : n ≠ 0) (hn1 : n ≠ 1) (hnodd : Odd n) :
    c2OddCoreNormalizedMassArithmetic cutoff n =
      (CPFormal.Carry.C2.oddCoreTruncatedMass cutoff n : ℝ) := by
  simp [c2OddCoreNormalizedMassArithmetic, hn0, hn1, hnodd]

/-- Coefficientwise logarithmic dressing `a_T(n) log n`. -/
def c2OddCoreWeightedLogMassArithmetic
    (cutoff : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n ↦
      c2OddCoreNormalizedMassArithmetic cutoff n *
        Real.log (n : ℝ),
    by simp⟩

/-- Canonical invertibility witness for the normalized unit coefficient. -/
@[reducible] noncomputable def c2OddCoreNormalizedMassOneInvertible
    (cutoff : ℕ) :
    Invertible (c2OddCoreNormalizedMassArithmetic cutoff 1) := by
  rw [c2OddCoreNormalizedMassArithmetic_one]
  exact invertibleOne

/--
Finite logarithmic extraction: the coefficient function `b_T` satisfying
`b_T * a_T = a_T log` under Dirichlet convolution.
-/
noncomputable def c2OddCoreLogCoefficientArithmetic
    (cutoff : ℕ) : ArithmeticFunction ℝ :=
  c2OddCoreWeightedLogMassArithmetic cutoff *
    ArithmeticFunction.dirichletInverse
      (c2OddCoreNormalizedMassArithmetic cutoff)
      (c2OddCoreNormalizedMassOneInvertible cutoff)

/-- The defining convolution identity of the finite logarithmic extraction. -/
theorem c2OddCoreLogCoefficientArithmetic_mul_mass
    (cutoff : ℕ) :
    c2OddCoreLogCoefficientArithmetic cutoff *
        c2OddCoreNormalizedMassArithmetic cutoff =
      c2OddCoreWeightedLogMassArithmetic cutoff := by
  unfold c2OddCoreLogCoefficientArithmetic
  rw [mul_assoc,
    ArithmeticFunction.dirichletInverse_mul_self
      (c2OddCoreNormalizedMassArithmetic cutoff)
      (c2OddCoreNormalizedMassOneInvertible cutoff),
    mul_one]

/-- Unbundled notation for the finite coefficient `b_T(n)`. -/
def c2OddCoreLogCoefficient (cutoff n : ℕ) : ℝ :=
  c2OddCoreLogCoefficientArithmetic cutoff n

/-- A prime coefficient is `a_T(p) log p`. -/
theorem c2OddCoreLogCoefficient_prime
    (cutoff : ℕ) {p : ℕ}
    (hp : Nat.Prime p) (hpodd : Odd p) :
    c2OddCoreLogCoefficient cutoff p =
      (CPFormal.Carry.C2.oddCoreTruncatedMass cutoff p : ℝ) *
        Real.log (p : ℝ) := by
  have hconv := congrArg
    (fun f : ArithmeticFunction ℝ ↦ f p)
    (c2OddCoreLogCoefficientArithmetic_mul_mass cutoff)
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal
      (fun i j ↦
        c2OddCoreLogCoefficientArithmetic cutoff i *
          c2OddCoreNormalizedMassArithmetic cutoff j),
    hp.divisors] at hconv
  have hbOne :
      c2OddCoreLogCoefficientArithmetic cutoff 1 = 0 := by
    have hOne := congrArg
      (fun f : ArithmeticFunction ℝ ↦ f 1)
      (c2OddCoreLogCoefficientArithmetic_mul_mass cutoff)
    simp [c2OddCoreWeightedLogMassArithmetic] at hOne
    exact hOne
  simpa [c2OddCoreLogCoefficient,
    c2OddCoreWeightedLogMassArithmetic,
    c2OddCoreNormalizedMassArithmetic_eq_mass
      cutoff hp.ne_zero hp.ne_one hpodd,
    hbOne, hp.pos] using hconv

/--
At a squarefree semiprime, the finite logarithmic coefficient is exactly the
logarithm times the concrete connected cumulant.
-/
theorem c2OddCoreLogCoefficient_distinct_primes
    (cutoff : ℕ) {p q : ℕ}
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q) (hpq : p ≠ q) :
    c2OddCoreLogCoefficient cutoff (p * q) =
      Real.log ((p * q : ℕ) : ℝ) *
        c2OddCoreConnectedCumulantReal cutoff p q := by
  have hbOne :
      c2OddCoreLogCoefficientArithmetic cutoff 1 = 0 := by
    have hOne := congrArg
      (fun f : ArithmeticFunction ℝ ↦ f 1)
      (c2OddCoreLogCoefficientArithmetic_mul_mass cutoff)
    simp [c2OddCoreWeightedLogMassArithmetic] at hOne
    exact hOne
  have hbp := c2OddCoreLogCoefficient_prime cutoff hp hpodd
  have hbq := c2OddCoreLogCoefficient_prime cutoff hq hqodd
  have hdivisors :
      (p * q).divisors = {1, p, q, p * q} := by
    rw [Nat.divisors_mul]
    ext d
    simp only [Finset.mem_mul, hp.divisors, hq.divisors,
      Finset.mem_insert, Finset.mem_singleton]
    aesop
  have hconv := congrArg
    (fun f : ArithmeticFunction ℝ ↦ f (p * q))
    (c2OddCoreLogCoefficientArithmetic_mul_mass cutoff)
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal
      (fun i j ↦
        c2OddCoreLogCoefficientArithmetic cutoff i *
          c2OddCoreNormalizedMassArithmetic cutoff j),
    hdivisors] at hconv
  have hpqnep : p * q ≠ p := by
    intro heq
    have heq' : p * q = p * 1 := by simpa using heq
    exact hq.ne_one (Nat.eq_of_mul_eq_mul_left hp.pos heq')
  have hpqneq : p * q ≠ q := by
    intro heq
    have heq' : q * p = q * 1 := by
      simpa [Nat.mul_comm] using heq
    exact hp.ne_one (Nat.eq_of_mul_eq_mul_left hq.pos heq')
  simp [hpqnep.symm, hpqneq.symm, hpq,
    hbOne, hp.pos, hq.pos] at hconv
  change
    c2OddCoreLogCoefficient cutoff p *
          c2OddCoreNormalizedMassArithmetic cutoff q +
        (c2OddCoreLogCoefficient cutoff q *
            c2OddCoreNormalizedMassArithmetic cutoff p +
          c2OddCoreLogCoefficient cutoff (p * q)) =
      c2OddCoreNormalizedMassArithmetic cutoff (p * q) *
        Real.log ((p * q : ℕ) : ℝ) at hconv
  have hpqneone : p * q ≠ 1 := by
    have hfour : 4 ≤ p * q := by
      have hmul := Nat.mul_le_mul hp.two_le hq.two_le
      norm_num at hmul ⊢
      exact hmul
    omega
  rw [
    c2OddCoreNormalizedMassArithmetic_eq_mass
      cutoff hq.ne_zero hq.ne_one hqodd,
    c2OddCoreNormalizedMassArithmetic_eq_mass
      cutoff hp.ne_zero hp.ne_one hpodd,
    c2OddCoreNormalizedMassArithmetic_eq_mass
      cutoff (Nat.mul_ne_zero hp.ne_zero hq.ne_zero) hpqneone
        (hpodd.mul hqodd),
    hbp, hbq] at hconv
  have hlog :
      Real.log (((p * q : ℕ) : ℝ)) =
        Real.log (p : ℝ) + Real.log (q : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul]
    · exact_mod_cast hp.ne_zero
    · exact_mod_cast hq.ne_zero
  rw [hlog] at hconv
  rw [hlog]
  unfold c2OddCoreConnectedCumulantReal
    c2OddCoreConnectedCumulant
  push_cast
  linear_combination hconv

/--
At the two exact dyadic cutoffs, the semiprime logarithmic coefficient has
the same connected Richardson defect, dressed only by `log(pq)`.
-/
theorem c2OddCoreLogCoefficient_distinct_primes_richardson_exact
    {M p q : ℕ}
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q) (hpq : p ≠ q)
    (hpM : p ≤ M) (hqM : q ≤ M) (hpqM : p * q ≤ M) :
    2 * c2OddCoreLogCoefficient (8 * M) (p * q) -
        c2OddCoreLogCoefficient (4 * M) (p * q) =
      Real.log ((p * q : ℕ) : ℝ) *
        ((1 / 2 : ℝ) *
          c2OddCoreFourScaleDefectReal M p *
            c2OddCoreFourScaleDefectReal M q) := by
  rw [
    c2OddCoreLogCoefficient_distinct_primes
      (8 * M) hp hpodd hq hqodd hpq,
    c2OddCoreLogCoefficient_distinct_primes
      (4 * M) hp hpodd hq hqodd hpq]
  have hConnected :=
    c2OddCoreConnectedCumulantReal_richardson_exact
      hp.pos hq.pos hpM hqM hpqM
  calc
    2 *
          (Real.log ((p * q : ℕ) : ℝ) *
            c2OddCoreConnectedCumulantReal (8 * M) p q) -
        Real.log ((p * q : ℕ) : ℝ) *
          c2OddCoreConnectedCumulantReal (4 * M) p q =
      Real.log ((p * q : ℕ) : ℝ) *
        (2 * c2OddCoreConnectedCumulantReal (8 * M) p q -
          c2OddCoreConnectedCumulantReal (4 * M) p q) := by
            ring
    _ = Real.log ((p * q : ℕ) : ℝ) *
        ((1 / 2 : ℝ) *
          c2OddCoreFourScaleDefectReal M p *
            c2OddCoreFourScaleDefectReal M q) := by
      rw [hConnected]

/--
The semiprime coefficient times its Dirichlet vertex is the connected
cumulant times the existing log-Dirichlet vertex.
-/
theorem c2OddCoreLogCoefficient_mul_positiveDirichletValue
    (cutoff : ℕ) {p q : ℕ}
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q) (hpq : p ≠ q)
    (s : ℂ) :
    (c2OddCoreLogCoefficient cutoff (p * q) : ℂ) *
        positiveDirichletValue s (p * q - 1) =
      (c2OddCoreConnectedCumulantReal cutoff p q : ℂ) *
        positiveLogDirichletValue s (p * q - 1) := by
  have hpqsub : p * q - 1 + 1 = p * q := by
    have hpqpos := Nat.mul_pos hp.pos hq.pos
    omega
  rw [c2OddCoreLogCoefficient_distinct_primes
    cutoff hp hpodd hq hqodd hpq]
  unfold positiveLogDirichletValue
  rw [hpqsub]
  push_cast
  ring

/--
Every log-Dirichlet vertex is the finite telescoping sum of the consecutive
log-jet gradients from the normalized seed.  This places the semiprime
monomial in the linear span of the native log-jet edge field, without yet
identifying the weighted canonical camera port.
-/
theorem positiveLogDirichletValue_eq_sum_range_gradient
    (s : ℂ) (N : ℕ) :
    positiveLogDirichletValue s N =
      ∑ n ∈ Finset.range N, positiveLogDirichletGradient s n := by
  have htelescope :=
    sum_range_forwardDifference
      (fun n ↦ positiveLogDirichletValue s n) 0 N
  simp only [Nat.zero_add] at htelescope
  rw [positiveLogDirichletValue_zero, sub_zero] at htelescope
  simpa [positiveLogDirichletGradient] using htelescope.symm

/--
Dirichlet-dressed form of the exact semiprime Richardson identity.  The
ordinary Dirichlet vertex on the extracted coefficients becomes the existing
log-Dirichlet vertex on the connected defect.
-/
theorem
    c2OddCoreLogCoefficient_distinct_primes_richardson_mul_positiveDirichletValue
    {M p q : ℕ}
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q) (hpq : p ≠ q)
    (hpM : p ≤ M) (hqM : q ≤ M) (hpqM : p * q ≤ M)
    (s : ℂ) :
    2 *
        ((c2OddCoreLogCoefficient (8 * M) (p * q) : ℂ) *
          positiveDirichletValue s (p * q - 1)) -
      ((c2OddCoreLogCoefficient (4 * M) (p * q) : ℂ) *
        positiveDirichletValue s (p * q - 1)) =
      (((1 / 2 : ℝ) *
        c2OddCoreFourScaleDefectReal M p *
          c2OddCoreFourScaleDefectReal M q : ℝ) : ℂ) *
        positiveLogDirichletValue s (p * q - 1) := by
  have hpqsub : p * q - 1 + 1 = p * q := by
    have hpqpos := Nat.mul_pos hp.pos hq.pos
    omega
  rw [
    c2OddCoreLogCoefficient_distinct_primes
      (8 * M) hp hpodd hq hqodd hpq,
    c2OddCoreLogCoefficient_distinct_primes
      (4 * M) hp hpodd hq hqodd hpq]
  have hConnected :=
    c2OddCoreConnectedCumulantReal_richardson_exact
      hp.pos hq.pos hpM hqM hpqM
  calc
    2 *
          (((Real.log ((p * q : ℕ) : ℝ) *
              c2OddCoreConnectedCumulantReal (8 * M) p q : ℝ) : ℂ) *
            positiveDirichletValue s (p * q - 1)) -
        (((Real.log ((p * q : ℕ) : ℝ) *
            c2OddCoreConnectedCumulantReal (4 * M) p q : ℝ) : ℂ) *
          positiveDirichletValue s (p * q - 1)) =
      ((Real.log ((p * q : ℕ) : ℝ) : ℝ) : ℂ) *
          (((2 * c2OddCoreConnectedCumulantReal (8 * M) p q -
            c2OddCoreConnectedCumulantReal (4 * M) p q : ℝ) : ℂ)) *
        positiveDirichletValue s (p * q - 1) := by
      push_cast
      ring
    _ = ((Real.log ((p * q : ℕ) : ℝ) : ℝ) : ℂ) *
          ((((1 / 2 : ℝ) *
            c2OddCoreFourScaleDefectReal M p *
              c2OddCoreFourScaleDefectReal M q : ℝ) : ℂ)) *
        positiveDirichletValue s (p * q - 1) := by
      rw [hConnected]
    _ = (((1 / 2 : ℝ) *
          c2OddCoreFourScaleDefectReal M p *
            c2OddCoreFourScaleDefectReal M q : ℝ) : ℂ) *
        positiveLogDirichletValue s (p * q - 1) := by
      unfold positiveLogDirichletValue
      rw [hpqsub]
      push_cast
      ring

/--
The same dressed Richardson cell written entirely in the native consecutive
log-jet gradient field.  What remains open is the weighted camera/provenance
intertwiner, not the passage from a semiprime vertex to consecutive edges.
-/
theorem
    c2OddCoreLogCoefficient_distinct_primes_richardson_eq_sum_logJetGradients
    {M p q : ℕ}
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q) (hpq : p ≠ q)
    (hpM : p ≤ M) (hqM : q ≤ M) (hpqM : p * q ≤ M)
    (s : ℂ) :
    2 *
        ((c2OddCoreLogCoefficient (8 * M) (p * q) : ℂ) *
          positiveDirichletValue s (p * q - 1)) -
      ((c2OddCoreLogCoefficient (4 * M) (p * q) : ℂ) *
        positiveDirichletValue s (p * q - 1)) =
      (((1 / 2 : ℝ) *
        c2OddCoreFourScaleDefectReal M p *
          c2OddCoreFourScaleDefectReal M q : ℝ) : ℂ) *
        ∑ n ∈ Finset.range (p * q - 1),
          positiveLogDirichletGradient s n := by
  rw [
    c2OddCoreLogCoefficient_distinct_primes_richardson_mul_positiveDirichletValue
      hp hpodd hq hqodd hpq hpM hqM hpqM s,
    positiveLogDirichletValue_eq_sum_range_gradient]

end

end CPFormal.Analytic.Cp
