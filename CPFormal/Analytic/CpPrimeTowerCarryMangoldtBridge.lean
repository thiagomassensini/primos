import CPFormal.Carry.PositionalDecomposition
import CPFormal.Carry.CpBranchWeight
import CPFormal.Analytic.CpNativeCarryMobiusLogDerivativeGuardrail
import CPFormal.Analytic.CpGenuineNativeRealBoundaryCrosswalk

/-!
# Prime-tower carry / von Mangoldt bridge

This module records the exact structural bridge between three descriptions of
the same prime-tower data:

* positional carry depth in the prime camera `p`;
* the vertical logarithmic charge `k * log p`;
* the atomic von Mangoldt readout, which contributes one copy of `log p` at
  every level `p, p^2, ..., p^k`.

The point is deliberately narrower than an identification of the full carry
operator with the classical explicit formula.  The bridge proves exact local
and accumulated identities on prime towers, then places them next to the
already kernel-checked reconstruction

`sum_{d | n} vonMangoldt(d) = log n`

and the already kernel-checked state crosswalk from the primitive real carry
sample to the Dirichlet monomial `n^(-s)`.

No claim is made here that von Mangoldt contains the full all-bases Green /
endpoint / bulk geometry, nor that the logarithmic derivative causes the
native carry zero confinement.
-/

open scoped BigOperators

namespace CPFormal.Analytic.Cp

open CPFormal.Carry.Positional
open CPFormal.Carry.Cp

noncomputable section

/-- Logarithmic vertical charge read by camera `p` at the maximal positional
carry depth of `n`. -/
def primeVerticalScale (p n : ℕ) : ℝ :=
  (positionalDepth p n : ℝ) * Real.log p

/-- In the prime camera `p`, the pure tower point `p^k` has positional depth
exactly `k`. -/
@[simp] theorem positionalDepth_prime_pow
    {p k : ℕ} (hp : Nat.Prime p) :
    positionalDepth p (p ^ k) = k := by
  unfold positionalDepth
  exact multiplicity_eq_of_emultiplicity_eq_some hp.emultiplicity_pow_self

/-- The vertical scale of the pure tower point `p^k` is exactly `k * log p`. -/
@[simp] theorem primeVerticalScale_prime_pow
    {p k : ℕ} (hp : Nat.Prime p) :
    primeVerticalScale p (p ^ k) = (k : ℝ) * Real.log p := by
  simp [primeVerticalScale, hp]

/-- A nonzero prime-power level carries one von Mangoldt atom `log p`,
independently of the level number. -/
theorem vonMangoldt_prime_pow
    {p k : ℕ} (hp : Nat.Prime p) (hk : k ≠ 0) :
    ArithmeticFunction.vonMangoldt (p ^ k) = Real.log p := by
  rw [ArithmeticFunction.vonMangoldt_apply_pow hk]
  exact ArithmeticFunction.vonMangoldt_apply_prime hp

/-- At a pure prime-tower point, the full vertical charge is the depth times
the single von Mangoldt atom seen at that level. -/
theorem primeVerticalScale_eq_depth_mul_vonMangoldt
    {p k : ℕ} (hp : Nat.Prime p) (hk : k ≠ 0) :
    primeVerticalScale p (p ^ k) =
      (k : ℝ) * ArithmeticFunction.vonMangoldt (p ^ k) := by
  rw [primeVerticalScale_prime_pow hp, vonMangoldt_prime_pow hp hk]

/-- Accumulating the von Mangoldt atoms along the first `k` positive levels of
the prime tower recovers the complete vertical charge of the top point `p^k`.
This is the precise sense in which von Mangoldt is an atomic vertical readout:
it stores `log p` per level, while the carry coordinate stores the accumulated
depth `k`. -/
theorem sum_vonMangoldt_primeTower_eq_verticalScale
    {p k : ℕ} (hp : Nat.Prime p) :
    (∑ j ∈ Finset.range k,
        ArithmeticFunction.vonMangoldt (p ^ (j + 1))) =
      primeVerticalScale p (p ^ k) := by
  rw [primeVerticalScale_prime_pow hp]
  simp [vonMangoldt_prime_pow hp]

/-- The same atomic accumulation identity at the actual positional depth of an
arbitrary positive integer in a fixed prime camera.  Mixed integers need not be
prime powers themselves; the camera still has a well-defined vertical depth,
and that depth is exactly the number of prime-tower atoms accumulated here. -/
theorem sum_vonMangoldt_primeTower_to_positionalDepth_eq_verticalScale
    {p n : ℕ} (hp : Nat.Prime p) :
    (∑ j ∈ Finset.range (positionalDepth p n),
        ArithmeticFunction.vonMangoldt (p ^ (j + 1))) =
      primeVerticalScale p n := by
  unfold primeVerticalScale
  simp [vonMangoldt_prime_pow hp]

/-- On a nonzero integer, prime-camera positional depth is exactly the exponent
of the same prime in the unique prime factorization. -/
theorem positionalDepth_eq_factorization_of_prime
    {p n : ℕ} (hp : Nat.Prime p) (hn : n ≠ 0) :
    positionalDepth p n = n.factorization p := by
  unfold positionalDepth
  exact Nat.multiplicity_eq_factorization hp hn

/-- The vertical charge in a prime camera is the factorization exponent times
`log p`.  This identifies the positional coordinate with the standard
factorization coordinate without changing either definition. -/
theorem primeVerticalScale_eq_factorizationCharge
    {p n : ℕ} (hp : Nat.Prime p) (hn : n ≠ 0) :
    primeVerticalScale p n =
      (n.factorization p : ℝ) * Real.log p := by
  rw [primeVerticalScale, positionalDepth_eq_factorization_of_prime hp hn]

/-- Summing the vertical charges of all active prime cameras reconstructs the
integer logarithm.  Composite cameras are not needed in this ledger because
the prime factorization already gives a nonredundant set of vertical axes. -/
theorem sum_primeVerticalScale_primeFactors_eq_log
    {n : ℕ} (hn : n ≠ 0) :
    (∑ p ∈ n.primeFactors, primeVerticalScale p n) = Real.log n := by
  have hprodNat :
      (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
    calc
      (∏ p ∈ n.primeFactors, p ^ n.factorization p) =
          n.factorization.prod (fun p k => p ^ k) := by
        symm
        exact Nat.prod_factorization_eq_prod_primeFactors (fun p k => p ^ k)
      _ = n := Nat.prod_factorization_pow_eq_self hn
  have hprodReal :
      (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) = (n : ℝ) := by
    exact_mod_cast hprodNat
  have hlogProd :
      Real.log (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) =
        ∑ p ∈ n.primeFactors,
          Real.log ((p : ℝ) ^ n.factorization p) := by
    apply Real.log_prod
    intro p hpMem
    have hp : Nat.Prime p := Nat.prime_of_mem_primeFactors hpMem
    exact pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  calc
    (∑ p ∈ n.primeFactors, primeVerticalScale p n) =
        ∑ p ∈ n.primeFactors,
          (n.factorization p : ℝ) * Real.log p := by
      apply Finset.sum_congr rfl
      intro p hpMem
      exact primeVerticalScale_eq_factorizationCharge
        (Nat.prime_of_mem_primeFactors hpMem) hn
    _ = ∑ p ∈ n.primeFactors,
          Real.log ((p : ℝ) ^ n.factorization p) := by
      apply Finset.sum_congr rfl
      intro p _hpMem
      rw [Real.log_pow]
    _ = Real.log (∏ p ∈ n.primeFactors,
          (p : ℝ) ^ n.factorization p) := hlogProd.symm
    _ = Real.log n := by rw [hprodReal]

/-- Globally, summing the prime-power atoms among the divisors of `n`
reconstructs the integer logarithmic field exactly. -/
theorem carryPrimeTowerAtoms_divisorSum_eq_integerLog (n : ℕ) :
    (∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d) =
      Real.log n :=
  primePowerSignal_divisorSum_eq_integerLog n

/-- The global prime-camera vertical ledger and the classical divisor-sum
von Mangoldt ledger are exactly the same scalar quantity. -/
theorem sum_primeVerticalScale_eq_divisorMangoldtSum
    {n : ℕ} (hn : n ≠ 0) :
    (∑ p ∈ n.primeFactors, primeVerticalScale p n) =
      ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d := by
  rw [sum_primeVerticalScale_primeFactors_eq_log hn,
    carryPrimeTowerAtoms_divisorSum_eq_integerLog]

/-- Fully expanded atomic ledger.  For every nonzero integer, accumulate one
von Mangoldt atom at every positive level reached in every active prime camera.
The result is exactly the usual divisor-sum von Mangoldt reconstruction.
This is the all-prime-cameras version of the local tower identity above. -/
theorem allPrimeCameraAtomicLedger_eq_divisorMangoldtLedger
    {n : ℕ} (hn : n ≠ 0) :
    (∑ p ∈ n.primeFactors,
        ∑ j ∈ Finset.range (positionalDepth p n),
          ArithmeticFunction.vonMangoldt (p ^ (j + 1))) =
      ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d := by
  calc
    (∑ p ∈ n.primeFactors,
        ∑ j ∈ Finset.range (positionalDepth p n),
          ArithmeticFunction.vonMangoldt (p ^ (j + 1))) =
        ∑ p ∈ n.primeFactors, primeVerticalScale p n := by
      apply Finset.sum_congr rfl
      intro p hpMem
      exact sum_vonMangoldt_primeTower_to_positionalDepth_eq_verticalScale
        (Nat.prime_of_mem_primeFactors hpMem)
    _ = ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d :=
      sum_primeVerticalScale_eq_divisorMangoldtSum hn

/-- The primitive real carry state at a pure prime-tower point packages to the
same Dirichlet monomial as every other positive integer.  This places the
prime-tower depth/readout identities above directly upstream of the already
proved real-to-Dirichlet state crosswalk. -/
theorem primePower_nativeCarrySample_packages_to_dirichletTerm
    (sigma time : ℝ) {p k : ℕ} (hp : Nat.Prime p) :
    nativeCarryRealPlaneComplexPackaging
        (nativeCarryRealPlaneSampleAt sigma time (p ^ k : ℤ)) =
      dirichletTerm (nativeCarryRealPlaneParameter sigma time) (p ^ k : ℤ) := by
  apply nativeCarryRealPlaneComplexPackaging_sampleAt_eq_dirichletTerm
  exact_mod_cast pow_pos hp.pos k

/-- Kernel-level bridge checkpoint: the same prime tower simultaneously has
carry depth `k`, vertical charge `k log p`, one von Mangoldt atom `log p` at
its top level (for positive depth), and the standard primitive Dirichlet state.
The conjunction intentionally adds no implication from the arithmetic readout
to native zero confinement. -/
theorem primeTowerCarryMangoldt_checkpoint
    (sigma time : ℝ) {p k : ℕ} (hp : Nat.Prime p) (hk : k ≠ 0) :
    positionalDepth p (p ^ k) = k ∧
      primeVerticalScale p (p ^ k) = (k : ℝ) * Real.log p ∧
      ArithmeticFunction.vonMangoldt (p ^ k) = Real.log p ∧
      nativeCarryRealPlaneComplexPackaging
          (nativeCarryRealPlaneSampleAt sigma time (p ^ k : ℤ)) =
        dirichletTerm (nativeCarryRealPlaneParameter sigma time) (p ^ k : ℤ) := by
  exact ⟨positionalDepth_prime_pow hp,
    primeVerticalScale_prime_pow hp,
    vonMangoldt_prime_pow hp hk,
    primePower_nativeCarrySample_packages_to_dirichletTerm sigma time hp⟩

end

end CPFormal.Analytic.Cp
