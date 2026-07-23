import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Truncated pushforward of the C2 odd branch

This file isolates the elementary finite arithmetic behind the odd-core
pushforward.  For a positive core `m`, the two points at depth `k ≥ 2` are

`2 ^ k * m - 1` and `2 ^ k * m + 1`,

and each carries the rational weight `2⁻ᵏ`.  The definitions below compute the
actual last admissible depth in each branch and sum precisely those weights.

The main theorem is the exact dyadic correction

`2 * a_(8M)(m) - a_(4M)(m) = 1`

for `0 < m ≤ M`.  Its proof comes from the concrete cutoff depths and finite
geometric sums.  No halving law is assumed.

Oddness is not needed for this finite arithmetic identity.  In the C2
application, one specializes `m` to an odd core.  This module makes no claim
about analytic continuation, Genuine, Green, or zeros.
-/

open scoped BigOperators

namespace CPFormal.Carry.C2

/-- Canonical rational mass assigned to one branch point at depth `k`. -/
def dyadicBranchWeight (k : ℕ) : ℚ :=
  ((2 : ℚ)⁻¹) ^ k

/--
Last depth allowed by the branch point `2 ^ k * m - 1 ≤ cutoff`.

For positive `m` and a nonzero quotient, division by `m` followed by the
base-two natural logarithm is exactly the largest exponent satisfying
`2 ^ k * m ≤ cutoff + 1`.  The value `0` is also the empty-branch sentinel
when the quotient vanishes; the admissibility theorem below remains exact
because branch depths start at `k = 2`.
-/
def oddCoreMinusDepth (cutoff m : ℕ) : ℕ :=
  Nat.log 2 ((cutoff + 1) / m)

/--
Last depth allowed by the branch point `2 ^ k * m + 1 ≤ cutoff`.

For positive `m` and a nonzero quotient, this is the largest exponent
satisfying `2 ^ k * m ≤ cutoff - 1`.  As above, `0` is the empty-branch
sentinel when the quotient vanishes.
-/
def oddCorePlusDepth (cutoff m : ℕ) : ℕ :=
  Nat.log 2 ((cutoff - 1) / m)

/-- Finite mass in one branch, summing every depth from `2` through `K`. -/
def oddCoreBranchMass (K : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 2 K, dyadicBranchWeight k

/--
Concrete truncated C2 pushforward above the core `m`: the sum of the minus
and plus branches with their independently computed cutoff depths.
-/
def oddCoreTruncatedMass (cutoff m : ℕ) : ℚ :=
  oddCoreBranchMass (oddCoreMinusDepth cutoff m) +
    oddCoreBranchMass (oddCorePlusDepth cutoff m)

/-- The minus-depth interval is exactly the finite set of admissible levels. -/
theorem mem_Icc_two_oddCoreMinusDepth_iff
    {cutoff m k : ℕ} (hm : 0 < m) :
    k ∈ Finset.Icc 2 (oddCoreMinusDepth cutoff m) ↔
      2 ≤ k ∧ 2 ^ k * m - 1 ≤ cutoff := by
  rw [Finset.mem_Icc]
  unfold oddCoreMinusDepth
  constructor
  · rintro ⟨hk, hlog⟩
    have hquot : (cutoff + 1) / m ≠ 0 := by
      intro hzero
      simp [hzero] at hlog
      omega
    have hpow : 2 ^ k ≤ (cutoff + 1) / m :=
      Nat.pow_le_of_le_log hquot hlog
    have hmul : 2 ^ k * m ≤ cutoff + 1 :=
      (Nat.le_div_iff_mul_le hm).1 hpow
    constructor
    · exact hk
    · have hpowPos : 0 < 2 ^ k * m := by positivity
      omega
  · rintro ⟨hk, hcutoff⟩
    constructor
    · exact hk
    · apply Nat.le_log_of_pow_le (by omega)
      apply (Nat.le_div_iff_mul_le hm).2
      have hpowPos : 0 < 2 ^ k * m := by positivity
      omega

/-- The plus-depth interval is exactly the finite set of admissible levels. -/
theorem mem_Icc_two_oddCorePlusDepth_iff
    {cutoff m k : ℕ} (hm : 0 < m) :
    k ∈ Finset.Icc 2 (oddCorePlusDepth cutoff m) ↔
      2 ≤ k ∧ 2 ^ k * m + 1 ≤ cutoff := by
  rw [Finset.mem_Icc]
  unfold oddCorePlusDepth
  constructor
  · rintro ⟨hk, hlog⟩
    have hquot : (cutoff - 1) / m ≠ 0 := by
      intro hzero
      simp [hzero] at hlog
      omega
    have hpow : 2 ^ k ≤ (cutoff - 1) / m :=
      (Nat.le_log_iff_pow_le (by omega) hquot).1 hlog
    have hmul : 2 ^ k * m ≤ cutoff - 1 :=
      (Nat.le_div_iff_mul_le hm).1 hpow
    constructor
    · exact hk
    · have hpowPos : 0 < 2 ^ k * m := by positivity
      omega
  · rintro ⟨hk, hcutoff⟩
    constructor
    · exact hk
    · apply Nat.le_log_of_pow_le (by omega)
      apply (Nat.le_div_iff_mul_le hm).2
      have hpowPos : 0 < 2 ^ k * m := by positivity
      omega

/-- At cutoff `4M`, the minus branch has reached depth at least `2`. -/
theorem two_le_oddCoreMinusDepth_four_mul
    {M m : ℕ} (hm : 0 < m) (hmM : m ≤ M) :
    2 ≤ oddCoreMinusDepth (4 * M) m := by
  apply Nat.le_log_of_pow_le (by omega)
  apply (Nat.le_div_iff_mul_le hm).2
  norm_num
  omega

/-- At cutoff `4M`, the plus branch has reached depth at least `1`. -/
theorem one_le_oddCorePlusDepth_four_mul
    {M m : ℕ} (hm : 0 < m) (hmM : m ≤ M) :
    1 ≤ oddCorePlusDepth (4 * M) m := by
  apply Nat.le_log_of_pow_le (by omega)
  apply (Nat.le_div_iff_mul_le hm).2
  norm_num
  omega

/--
Doubling the cutoff from `4M` to `8M` adds exactly one minus-branch depth.
-/
theorem oddCoreMinusDepth_eight_mul_eq_four_mul_add_one
    {M m : ℕ} (hm : 0 < m) (hmM : m ≤ M) :
    oddCoreMinusDepth (8 * M) m =
      oddCoreMinusDepth (4 * M) m + 1 := by
  let K := oddCoreMinusDepth (4 * M) m
  have hquot4 : (4 * M + 1) / m ≠ 0 := by
    apply Nat.ne_of_gt
    exact Nat.div_pos (by omega) hm
  have hKpow : 2 ^ K ≤ (4 * M + 1) / m := by
    exact Nat.pow_log_le_self 2 hquot4
  have hKpowMul : 2 ^ K * m ≤ 4 * M + 1 := by
    exact (Nat.le_div_iff_mul_le hm).mp hKpow
  have hKtwo : 2 ≤ K := by
    simpa [K] using two_le_oddCoreMinusDepth_four_mul hm hmM
  have hKpos : 0 < K := by
    omega
  have hKpowEven : Even (2 ^ K * m) := by
    exact Even.mul_right ((Nat.even_pow' hKpos.ne').2 even_two) m
  have hKpowMulTight : 2 ^ K * m ≤ 4 * M := by
    rcases hKpowEven with ⟨r, hr⟩
    omega
  have hloNat : 2 ^ (K + 1) * m ≤ 8 * M + 1 := by
    have hdouble : 2 * (2 ^ K * m) ≤ 8 * M + 1 := by
      omega
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hdouble
  have hlo : 2 ^ (K + 1) ≤ (8 * M + 1) / m :=
    (Nat.le_div_iff_mul_le hm).2 hloNat
  have hupper4 : (4 * M + 1) / m < 2 ^ (K + 1) := by
    exact Nat.lt_pow_succ_log_self (by omega) _
  have hupper4Nat : 4 * M + 1 < 2 ^ (K + 1) * m := by
    exact (Nat.div_lt_iff_lt_mul hm).mp hupper4
  have hupper8Nat : 8 * M + 1 < 2 ^ ((K + 1) + 1) * m := by
    have hdouble : 8 * M + 1 < 2 * (2 ^ (K + 1) * m) := by
      omega
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hdouble
  have hupper : (8 * M + 1) / m < 2 ^ ((K + 1) + 1) := by
    exact (Nat.div_lt_iff_lt_mul hm).2 hupper8Nat
  unfold oddCoreMinusDepth at K ⊢
  exact Nat.log_eq_of_pow_le_of_lt_pow hlo hupper

/--
Doubling the cutoff from `4M` to `8M` adds exactly one plus-branch depth.
-/
theorem oddCorePlusDepth_eight_mul_eq_four_mul_add_one
    {M m : ℕ} (hm : 0 < m) (hmM : m ≤ M) :
    oddCorePlusDepth (8 * M) m =
      oddCorePlusDepth (4 * M) m + 1 := by
  let K := oddCorePlusDepth (4 * M) m
  have hquot4 : (4 * M - 1) / m ≠ 0 := by
    apply Nat.ne_of_gt
    exact Nat.div_pos (by omega) hm
  have hKpow : 2 ^ K ≤ (4 * M - 1) / m := by
    exact Nat.pow_log_le_self 2 hquot4
  have hKpowMul : 2 ^ K * m ≤ 4 * M - 1 := by
    exact (Nat.le_div_iff_mul_le hm).mp hKpow
  have hloNat : 2 ^ (K + 1) * m ≤ 8 * M - 1 := by
    have hdouble : 2 * (2 ^ K * m) ≤ 8 * M - 1 := by
      omega
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hdouble
  have hlo : 2 ^ (K + 1) ≤ (8 * M - 1) / m :=
    (Nat.le_div_iff_mul_le hm).2 hloNat
  have hupper4 : (4 * M - 1) / m < 2 ^ (K + 1) := by
    exact Nat.lt_pow_succ_log_self (by omega) _
  have hupper4Nat : 4 * M - 1 < 2 ^ (K + 1) * m := by
    exact (Nat.div_lt_iff_lt_mul hm).mp hupper4
  have hupper8Nat : 8 * M - 1 < 2 ^ ((K + 1) + 1) * m := by
    have hdouble : 8 * M - 1 < 2 * (2 ^ (K + 1) * m) := by
      omega
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hdouble
  have hupper : (8 * M - 1) / m < 2 ^ ((K + 1) + 1) := by
    exact (Nat.div_lt_iff_lt_mul hm).2 hupper8Nat
  unfold oddCorePlusDepth at K ⊢
  exact Nat.log_eq_of_pow_le_of_lt_pow hlo hupper

/--
The finite geometric branch mass obeys its concrete one-step identity.

The proof reindexes the actual depths `2, ..., K` to `3, ..., K + 1`;
it does not assume a recurrence for the mass.
-/
theorem oddCoreBranchMass_succ
    {K : ℕ} (hK : 1 ≤ K) :
    oddCoreBranchMass (K + 1) =
      (1 / 4 : ℚ) + (1 / 2 : ℚ) * oddCoreBranchMass K := by
  have hsplit :
      Finset.Icc 2 (K + 1) =
        insert 2 (Finset.Icc 3 (K + 1)) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have himage :
      (Finset.Icc 2 K).image (fun k : ℕ => k + 1) =
        Finset.Icc 3 (K + 1) := by
    ext k
    simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨j, ⟨hj2, hjK⟩, rfl⟩
      omega
    · intro hk
      refine ⟨k - 1, ?_, by omega⟩
      omega
  rw [oddCoreBranchMass, hsplit, Finset.sum_insert (by simp)]
  rw [← himage, Finset.sum_image]
  · rw [show dyadicBranchWeight 2 = (1 / 4 : ℚ) by
      norm_num [dyadicBranchWeight]]
    simp_rw [dyadicBranchWeight, pow_succ]
    rw [← Finset.sum_mul]
    simp only [oddCoreBranchMass, dyadicBranchWeight]
    ring
  · intro a _ b _ hab
    exact Nat.add_right_cancel hab

/-- Both concrete branch masses at `8M` are obtained by one finite shift. -/
theorem oddCoreTruncatedMass_eight_mul_eq
    {M m : ℕ} (hm : 0 < m) (hmM : m ≤ M) :
    oddCoreTruncatedMass (8 * M) m =
      (1 / 2 : ℚ) +
        (1 / 2 : ℚ) * oddCoreTruncatedMass (4 * M) m := by
  have hminus : 1 ≤ oddCoreMinusDepth (4 * M) m := by
    have htwo := two_le_oddCoreMinusDepth_four_mul hm hmM
    omega
  rw [oddCoreTruncatedMass,
    oddCoreMinusDepth_eight_mul_eq_four_mul_add_one hm hmM,
    oddCorePlusDepth_eight_mul_eq_four_mul_add_one hm hmM,
    oddCoreBranchMass_succ hminus,
    oddCoreBranchMass_succ
      (one_le_oddCorePlusDepth_four_mul hm hmM),
    oddCoreTruncatedMass]
  ring

/--
Exact finite Richardson correction for the concrete C2 odd-core pushforward.

For every positive core `m ≤ M` (in particular every positive odd core),
`2 * a_(8M)(m) - a_(4M)(m)` is exactly the limiting mass `1`.
-/
theorem oddCoreTruncatedMass_richardson_exact
    {M m : ℕ} (hm : 0 < m) (hmM : m ≤ M) :
    2 * oddCoreTruncatedMass (8 * M) m -
        oddCoreTruncatedMass (4 * M) m =
      1 := by
  rw [oddCoreTruncatedMass_eight_mul_eq hm hmM]
  ring

end CPFormal.Carry.C2
