import CPFormal.Analytic.CpGenuineKernelPrimeState
import CPFormal.Analytic.CpGenuinePrimeCarryDefectUniformBound

/-!
# Contractive lift from the native `G_pre` tower to the common carry state

The native tower already supplies one fixed Hilbert state before prime-camera
readout.  This module bundles all first-time prime moments into the global
centered-carry Hilbert space without defining the source state from the target
camera coefficients.

For `x : NativeGpreTowerHilbert`, the `p`-coordinate is

`<h_(p,1), x> • psi_p^vee`,

where `h_(p,1)` is the native material tower profile and `psi_p^vee` is the
canonical dual centered-carry axis.  The resulting state reads back every
prime moment exactly.

The arithmetic profile ledger gives the strict atlas-independent estimate

`‖T x‖^2 ≤ (11 / 12) ‖x‖^2`.

The constant is obtained without a prime-number asymptotic:

* the camera `2` contributes at most `13 / 24`;
* every other prime is odd, and the odd-camera tail contributes at most
  `3 / 8`;
* `13 / 24 + 3 / 8 = 11 / 12`.

No Genuine zero, critical localization, spectral continuation, or global
moment-realization hypothesis enters the contraction itself.  The final
crosswalk says only that, if a native source state has the required moments,
then this contractive lift is the common realization used by the finite-atlas
Pythagorean ledger.
-/

open scoped BigOperators ENNReal

namespace CPFormal.Analytic.Cp

noncomputable section

/-! ## A telescoping budget for the prime index -/

/--
Majorant assigned to the injective prime index: index zero is reserved for
the prime `2`; positive index `k` represents the possible odd value `2k+1`.
-/
def nativeGprePrimeCarryContractionMajorant (k : ℕ) : ℝ :=
  if k = 0 then 13 / 24
  else
    (3 / 8) *
      (1 / (k : ℝ) - 1 / ((k : ℝ) + 1))

theorem nativeGprePrimeCarryContractionMajorant_nonneg (k : ℕ) :
    0 ≤ nativeGprePrimeCarryContractionMajorant k := by
  by_cases hk : k = 0
  · norm_num [nativeGprePrimeCarryContractionMajorant, hk]
  · have hkpos : (0 : ℝ) < k := by
      exact_mod_cast Nat.pos_of_ne_zero hk
    have hkle : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
    have hdiff :
        0 ≤ 1 / (k : ℝ) - 1 / ((k : ℝ) + 1) :=
      sub_nonneg.mpr (one_div_le_one_div_of_le hkpos hkle)
    rw [nativeGprePrimeCarryContractionMajorant, if_neg hk]
    exact mul_nonneg (by norm_num) hdiff

theorem nativeGprePrimeCarryContractionMajorant_summable :
    Summable nativeGprePrimeCarryContractionMajorant := by
  have htail :
      Summable
        (fun n : ℕ =>
          nativeGprePrimeCarryContractionMajorant (n + 1)) := by
    have hbase := nativeGpreTelescopingSquareMajorant_hasSum.summable
    have hscaled :=
      hbase.mul_left (3 / 8 : ℝ)
    refine hscaled.congr ?_
    intro n
    have hn : n + 1 ≠ 0 := by omega
    rw [nativeGprePrimeCarryContractionMajorant, if_neg hn,
      nativeGpreTelescopingSquareMajorant]
    push_cast
    ring
  exact (summable_nat_add_iff 1).1 htail

theorem nativeGprePrimeCarryContractionMajorant_tsum :
    (∑' k : ℕ, nativeGprePrimeCarryContractionMajorant k) =
      (11 / 12 : ℝ) := by
  have hsum := nativeGprePrimeCarryContractionMajorant_summable
  have hsplit := hsum.sum_add_tsum_nat_add 1
  have htail :
      (∑' n : ℕ,
          nativeGprePrimeCarryContractionMajorant (n + 1)) =
        (3 / 8 : ℝ) := by
    have hbase := nativeGpreTelescopingSquareMajorant_hasSum
    have hscaled := hbase.mul_left (3 / 8 : ℝ)
    have htailHasSum :
        HasSum
          (fun n : ℕ =>
            nativeGprePrimeCarryContractionMajorant (n + 1))
          (3 / 8 : ℝ) := by
      refine hscaled.congr ?_
      intro n
      have hn : n + 1 ≠ 0 := by omega
      rw [nativeGprePrimeCarryContractionMajorant, if_neg hn,
        nativeGpreTelescopingSquareMajorant]
      push_cast
      ring
    exact htailHasSum.tsum_eq
  rw [Finset.sum_range_one, htail] at hsplit
  norm_num [nativeGprePrimeCarryContractionMajorant] at hsplit ⊢
  linarith

/-! ## Sharp enough material profile estimates -/

/-- Exact geometric resolvent bound at the first native time. -/
theorem nativeGpreTowerProfileVector_one_norm_sq_le_resolvent
    (p : ℕ) (hp : 2 ≤ p) :
    ‖nativeGpreTowerProfileVector p 1‖ ^ 2 ≤
      (((p : ℝ) ^ 2 - 1)⁻¹) := by
  let q : ℝ := ((p : ℝ) ^ 2)⁻¹
  let f : ℕ → ℝ := fun j => nativeUnitMassTowerProfile p 1 j ^ 2
  have hq0 : 0 ≤ q := by positivity
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hpSq : (4 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
  have hq4 : q ≤ (1 / 4 : ℝ) := by
    dsimp [q]
    rw [one_div]
    exact
      (inv_le_inv₀
        (a := (p : ℝ) ^ 2) (b := (4 : ℝ))
        (by positivity) (by norm_num)).2 hpSq
  have hq1 : q < 1 := lt_of_le_of_lt hq4 (by norm_num)
  have hf : Summable f :=
    nativeUnitMassTowerProfile_sq_summable_of_pos p 1 hp (by norm_num)
  have hgeom : Summable (fun j : ℕ => q ^ j) :=
    summable_geometric_of_lt_one hq0 hq1
  have hfshift : (∑' j : ℕ, f j) = ∑' j : ℕ, f (j + 1) := by
    have h := hf.sum_add_tsum_nat_add 1
    rw [Finset.sum_range_one] at h
    calc
      (∑' j : ℕ, f j) = f 0 + ∑' j : ℕ, f (j + 1) := h.symm
      _ = ∑' j : ℕ, f (j + 1) := by
        simp [f, nativeUnitMassTowerProfile]
  have hle :
      (∑' j : ℕ, f (j + 1)) ≤ ∑' j : ℕ, q ^ (j + 1) := by
    exact Summable.tsum_le_tsum
      (fun j => by
        simpa [q] using
          nativeUnitMassTowerProfile_sq_le_geometric p (j + 1) 1)
      ((summable_nat_add_iff 1).2 hf)
      ((summable_nat_add_iff 1).2 hgeom)
  have hgeomSum :
      (∑' j : ℕ, q ^ (j + 1)) = q * (1 - q)⁻¹ := by
    simp_rw [pow_succ']
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hpSqNe : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  rw [nativeGpreTowerProfileVector_norm_sq, hfshift]
  calc
    (∑' j : ℕ, f (j + 1)) ≤ ∑' j : ℕ, q ^ (j + 1) := hle
    _ = q * (1 - q)⁻¹ := hgeomSum
    _ = (((p : ℝ) ^ 2 - 1)⁻¹) := by
      dsimp [q]
      field_simp [hp0, hpSqNe]

/-- The first native profile of camera `2` has the sharper bound `13/48`. -/
theorem nativeGpreTowerProfileVector_two_one_norm_sq_le :
    ‖nativeGpreTowerProfileVector 2 1‖ ^ 2 ≤ (13 / 48 : ℝ) := by
  let f : ℕ → ℝ := fun j => nativeUnitMassTowerProfile 2 1 j ^ 2
  have hf : Summable f := nativeUnitMassTowerProfile_sq_summable 2 1
  have hsplit := hf.sum_add_tsum_nat_add 2
  have hhead : (∑ j ∈ Finset.range 2, f j) = (1 / 4 : ℝ) := by
    norm_num [Finset.sum_range_succ, f, nativeUnitMassTowerProfile]
  have hpoint :
      ∀ j : ℕ, f (j + 2) ≤
        (1 / 4 : ℝ) * (1 / 4 : ℝ) ^ (j + 2) := by
    intro j
    have hj : j + 2 ≠ 0 := by omega
    have hden : (4 : ℝ) ≤ ((j + 2 : ℕ) : ℝ) ^ 2 := by
      push_cast
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
      nlinarith [sq_nonneg (j : ℝ)]
    have hinv :
        ((((j + 2 : ℕ) : ℝ) ^ 2)⁻¹) ≤ (1 / 4 : ℝ) := by
      rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num]
      exact (inv_le_inv₀ (by positivity) (by norm_num)).2 hden
    dsimp [f]
    rw [nativeUnitMassTowerProfile, if_neg hj, div_pow,
      nativeUnitMassTowerProfile_pow_identity]
    norm_num
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) _)
  have hmajorSummable :
      Summable
        (fun j : ℕ =>
          (1 / 4 : ℝ) * (1 / 4 : ℝ) ^ (j + 2)) := by
    have hgeom :
        Summable (fun j : ℕ => (1 / 4 : ℝ) ^ j) :=
      summable_geometric_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num : (1 / 4 : ℝ) < 1)
    exact ((summable_nat_add_iff 2).2 hgeom).mul_left (1 / 4 : ℝ)
  have htail :
      (∑' j : ℕ, f (j + 2)) ≤ (1 / 48 : ℝ) := by
    calc
      (∑' j : ℕ, f (j + 2)) ≤
          ∑' j : ℕ,
            (1 / 4 : ℝ) * (1 / 4 : ℝ) ^ (j + 2) :=
        Summable.tsum_le_tsum hpoint
          ((summable_nat_add_iff 2).2 hf) hmajorSummable
      _ = (1 / 48 : ℝ) := by
        rw [tsum_mul_left]
        simp_rw [pow_add]
        rw [tsum_mul_right,
          tsum_geometric_of_lt_one
            (by norm_num : (0 : ℝ) ≤ 1 / 4)
            (by norm_num : (1 / 4 : ℝ) < 1)]
        norm_num
  rw [hhead] at hsplit
  rw [nativeGpreTowerProfileVector_norm_sq]
  linarith

/-! ## The injective prime budget -/

/-- Prime `2` receives index zero; an odd prime `2k+1` receives index `k`. -/
def nativeGprePrimeCarryContractionIndex (p : Nat.Primes) : ℕ :=
  if (p : ℕ) = 2 then 0 else ((p : ℕ) - 1) / 2

theorem nativeGprePrimeCarryContractionIndex_injective :
    Function.Injective nativeGprePrimeCarryContractionIndex := by
  intro p q hpq
  apply Nat.Primes.coe_nat_injective
  rcases p.property.eq_two_or_odd with hpTwo | hpOdd
  · rcases q.property.eq_two_or_odd with hqTwo | hqOdd
    · exact hpTwo.trans hqTwo.symm
    · have hqOdd' : Odd (q : ℕ) := Nat.odd_iff.mpr hqOdd
      rcases hqOdd' with ⟨k, hk⟩
      have hqNe : (q : ℕ) ≠ 2 := by omega
      have hkpos : 0 < k := by
        have hqTwoLe := q.property.two_le
        omega
      simp [nativeGprePrimeCarryContractionIndex, hpTwo, hqNe] at hpq
      omega
  · have hpOdd' : Odd (p : ℕ) := Nat.odd_iff.mpr hpOdd
    rcases hpOdd' with ⟨kp, hkp⟩
    have hpNe : (p : ℕ) ≠ 2 := by omega
    rcases q.property.eq_two_or_odd with hqTwo | hqOdd
    · have hkpos : 0 < kp := by
        have hpTwoLe := p.property.two_le
        omega
      simp [nativeGprePrimeCarryContractionIndex, hpNe, hqTwo] at hpq
      omega
    · have hqOdd' : Odd (q : ℕ) := Nat.odd_iff.mpr hqOdd
      rcases hqOdd' with ⟨kq, hkq⟩
      have hqNe : (q : ℕ) ≠ 2 := by omega
      simp [nativeGprePrimeCarryContractionIndex, hpNe, hqNe] at hpq
      omega

/-! ## The global contractive lift -/

/-- One local dual-axis coordinate produced by a native tower state. -/
def nativeGprePrimeCarryDefectCoordinate
    (x : NativeGpreTowerHilbert) (p : Nat.Primes) :
    PrimeCarryResidueHilbert p :=
  inner ℝ (nativeGpreTowerProfileVector (p : ℕ) 1) x •
    primeCriticalCenteredCarryDualAxis p

theorem nativeGprePrimeCarryDefectCoordinate_norm_sq
    (x : NativeGpreTowerHilbert) (p : Nat.Primes) :
    ‖nativeGprePrimeCarryDefectCoordinate x p‖ ^ 2 =
      ‖primeCriticalCenteredCarryDualAxis p‖ ^ 2 *
        (inner ℝ (nativeGpreTowerProfileVector (p : ℕ) 1) x) ^ 2 := by
  unfold nativeGprePrimeCarryDefectCoordinate
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- Material profile cost of one prime camera before applying a source state. -/
def nativeGprePrimeCarryProfileCost (p : Nat.Primes) : ℝ :=
  ‖primeCriticalCenteredCarryDualAxis p‖ ^ 2 *
    ‖nativeGpreTowerProfileVector (p : ℕ) 1‖ ^ 2

theorem nativeGprePrimeCarryProfileCost_nonneg (p : Nat.Primes) :
    0 ≤ nativeGprePrimeCarryProfileCost p := by
  exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem nativeGprePrimeCarryProfileCost_summable :
    Summable nativeGprePrimeCarryProfileCost := by
  have hprofiles :=
    summable_nativeGpreTowerProfileVector_norm_sq_over_primes
      1 (by norm_num)
  have hmajor := hprofiles.mul_left (2 : ℝ)
  exact Summable.of_nonneg_of_le
    nativeGprePrimeCarryProfileCost_nonneg
    (fun p => by
      unfold nativeGprePrimeCarryProfileCost
      exact mul_le_mul_of_nonneg_right
        (primeCriticalCenteredCarryDualAxis_norm_sq_le_two p)
        (sq_nonneg _))
    hmajor

theorem nativeGprePrimeCarryProfileCost_le_majorant
    (p : Nat.Primes) :
    nativeGprePrimeCarryProfileCost p ≤
      nativeGprePrimeCarryContractionMajorant
        (nativeGprePrimeCarryContractionIndex p) := by
  by_cases hpTwo : (p : ℕ) = 2
  · have hdual :
        ‖primeCriticalCenteredCarryDualAxis p‖ ^ 2 = 2 := by
      rw [primeCriticalCenteredCarryDualAxis_norm_sq]
      norm_num [hpTwo]
    rw [nativeGprePrimeCarryProfileCost, hdual]
    have hprofile :
        ‖nativeGpreTowerProfileVector (p : ℕ) 1‖ ^ 2 ≤
          (13 / 48 : ℝ) := by
      simpa [hpTwo] using
        nativeGpreTowerProfileVector_two_one_norm_sq_le
    simp only [nativeGprePrimeCarryContractionIndex, hpTwo, if_pos,
      nativeGprePrimeCarryContractionMajorant]
    norm_num
    nlinarith
  · have hpOdd : Odd (p : ℕ) :=
      Nat.odd_iff.mpr (p.property.eq_two_or_odd.resolve_left hpTwo)
    rcases hpOdd with ⟨k, hk⟩
    have hkpos : 0 < k := by
      have hpTwoLe := p.property.two_le
      omega
    have hpThree : 3 ≤ (p : ℕ) := by omega
    have hdual :
        ‖primeCriticalCenteredCarryDualAxis p‖ ^ 2 ≤
          (3 / 2 : ℝ) := by
      rw [primeCriticalCenteredCarryDualAxis_norm_sq]
      have hden : 0 < (p : ℝ) - 1 := by
        have hpOne : (1 : ℝ) < (p : ℝ) := by
          exact_mod_cast p.property.one_lt
        linarith
      apply (div_le_iff₀ hden).2
      have hpThreeR : (3 : ℝ) ≤ p := by exact_mod_cast hpThree
      nlinarith
    have hprofile :
        ‖nativeGpreTowerProfileVector (p : ℕ) 1‖ ^ 2 ≤
          (((p : ℝ) ^ 2 - 1)⁻¹) :=
      nativeGpreTowerProfileVector_one_norm_sq_le_resolvent
        (p : ℕ) p.property.two_le
    have hcost :
        nativeGprePrimeCarryProfileCost p ≤
          (3 / 2 : ℝ) * (((p : ℝ) ^ 2 - 1)⁻¹) := by
      unfold nativeGprePrimeCarryProfileCost
      exact
        (mul_le_mul hdual hprofile
          (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 3 / 2))
    have hindex :
        nativeGprePrimeCarryContractionIndex p = k := by
      rw [nativeGprePrimeCarryContractionIndex, if_neg hpTwo, hk]
      omega
    rw [hindex]
    have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
    have hk1R : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hformula :
        (3 / 2 : ℝ) * (((p : ℝ) ^ 2 - 1)⁻¹) =
          nativeGprePrimeCarryContractionMajorant k := by
      rw [nativeGprePrimeCarryContractionMajorant, if_neg hkpos.ne']
      have hpFactor :
          (p : ℝ) ^ 2 - 1 =
            4 * (k : ℝ) * ((k : ℝ) + 1) := by
        rw [hk]
        push_cast
        ring
      rw [hpFactor]
      field_simp [ne_of_gt hkR, ne_of_gt hk1R]
      ring
    exact hcost.trans_eq hformula

theorem nativeGprePrimeCarryProfileCost_tsum_le :
    (∑' p : Nat.Primes, nativeGprePrimeCarryProfileCost p) ≤
      (11 / 12 : ℝ) := by
  let index : Nat.Primes → ℕ :=
    nativeGprePrimeCarryContractionIndex
  let majorant : ℕ → ℝ :=
    nativeGprePrimeCarryContractionMajorant
  have hmajorSummable : Summable majorant :=
    nativeGprePrimeCarryContractionMajorant_summable
  have hindexInjective : Function.Injective index :=
    nativeGprePrimeCarryContractionIndex_injective
  have hcompSummable : Summable (fun p : Nat.Primes => majorant (index p)) :=
    hmajorSummable.comp_injective hindexInjective
  have hcostToComp :
      (∑' p : Nat.Primes, nativeGprePrimeCarryProfileCost p) ≤
        ∑' p : Nat.Primes, majorant (index p) :=
    Summable.tsum_le_tsum
      (fun p => nativeGprePrimeCarryProfileCost_le_majorant p)
      nativeGprePrimeCarryProfileCost_summable
      hcompSummable
  have hcompToAll :
      (∑' p : Nat.Primes, majorant (index p)) ≤
        ∑' k : ℕ, majorant k := by
    exact tsum_comp_le_tsum_of_inj
      (f := majorant)
      hmajorSummable
      nativeGprePrimeCarryContractionMajorant_nonneg
      hindexInjective
  calc
    (∑' p : Nat.Primes, nativeGprePrimeCarryProfileCost p) ≤
        ∑' p : Nat.Primes, majorant (index p) := hcostToComp
    _ ≤ ∑' k : ℕ, majorant k := hcompToAll
    _ = (11 / 12 : ℝ) :=
      nativeGprePrimeCarryContractionMajorant_tsum

theorem nativeGprePrimeCarryDefectCoordinate_norm_sq_summable
    (x : NativeGpreTowerHilbert) :
    Summable (fun p : Nat.Primes =>
      ‖nativeGprePrimeCarryDefectCoordinate x p‖ ^ 2) := by
  have hmoments :=
    summable_nativeGpreTowerPrimeMoment_sq_over_primes
      1 (by norm_num) x
  have hmajor := hmoments.mul_left (2 : ℝ)
  exact Summable.of_nonneg_of_le
    (fun p => sq_nonneg _)
    (fun p => by
      rw [nativeGprePrimeCarryDefectCoordinate_norm_sq]
      exact mul_le_mul_of_nonneg_right
        (primeCriticalCenteredCarryDualAxis_norm_sq_le_two p)
        (sq_nonneg _))
    hmajor

/-- The common centered-carry state produced by the native source state. -/
def nativeGprePrimeCarryDefectState
    (x : NativeGpreTowerHilbert) : PrimeCarryDefectGlobalHilbert :=
  let f : PreLp (fun p : Nat.Primes => PrimeCarryResidueHilbert p) :=
    fun p => nativeGprePrimeCarryDefectCoordinate x p
  ⟨f, by
    change Memℓp f 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    simpa [f] using nativeGprePrimeCarryDefectCoordinate_norm_sq_summable x⟩

@[simp] theorem nativeGprePrimeCarryDefectState_apply
    (x : NativeGpreTowerHilbert) (p : Nat.Primes) :
    nativeGprePrimeCarryDefectState x p =
      nativeGprePrimeCarryDefectCoordinate x p := rfl

/-- Every centered camera reads back exactly its native tower moment. -/
@[simp] theorem inner_globalCarryAxis_nativeGprePrimeCarryDefectState
    (x : NativeGpreTowerHilbert) (p : Nat.Primes) :
    inner ℝ (primeCriticalCenteredCarryGlobalAxis p)
        (nativeGprePrimeCarryDefectState x) =
      inner ℝ (nativeGpreTowerProfileVector (p : ℕ) 1) x := by
  rw [inner_primeCriticalCenteredCarryGlobalAxis,
    nativeGprePrimeCarryDefectState_apply]
  unfold nativeGprePrimeCarryDefectCoordinate
  rw [inner_smul_right,
    inner_primeCriticalCenteredCarryAxis_dualAxis]
  ring

theorem nativeGprePrimeCarryDefectState_norm_sq
    (x : NativeGpreTowerHilbert) :
    ‖nativeGprePrimeCarryDefectState x‖ ^ 2 =
      ∑' p : Nat.Primes,
        ‖nativeGprePrimeCarryDefectCoordinate x p‖ ^ 2 := by
  have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num)
    (nativeGprePrimeCarryDefectState x)
  simpa using h.tsum_eq.symm

/-- Strict contraction from the native pre-compression state to all cameras. -/
theorem nativeGprePrimeCarryDefectState_norm_sq_le
    (x : NativeGpreTowerHilbert) :
    ‖nativeGprePrimeCarryDefectState x‖ ^ 2 ≤
      (11 / 12 : ℝ) * ‖x‖ ^ 2 := by
  have hcost := nativeGprePrimeCarryProfileCost_tsum_le
  have hcostSummable := nativeGprePrimeCarryProfileCost_summable
  have hcoordinate :=
    nativeGprePrimeCarryDefectCoordinate_norm_sq_summable x
  have hpoint :
      ∀ p : Nat.Primes,
        ‖nativeGprePrimeCarryDefectCoordinate x p‖ ^ 2 ≤
          ‖x‖ ^ 2 * nativeGprePrimeCarryProfileCost p := by
    intro p
    rw [nativeGprePrimeCarryDefectCoordinate_norm_sq]
    have hmoment :=
      abs_real_inner_le_norm
        (nativeGpreTowerProfileVector (p : ℕ) 1) x
    have hleft0 :
        0 ≤
          |inner ℝ (nativeGpreTowerProfileVector (p : ℕ) 1) x| :=
      abs_nonneg _
    have hright0 :
        0 ≤ ‖nativeGpreTowerProfileVector (p : ℕ) 1‖ * ‖x‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hmomentSq :
        (inner ℝ (nativeGpreTowerProfileVector (p : ℕ) 1) x) ^ 2 ≤
          ‖nativeGpreTowerProfileVector (p : ℕ) 1‖ ^ 2 * ‖x‖ ^ 2 := by
      have hsquare := (sq_le_sq₀ hleft0 hright0).2 hmoment
      simpa [sq_abs, mul_pow] using hsquare
    unfold nativeGprePrimeCarryProfileCost
    have hdual0 :
        0 ≤ ‖primeCriticalCenteredCarryDualAxis p‖ ^ 2 :=
      sq_nonneg _
    calc
      ‖primeCriticalCenteredCarryDualAxis p‖ ^ 2 *
          (inner ℝ (nativeGpreTowerProfileVector (p : ℕ) 1) x) ^ 2 ≤
        ‖primeCriticalCenteredCarryDualAxis p‖ ^ 2 *
          (‖nativeGpreTowerProfileVector (p : ℕ) 1‖ ^ 2 *
            ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hmomentSq hdual0
      _ = ‖x‖ ^ 2 *
          (‖primeCriticalCenteredCarryDualAxis p‖ ^ 2 *
            ‖nativeGpreTowerProfileVector (p : ℕ) 1‖ ^ 2) := by ring
  rw [nativeGprePrimeCarryDefectState_norm_sq]
  calc
    (∑' p : Nat.Primes,
        ‖nativeGprePrimeCarryDefectCoordinate x p‖ ^ 2) ≤
      ∑' p : Nat.Primes,
        ‖x‖ ^ 2 * nativeGprePrimeCarryProfileCost p :=
      Summable.tsum_le_tsum hpoint hcoordinate
        (hcostSummable.mul_left (‖x‖ ^ 2))
    _ = ‖x‖ ^ 2 *
        ∑' p : Nat.Primes, nativeGprePrimeCarryProfileCost p := by
      rw [tsum_mul_left]
    _ ≤ ‖x‖ ^ 2 * (11 / 12 : ℝ) :=
      mul_le_mul_of_nonneg_left hcost (sq_nonneg _)
    _ = (11 / 12 : ℝ) * ‖x‖ ^ 2 := by ring

/-! ## Crosswalk to the finite-atlas Pythagorean ledger -/

/--
A fixed-time native moment realization lifts to the common carry realization
used by the prime-camera Pythagorean ledger.
-/
theorem nativeGprePrimeCarryDefectState_realizes
    (M : ℕ) (s : ℂ) (x : NativeGpreTowerHilbert)
    (hx : IsNativeGprePrimeMomentRealizationAt 1 (3 * M) s x) :
    IsCanonicalEnrichedPrimeCarryDefectReadoutRealization
      M s (nativeGprePrimeCarryDefectState x) := by
  intro p
  rw [inner_globalCarryAxis_nativeGprePrimeCarryDefectState, hx p,
    finiteEnrichedNativeGpreLogJetGreenBulkReadout_eq
      p M (by norm_num) (fun _ => 1) (by intro m; norm_num) s]

/-- Constructive, atlas-independent, strictly contractive global lift. -/
theorem nativeMomentRealization_yields_contractive_globalRealization
    (M : ℕ) (s : ℂ) (x : NativeGpreTowerHilbert)
    (hx : IsNativeGprePrimeMomentRealizationAt 1 (3 * M) s x) :
    ∃ y : PrimeCarryDefectGlobalHilbert,
      IsCanonicalEnrichedPrimeCarryDefectReadoutRealization M s y ∧
        ‖y‖ ^ 2 ≤ (11 / 12 : ℝ) * ‖x‖ ^ 2 := by
  exact
    ⟨nativeGprePrimeCarryDefectState x,
      nativeGprePrimeCarryDefectState_realizes M s x hx,
      nativeGprePrimeCarryDefectState_norm_sq_le x⟩

/--
Every finite canonical camera atlas is controlled by the same native source
energy, with the strict factor `11/12`.
-/
theorem canonicalProvenanceState_norm_sq_le_of_nativeMomentRealization
    (M : ℕ) (s : ℂ) (x : NativeGpreTowerHilbert)
    (hx : IsNativeGprePrimeMomentRealizationAt 1 (3 * M) s x)
    (S : Finset Nat.Primes) :
    ‖canonicalEnrichedPrimeCarryDefectProvenanceState M s S‖ ^ 2 ≤
      (11 / 12 : ℝ) * ‖x‖ ^ 2 := by
  exact
    (canonicalProvenanceState_norm_sq_le_of_realizesOn
      M s S (nativeGprePrimeCarryDefectState x)
      (fun p hp =>
        nativeGprePrimeCarryDefectState_realizes M s x hx p)).trans
      (nativeGprePrimeCarryDefectState_norm_sq_le x)

end

end CPFormal.Analytic.Cp
