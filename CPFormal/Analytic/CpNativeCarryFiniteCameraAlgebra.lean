import CPFormal.Analytic.CpNativeCarryRealPlaneBracket

/-!
# Finite algebra of the native carry cameras

This file stays entirely at finite cutoff and in an additive commutative
group.  It records four pieces of algebra that are independent of primality:

* the scanner's specially labelled aligned `C₂` camera is exactly the native
  width-four saturated camera;
* every nontrivial odd width has a prefix-minus-centres normal form;
* odd widths satisfy a multiplicative decomposition and the resulting cross
  identity;
* every even width greater than two has a normal form with the missing
  `D_(b/2)` channel displayed explicitly.

The hypotheses `1 < p` in the odd results and `2 < b` in the even result only
exclude degenerate widths.  No assertion here concerns an infinite series,
convergence, a zero of an analytic function, or a prime-only residue model.
-/

open scoped BigOperators

namespace CPFormal.Analytic.Cp

noncomputable section

variable {A : Type*} [AddCommGroup A]

/-! ## Finite prefixes and channels -/

/-- Literal positive prefix `1, ..., endpoint`. -/
def nativeCarryPositivePrefix (endpoint : ℤ) (f : ℤ → A) : A :=
  ∑ n ∈ Finset.Icc (1 : ℤ) endpoint, f n

/-- Values on the aligned centres `p, 2p, ..., Mp`. -/
def nativeCarryCenterChannel (p M : ℕ) (f : ℤ → A) : A :=
  ∑ k ∈ Finset.range M,
    f (CPFormal.Genuine.Cp.alignedCenter p k)

/-- The first `L` positive samples after dilation by `d`. -/
def nativeCarryDilationChannel (d L : ℕ) (f : ℤ → A) : A :=
  ∑ j ∈ Finset.range L,
    f ((d : ℤ) * ((j + 1 : ℕ) : ℤ))

/-- A complete additive block of radius `h`, including its centre. -/
def nativeCarryCompleteBlock
    (h : ℕ) (f : ℤ → A) (center : ℤ) : A :=
  ∑ offset ∈ Finset.Icc (-(h : ℤ)) (h : ℤ),
    f (center + offset)

/-- Add one saturated bracket at the next aligned centre. -/
theorem nativeCarryFiniteSaturatedChart_succ
    (p M : ℕ) (f : ℤ → A) :
    nativeCarryFiniteSaturatedChart p (M + 1) f =
      nativeCarryFiniteSaturatedChart p M f +
        CPFormal.saturatedBracket
          (CPFormal.Genuine.Cp.halfRange p) f
          (CPFormal.Genuine.Cp.alignedCenter p M) := by
  classical
  unfold nativeCarryFiniteSaturatedChart
  rw [Finset.sum_range_succ]
  abel

/-- Add the next aligned centre to the centre channel. -/
theorem nativeCarryCenterChannel_succ
    (p M : ℕ) (f : ℤ → A) :
    nativeCarryCenterChannel p (M + 1) f =
      nativeCarryCenterChannel p M f +
        f (CPFormal.Genuine.Cp.alignedCenter p M) := by
  classical
  unfold nativeCarryCenterChannel
  rw [Finset.sum_range_succ]

/-! ## Elementary reindexing and complete blocks -/

/-- Reindex positive natural radii by their positive integer interval. -/
lemma nativeCarry_sum_nat_radii_eq_sum_int_positive
    (h : ℕ) (g : ℤ → A) :
    (∑ radius ∈ Finset.Icc 1 h, g (radius : ℤ)) =
      ∑ a ∈ Finset.Icc (1 : ℤ) (h : ℤ), g a := by
  classical
  refine Finset.sum_bij (fun radius _ ↦ (radius : ℤ)) ?_ ?_ ?_ ?_
  · intro radius hradius
    simp only [Finset.mem_Icc] at hradius ⊢
    exact_mod_cast hradius
  · intro radius₁ hradius₁ radius₂ hradius₂ heq
    exact_mod_cast heq
  · intro a ha
    have haBounds := Finset.mem_Icc.mp ha
    have haNonneg : 0 ≤ a := le_trans (by norm_num) haBounds.1
    have hcast : ((a.toNat : ℕ) : ℤ) = a :=
      Int.toNat_of_nonneg haNonneg
    refine ⟨a.toNat, ?_, hcast⟩
    apply Finset.mem_Icc.mpr
    constructor
    · exact_mod_cast (show (1 : ℤ) ≤ (a.toNat : ℤ) by
        simpa [hcast] using haBounds.1)
    · exact_mod_cast (show (a.toNat : ℤ) ≤ (h : ℤ) by
        simpa [hcast] using haBounds.2)
  · intro radius hradius
    rfl

/-- Reindex positive natural radii by the corresponding negative integers. -/
lemma nativeCarry_sum_neg_nat_radii_eq_sum_int_negative
    (h : ℕ) (g : ℤ → A) :
    (∑ radius ∈ Finset.Icc 1 h, g (-(radius : ℤ))) =
      ∑ a ∈ Finset.Icc (-(h : ℤ)) (-1), g a := by
  classical
  refine Finset.sum_bij (fun radius _ ↦ -(radius : ℤ)) ?_ ?_ ?_ ?_
  · intro radius hradius
    simp only [Finset.mem_Icc] at hradius ⊢
    have hlower : (1 : ℤ) ≤ (radius : ℤ) := by
      exact_mod_cast hradius.1
    have hupper : (radius : ℤ) ≤ (h : ℤ) := by
      exact_mod_cast hradius.2
    constructor <;> omega
  · intro radius₁ hradius₁ radius₂ hradius₂ heq
    have : (radius₁ : ℤ) = (radius₂ : ℤ) := neg_injective heq
    exact_mod_cast this
  · intro a ha
    have haBounds := Finset.mem_Icc.mp ha
    have hnegNonneg : 0 ≤ -a := by omega
    have hcast : (((-a).toNat : ℕ) : ℤ) = -a :=
      Int.toNat_of_nonneg hnegNonneg
    refine ⟨(-a).toNat, ?_, ?_⟩
    · apply Finset.mem_Icc.mpr
      constructor
      · exact_mod_cast (show (1 : ℤ) ≤ ((-a).toNat : ℤ) by
          rw [hcast]
          omega)
      · exact_mod_cast (show (((-a).toNat : ℕ) : ℤ) ≤ (h : ℤ) by
          rw [hcast]
          omega)
    · rw [hcast]
      omega
  · intro radius hradius
    rfl

/-- Split a sum over two adjacent integer intervals. -/
lemma nativeCarry_sum_Icc_split_adjacent
    (f : ℤ → A) {left middle right : ℤ}
    (hleft : left ≤ middle) (hright : middle < right) :
    (∑ n ∈ Finset.Icc left right, f n) =
      (∑ n ∈ Finset.Icc left middle, f n) +
        ∑ n ∈ Finset.Icc (middle + 1) right, f n := by
  classical
  have hdisjoint :
      Disjoint (Finset.Icc left middle)
        (Finset.Icc (middle + 1) right) := by
    rw [Finset.disjoint_left]
    intro n hnleft hnright
    simp only [Finset.mem_Icc] at hnleft hnright
    omega
  have hunion :
      Finset.Icc left middle ∪ Finset.Icc (middle + 1) right =
        Finset.Icc left right := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  rw [← hunion, Finset.sum_union hdisjoint]

/-- Translating complete offsets gives the literal interval around a centre. -/
theorem nativeCarryCompleteBlock_eq_sum_Icc
    (h : ℕ) (f : ℤ → A) (center : ℤ) :
    nativeCarryCompleteBlock h f center =
      ∑ n ∈ Finset.Icc
        (center - (h : ℤ)) (center + (h : ℤ)), f n := by
  classical
  unfold nativeCarryCompleteBlock
  apply Finset.sum_bijective (fun a : ℤ ↦ center + a)
  · constructor
    · intro a b hab
      exact add_left_cancel hab
    · intro n
      exact ⟨n - center, by ring⟩
  · intro a
    simp only [Finset.mem_Icc]
    constructor <;> intro ha <;> constructor <;> omega
  · intro a ha
    rfl

/-- A nondegenerate complete block is its centre plus its symmetric pairs. -/
theorem nativeCarryCompleteBlock_eq_center_add_pairSum
    (h : ℕ) (hh : 1 ≤ h) (f : ℤ → A) (center : ℤ) :
    nativeCarryCompleteBlock h f center =
      f center +
        ∑ radius ∈ Finset.Icc 1 h,
          (f (center - (radius : ℤ)) +
            f (center + (radius : ℤ))) := by
  classical
  have hhInt : (1 : ℤ) ≤ (h : ℤ) := by
    exact_mod_cast hh
  have hneg : -(h : ℤ) ≤ -1 := by omega
  have hpos : (0 : ℤ) < (h : ℤ) := by
    exact_mod_cast hh
  rw [nativeCarryCompleteBlock]
  rw [nativeCarry_sum_Icc_split_adjacent
    (fun a : ℤ ↦ f (center + a)) hneg (by omega)]
  rw [nativeCarry_sum_Icc_split_adjacent
    (fun a : ℤ ↦ f (center + a)) (by omega) hpos]
  norm_num only [Int.reduceNeg, Int.reduceAdd, zero_add, add_zero]
  rw [← nativeCarry_sum_neg_nat_radii_eq_sum_int_negative
    h (fun a : ℤ ↦ f (center + a))]
  rw [← nativeCarry_sum_nat_radii_eq_sum_int_positive
    h (fun a : ℤ ↦ f (center + a))]
  simp [Finset.sum_add_distrib, sub_eq_add_neg]
  abel

/--
A saturated bracket is a complete block minus `2h+1` copies of its centre.
-/
theorem saturatedBracket_eq_nativeCarryCompleteBlock_sub
    (h : ℕ) (hh : 1 ≤ h) (f : ℤ → A) (center : ℤ) :
    CPFormal.saturatedBracket h f center =
      nativeCarryCompleteBlock h f center -
        (2 * h + 1) • f center := by
  classical
  rw [nativeCarryCompleteBlock_eq_center_add_pairSum h hh]
  unfold CPFormal.saturatedBracket CPFormal.centeredSecondDifference
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hcard : (Finset.Icc 1 h).card = h := by
    rw [Nat.card_Icc]
    omega
  have hcenter :
      (∑ _radius ∈ Finset.Icc 1 h, 2 • f center) =
        (2 * h) • f center := by
    calc
      (∑ _radius ∈ Finset.Icc 1 h, 2 • f center) =
          h • (2 • f center) := by simp [hcard]
      _ = (2 * h) • f center := by
        rw [smul_smul]
        congr 1
        omega
  have hcoefficient :
      (2 * h + 1) • f center =
        (2 * h) • f center + f center := by
    rw [add_nsmul, one_nsmul]
  rw [hcenter, hcoefficient]
  abel

/-! ## The aligned camera labelled `C₂` -/

/--
The scanner's `C₂` label: one seed sample and radius-one brackets at
`4, 8, ..., 4M`.
-/
def nativeCarryAlignedC2Chart (M : ℕ) (f : ℤ → A) : A :=
  f 1 +
    ∑ k ∈ Finset.range M,
      CPFormal.centeredSecondDifference f
        (CPFormal.Genuine.Cp.alignedCenter 4 k) 1

/-- The explicitly aligned `C₂` chart is exactly the native width-four chart. -/
theorem nativeCarryAlignedC2Chart_eq_width_four
    (M : ℕ) (f : ℤ → A) :
    nativeCarryAlignedC2Chart M f =
      nativeCarryFiniteSaturatedChart 4 M f := by
  classical
  norm_num [nativeCarryAlignedC2Chart,
    nativeCarryFiniteSaturatedChart, CPFormal.saturatedBracket,
    CPFormal.Genuine.Cp.halfRange]

/-! ## Odd-width normal form -/

/--
For every nontrivial odd width, the native finite chart is a literal positive
prefix minus `p` copies of every aligned centre.  Primality is absent.
-/
theorem nativeCarryFiniteSaturatedChart_odd_normal_form
    (p M : ℕ) (hpodd : Odd p) (hp : 1 < p) (f : ℤ → A) :
    nativeCarryFiniteSaturatedChart p M f =
      nativeCarryPositivePrefix
          ((p : ℤ) * (M : ℤ) +
            (CPFormal.Genuine.Cp.halfRange p : ℤ)) f -
        p • nativeCarryCenterChannel p M f := by
  induction M with
  | zero =>
      simp [nativeCarryFiniteSaturatedChart, nativeCarryPositivePrefix,
        nativeCarryCenterChannel]
  | succ M ih =>
      have hpformNat :=
        CPFormal.Carry.Cp.two_mul_halfRange_add_one hpodd
      have hh : 1 ≤ CPFormal.Genuine.Cp.halfRange p := by
        omega
      have hpformInt :
          (p : ℤ) =
            2 * (CPFormal.Genuine.Cp.halfRange p : ℤ) + 1 := by
        exact_mod_cast hpformNat.symm
      have hlower :
          CPFormal.Genuine.Cp.alignedCenter p M -
              (CPFormal.Genuine.Cp.halfRange p : ℤ) =
            (p : ℤ) * (M : ℤ) +
              (CPFormal.Genuine.Cp.halfRange p : ℤ) + 1 := by
        unfold CPFormal.Genuine.Cp.alignedCenter
        push_cast
        rw [hpformInt]
        ring
      have hupper :
          CPFormal.Genuine.Cp.alignedCenter p M +
              (CPFormal.Genuine.Cp.halfRange p : ℤ) =
            (p : ℤ) * ((M + 1 : ℕ) : ℤ) +
              (CPFormal.Genuine.Cp.halfRange p : ℤ) := by
        rfl
      have hhInt :
          (1 : ℤ) ≤
            (CPFormal.Genuine.Cp.halfRange p : ℤ) := by
        exact_mod_cast hh
      have hnonneg : 0 ≤ (p : ℤ) * (M : ℤ) := by positivity
      have hleft :
          (1 : ℤ) ≤
            (p : ℤ) * (M : ℤ) +
              (CPFormal.Genuine.Cp.halfRange p : ℤ) := by
        omega
      have hpIntPos : 0 < (p : ℤ) := by
        exact_mod_cast (lt_trans Nat.zero_lt_one hp)
      have hstep :
          (p : ℤ) * ((M + 1 : ℕ) : ℤ) +
              (CPFormal.Genuine.Cp.halfRange p : ℤ) =
            ((p : ℤ) * (M : ℤ) +
              (CPFormal.Genuine.Cp.halfRange p : ℤ)) + (p : ℤ) := by
        push_cast
        ring
      have hright :
          (p : ℤ) * (M : ℤ) +
              (CPFormal.Genuine.Cp.halfRange p : ℤ) <
            (p : ℤ) * ((M + 1 : ℕ) : ℤ) +
              (CPFormal.Genuine.Cp.halfRange p : ℤ) := by
        rw [hstep]
        exact lt_add_of_pos_right _ hpIntPos
      have htile :
          nativeCarryPositivePrefix
                ((p : ℤ) * (M : ℤ) +
                  (CPFormal.Genuine.Cp.halfRange p : ℤ)) f +
              nativeCarryCompleteBlock
                (CPFormal.Genuine.Cp.halfRange p) f
                (CPFormal.Genuine.Cp.alignedCenter p M) =
            nativeCarryPositivePrefix
              ((p : ℤ) * ((M + 1 : ℕ) : ℤ) +
                (CPFormal.Genuine.Cp.halfRange p : ℤ)) f := by
        unfold nativeCarryPositivePrefix
        rw [nativeCarryCompleteBlock_eq_sum_Icc, hlower, hupper]
        exact
          (nativeCarry_sum_Icc_split_adjacent f hleft hright).symm
      rw [nativeCarryFiniteSaturatedChart_succ, ih]
      rw [saturatedBracket_eq_nativeCarryCompleteBlock_sub
        (CPFormal.Genuine.Cp.halfRange p) hh]
      rw [nativeCarryCenterChannel_succ, nsmul_add]
      calc
        (nativeCarryPositivePrefix
                ((p : ℤ) * (M : ℤ) +
                  (CPFormal.Genuine.Cp.halfRange p : ℤ)) f -
              p • nativeCarryCenterChannel p M f) +
            (nativeCarryCompleteBlock
                (CPFormal.Genuine.Cp.halfRange p) f
                (CPFormal.Genuine.Cp.alignedCenter p M) -
              (2 * CPFormal.Genuine.Cp.halfRange p + 1) •
                f (CPFormal.Genuine.Cp.alignedCenter p M)) =
            (nativeCarryPositivePrefix
                ((p : ℤ) * (M : ℤ) +
                  (CPFormal.Genuine.Cp.halfRange p : ℤ)) f +
              nativeCarryCompleteBlock
                (CPFormal.Genuine.Cp.halfRange p) f
                (CPFormal.Genuine.Cp.alignedCenter p M)) -
              (p • nativeCarryCenterChannel p M f +
                p • f (CPFormal.Genuine.Cp.alignedCenter p M)) := by
                  rw [hpformNat]
                  abel
        _ = nativeCarryPositivePrefix
                ((p : ℤ) * ((M + 1 : ℕ) : ℤ) +
                  (CPFormal.Genuine.Cp.halfRange p : ℤ)) f -
              (p • nativeCarryCenterChannel p M f +
                p • f (CPFormal.Genuine.Cp.alignedCenter p M)) := by
              rw [htile]

/-! ## Odd multiplicative decomposition -/

/-- Half-ranges multiply affinely for odd widths. -/
lemma halfRange_mul_of_odd
    {a b : ℕ} (haodd : Odd a) (hbodd : Odd b) :
    CPFormal.Genuine.Cp.halfRange (a * b) =
      a * CPFormal.Genuine.Cp.halfRange b +
        CPFormal.Genuine.Cp.halfRange a := by
  have haform :=
    CPFormal.Carry.Cp.two_mul_halfRange_add_one haodd
  have hbform :=
    CPFormal.Carry.Cp.two_mul_halfRange_add_one hbodd
  have habform :=
    CPFormal.Carry.Cp.two_mul_halfRange_add_one (haodd.mul hbodd)
  have htwice :
      2 * (a * CPFormal.Genuine.Cp.halfRange b +
          CPFormal.Genuine.Cp.halfRange a) + 1 =
        2 * CPFormal.Genuine.Cp.halfRange (a * b) + 1 := by
    calc
      2 * (a * CPFormal.Genuine.Cp.halfRange b +
          CPFormal.Genuine.Cp.halfRange a) + 1 =
          2 * a * CPFormal.Genuine.Cp.halfRange b +
            (2 * CPFormal.Genuine.Cp.halfRange a + 1) := by ring
      _ = 2 * a * CPFormal.Genuine.Cp.halfRange b + a := by
        rw [haform]
      _ = a * (2 * CPFormal.Genuine.Cp.halfRange b + 1) := by ring
      _ = a * b := by rw [hbform]
      _ = 2 * CPFormal.Genuine.Cp.halfRange (a * b) + 1 :=
        habform.symm
  omega

/-- Aligned centres are exactly a dilated positive prefix. -/
theorem nativeCarryCenterChannel_eq_dilated_positivePrefix
    (p M : ℕ) (f : ℤ → A) :
    nativeCarryCenterChannel p M f =
      nativeCarryPositivePrefix (M : ℤ)
        (fun n ↦ f ((p : ℤ) * n)) := by
  classical
  unfold nativeCarryCenterChannel nativeCarryPositivePrefix
    CPFormal.Genuine.Cp.alignedCenter
  refine Finset.sum_bij
    (fun k _ ↦ ((k + 1 : ℕ) : ℤ)) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_range] at hk
    apply Finset.mem_Icc.mpr
    constructor
    · exact_mod_cast (show 1 ≤ k + 1 by omega)
    · exact_mod_cast (show k + 1 ≤ M by omega)
  · intro k₁ hk₁ k₂ hk₂ heq
    have hsucc : k₁ + 1 = k₂ + 1 := by
      exact_mod_cast heq
    omega
  · intro n hn
    have hnBounds := Finset.mem_Icc.mp hn
    have hnNonneg : 0 ≤ n := le_trans (by norm_num) hnBounds.1
    have hcast : ((n.toNat : ℕ) : ℤ) = n :=
      Int.toNat_of_nonneg hnNonneg
    have hnOne : 1 ≤ n.toNat := by
      simpa using Int.toNat_le_toNat hnBounds.1
    have hnUpper : n.toNat ≤ M := by
      simpa using Int.toNat_le_toNat hnBounds.2
    refine ⟨n.toNat - 1, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · rw [Nat.sub_add_cancel hnOne, hcast]
  · intro k hk
    rfl

/-- Dilation by `a` sends the `b`-centre channel to the `ab` channel. -/
theorem nativeCarryCenterChannel_dilation
    (a b M : ℕ) (f : ℤ → A) :
    nativeCarryCenterChannel b M
        (fun n ↦ f ((a : ℤ) * n)) =
      nativeCarryCenterChannel (a * b) M f := by
  classical
  unfold nativeCarryCenterChannel CPFormal.Genuine.Cp.alignedCenter
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  push_cast
  ring

/--
Odd product decomposition.  The cutoff shift is exactly the half-range of the
inner width, and no prime hypothesis is used.
-/
theorem nativeCarryFiniteSaturatedChart_odd_mul_decomposition
    (a b M : ℕ)
    (haodd : Odd a) (hbodd : Odd b)
    (ha : 1 < a) (hb : 1 < b)
    (f : ℤ → A) :
    nativeCarryFiniteSaturatedChart (a * b) M f =
      nativeCarryFiniteSaturatedChart a
          (b * M + CPFormal.Genuine.Cp.halfRange b) f +
        a • nativeCarryFiniteSaturatedChart b M
          (fun n ↦ f ((a : ℤ) * n)) := by
  have hab : 1 < a * b := by nlinarith
  have hendpoint :
      ((a * b : ℕ) : ℤ) * (M : ℤ) +
          (CPFormal.Genuine.Cp.halfRange (a * b) : ℤ) =
        (a : ℤ) *
            ((b * M + CPFormal.Genuine.Cp.halfRange b : ℕ) : ℤ) +
          (CPFormal.Genuine.Cp.halfRange a : ℤ) := by
    rw [halfRange_mul_of_odd haodd hbodd]
    push_cast
    ring
  have hcancel :
      nativeCarryCenterChannel a
          (b * M + CPFormal.Genuine.Cp.halfRange b) f =
        nativeCarryPositivePrefix
          ((b : ℤ) * (M : ℤ) +
            (CPFormal.Genuine.Cp.halfRange b : ℤ))
          (fun n ↦ f ((a : ℤ) * n)) := by
    rw [nativeCarryCenterChannel_eq_dilated_positivePrefix]
    apply congrArg
      (fun endpoint ↦
        nativeCarryPositivePrefix endpoint
          (fun n ↦ f ((a : ℤ) * n)))
    push_cast
    ring
  rw [nativeCarryFiniteSaturatedChart_odd_normal_form
      (a * b) M (haodd.mul hbodd) hab,
    nativeCarryFiniteSaturatedChart_odd_normal_form
      a (b * M + CPFormal.Genuine.Cp.halfRange b) haodd ha,
    nativeCarryFiniteSaturatedChart_odd_normal_form
      b M hbodd hb]
  rw [hendpoint, hcancel,
    nativeCarryCenterChannel_dilation a b M]
  simp only [nsmul_sub, smul_smul]
  abel

/-- The two odd factorizations of the same product give the finite cross law. -/
theorem nativeCarryFiniteSaturatedChart_odd_cross_identity
    (a b M : ℕ)
    (haodd : Odd a) (hbodd : Odd b)
    (ha : 1 < a) (hb : 1 < b)
    (f : ℤ → A) :
    nativeCarryFiniteSaturatedChart a
          (b * M + CPFormal.Genuine.Cp.halfRange b) f +
        a • nativeCarryFiniteSaturatedChart b M
          (fun n ↦ f ((a : ℤ) * n)) =
      nativeCarryFiniteSaturatedChart b
          (a * M + CPFormal.Genuine.Cp.halfRange a) f +
        b • nativeCarryFiniteSaturatedChart a M
          (fun n ↦ f ((b : ℤ) * n)) := by
  calc
    nativeCarryFiniteSaturatedChart a
          (b * M + CPFormal.Genuine.Cp.halfRange b) f +
        a • nativeCarryFiniteSaturatedChart b M
          (fun n ↦ f ((a : ℤ) * n)) =
        nativeCarryFiniteSaturatedChart (a * b) M f :=
      (nativeCarryFiniteSaturatedChart_odd_mul_decomposition
        a b M haodd hbodd ha hb f).symm
    _ = nativeCarryFiniteSaturatedChart (b * a) M f := by
      rw [Nat.mul_comm a b]
    _ = nativeCarryFiniteSaturatedChart b
          (a * M + CPFormal.Genuine.Cp.halfRange a) f +
        b • nativeCarryFiniteSaturatedChart a M
          (fun n ↦ f ((b : ℤ) * n)) :=
      nativeCarryFiniteSaturatedChart_odd_mul_decomposition
        b a M hbodd haodd hb ha f

/-! ## Even-width normal form -/

/-- Arithmetic form of a nondegenerate even half-range. -/
lemma two_mul_halfRange_add_two_of_even
    {b : ℕ} (hbeven : Even b) (hb : 2 < b) :
    2 * CPFormal.Genuine.Cp.halfRange b + 2 = b := by
  rcases hbeven with ⟨d, rfl⟩
  unfold CPFormal.Genuine.Cp.halfRange
  omega

/-- For a nondegenerate even width, `b/2` is one past the half-range. -/
lemma div_two_eq_halfRange_add_one_of_even
    {b : ℕ} (hbeven : Even b) (hb : 2 < b) :
    b / 2 = CPFormal.Genuine.Cp.halfRange b + 1 := by
  have hform := two_mul_halfRange_add_two_of_even hbeven hb
  rcases hbeven with ⟨d, hd⟩
  subst b
  omega

/-- Add the next gap and centre to the explicit `D_(b/2)` channel. -/
lemma nativeCarryDilationChannel_even_succ
    (b M : ℕ) (hbeven : Even b) (f : ℤ → A) :
    nativeCarryDilationChannel (b / 2) (2 * (M + 1)) f =
      nativeCarryDilationChannel (b / 2) (2 * M) f +
        f ((b : ℤ) * (M : ℤ) + ((b / 2 : ℕ) : ℤ)) +
        f (CPFormal.Genuine.Cp.alignedCenter b M) := by
  classical
  have htwo : 2 * (b / 2) = b := by
    rcases hbeven with ⟨d, rfl⟩
    omega
  unfold nativeCarryDilationChannel
  rw [show 2 * (M + 1) = (2 * M + 1) + 1 by omega,
    Finset.sum_range_succ,
    Finset.sum_range_succ]
  have htwoInt : 2 * ((b / 2 : ℕ) : ℤ) = (b : ℤ) := by
    exact_mod_cast htwo
  have hgap :
      ((b / 2 : ℕ) : ℤ) * (((2 * M) + 1 : ℕ) : ℤ) =
        (b : ℤ) * (M : ℤ) + ((b / 2 : ℕ) : ℤ) := by
    push_cast
    rw [← htwoInt]
    ring
  have hcenter :
      ((b / 2 : ℕ) : ℤ) * (((2 * M + 1) + 1 : ℕ) : ℤ) =
        CPFormal.Genuine.Cp.alignedCenter b M := by
    unfold CPFormal.Genuine.Cp.alignedCenter
    push_cast
    rw [← htwoInt]
    ring
  rw [hgap, hcenter]

/--
Even normal form.  The first subtraction is the explicit positive
`D_(b/2)` channel; the remaining correction has coefficient `b-2`.
-/
theorem nativeCarryFiniteSaturatedChart_even_normal_form
    (b M : ℕ) (hbeven : Even b) (hb : 2 < b) (f : ℤ → A) :
    nativeCarryFiniteSaturatedChart b M f =
      nativeCarryPositivePrefix
          ((b : ℤ) * (M : ℤ) +
            (CPFormal.Genuine.Cp.halfRange b : ℤ)) f -
        nativeCarryDilationChannel (b / 2) (2 * M) f -
        (b - 2) • nativeCarryCenterChannel b M f := by
  induction M with
  | zero =>
      simp [nativeCarryFiniteSaturatedChart, nativeCarryPositivePrefix,
        nativeCarryDilationChannel, nativeCarryCenterChannel]
  | succ M ih =>
      have hbformNat :=
        two_mul_halfRange_add_two_of_even hbeven hb
      have hdformNat :=
        div_two_eq_halfRange_add_one_of_even hbeven hb
      have hh : 1 ≤ CPFormal.Genuine.Cp.halfRange b := by
        omega
      have hbformInt :
          (b : ℤ) =
            2 * (CPFormal.Genuine.Cp.halfRange b : ℤ) + 2 := by
        exact_mod_cast hbformNat.symm
      have hdformInt :
          ((b / 2 : ℕ) : ℤ) =
            (CPFormal.Genuine.Cp.halfRange b : ℤ) + 1 := by
        exact_mod_cast hdformNat
      have hgap :
          (b : ℤ) * (M : ℤ) + ((b / 2 : ℕ) : ℤ) =
            ((b : ℤ) * (M : ℤ) +
              (CPFormal.Genuine.Cp.halfRange b : ℤ)) + 1 := by
        rw [hdformInt]
        ring
      have hlower :
          CPFormal.Genuine.Cp.alignedCenter b M -
              (CPFormal.Genuine.Cp.halfRange b : ℤ) =
            ((b : ℤ) * (M : ℤ) + ((b / 2 : ℕ) : ℤ)) + 1 := by
        unfold CPFormal.Genuine.Cp.alignedCenter
        push_cast
        rw [hbformInt, hdformInt]
        ring
      have hupper :
          CPFormal.Genuine.Cp.alignedCenter b M +
              (CPFormal.Genuine.Cp.halfRange b : ℤ) =
            (b : ℤ) * ((M + 1 : ℕ) : ℤ) +
              (CPFormal.Genuine.Cp.halfRange b : ℤ) := by
        rfl
      have hhInt :
          (1 : ℤ) ≤
            (CPFormal.Genuine.Cp.halfRange b : ℤ) := by
        exact_mod_cast hh
      have hnonneg : 0 ≤ (b : ℤ) * (M : ℤ) := by positivity
      have hleft :
          (1 : ℤ) ≤
            (b : ℤ) * (M : ℤ) +
              (CPFormal.Genuine.Cp.halfRange b : ℤ) := by
        omega
      have hbIntPos : 0 < (b : ℤ) := by
        exact_mod_cast (lt_trans Nat.zero_lt_two hb)
      have hstep :
          (b : ℤ) * ((M + 1 : ℕ) : ℤ) +
              (CPFormal.Genuine.Cp.halfRange b : ℤ) =
            ((b : ℤ) * (M : ℤ) +
              (CPFormal.Genuine.Cp.halfRange b : ℤ)) + (b : ℤ) := by
        push_cast
        ring
      have hright :
          (b : ℤ) * (M : ℤ) +
              (CPFormal.Genuine.Cp.halfRange b : ℤ) <
            (b : ℤ) * ((M + 1 : ℕ) : ℤ) +
              (CPFormal.Genuine.Cp.halfRange b : ℤ) := by
        rw [hstep]
        exact lt_add_of_pos_right _ hbIntPos
      have hgapRight :
          (b : ℤ) * (M : ℤ) + ((b / 2 : ℕ) : ℤ) <
            (b : ℤ) * ((M + 1 : ℕ) : ℤ) +
              (CPFormal.Genuine.Cp.halfRange b : ℤ) := by
        rw [hstep, hgap]
        have hbLarge : (3 : ℤ) ≤ (b : ℤ) := by exact_mod_cast hb
        omega
      have htail :
          f ((b : ℤ) * (M : ℤ) + ((b / 2 : ℕ) : ℤ)) +
              nativeCarryCompleteBlock
                (CPFormal.Genuine.Cp.halfRange b) f
                (CPFormal.Genuine.Cp.alignedCenter b M) =
            ∑ n ∈ Finset.Icc
              (((b : ℤ) * (M : ℤ) +
                (CPFormal.Genuine.Cp.halfRange b : ℤ)) + 1)
              ((b : ℤ) * ((M + 1 : ℕ) : ℤ) +
                (CPFormal.Genuine.Cp.halfRange b : ℤ)), f n := by
        rw [nativeCarryCompleteBlock_eq_sum_Icc, hlower, hupper, ← hgap]
        simpa using
          (nativeCarry_sum_Icc_split_adjacent f
            (le_refl ((b : ℤ) * (M : ℤ) + ((b / 2 : ℕ) : ℤ)))
            hgapRight).symm
      have htile :
          nativeCarryPositivePrefix
              ((b : ℤ) * (M : ℤ) +
                  (CPFormal.Genuine.Cp.halfRange b : ℤ)) f +
              f ((b : ℤ) * (M : ℤ) + ((b / 2 : ℕ) : ℤ)) +
              nativeCarryCompleteBlock
                (CPFormal.Genuine.Cp.halfRange b) f
                (CPFormal.Genuine.Cp.alignedCenter b M) =
            nativeCarryPositivePrefix
              ((b : ℤ) * ((M + 1 : ℕ) : ℤ) +
                (CPFormal.Genuine.Cp.halfRange b : ℤ)) f := by
        unfold nativeCarryPositivePrefix
        rw [add_assoc, htail]
        exact
          (nativeCarry_sum_Icc_split_adjacent f hleft hright).symm
      have hbracketCoefficient :
          2 * CPFormal.Genuine.Cp.halfRange b + 1 = b - 1 := by
        omega
      have hcenterCoefficient :
          (b - 1) •
              f (CPFormal.Genuine.Cp.alignedCenter b M) =
            (b - 2) •
                f (CPFormal.Genuine.Cp.alignedCenter b M) +
              f (CPFormal.Genuine.Cp.alignedCenter b M) := by
        rw [show b - 1 = (b - 2) + 1 by omega,
          add_nsmul, one_nsmul]
      rw [nativeCarryFiniteSaturatedChart_succ, ih]
      rw [saturatedBracket_eq_nativeCarryCompleteBlock_sub
        (CPFormal.Genuine.Cp.halfRange b) hh]
      rw [hbracketCoefficient, hcenterCoefficient]
      rw [nativeCarryDilationChannel_even_succ b M hbeven]
      rw [nativeCarryCenterChannel_succ, nsmul_add]
      rw [← htile]
      abel

end

end CPFormal.Analytic.Cp
