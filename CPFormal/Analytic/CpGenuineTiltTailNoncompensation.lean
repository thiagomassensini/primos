import CPFormal.Analytic.CpGenuineTiltAuxiliaryRoute

/-!
# Cofinal noncancellation of the canonical C3 tilt tail

For a parameter in the open Genuine strip away from the half-abscissa, every
complete C3 tilt block after the first is bounded by an explicit reciprocal-
square envelope.  Its total norm budget is at most

`rho = (3 / 4) * (6 / 5)^(3 / 2)`, with `rho^2 = 243 / 250 < 1`.

Consequently the complete tail of later tilt centers cannot cancel the first
phase-bearing tilt block, at any finite cutoff or in the infinite sum.  This
result concerns the tilt channel itself.  It does not erase or control the
separate critical-carrier remainder in the exact Genuine product-rule ledger.
-/

open scoped BigOperators

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Elementary telescoping majorant used by the canonical C3 tilt tail. -/
theorem invSq_add_two_le_three_quarters (M : ℕ) :
    (∑ k ∈ Finset.range M, (((k + 2 : ℕ) : ℝ) ^ (-2 : ℝ))) ≤
      (3 : ℝ) / 4 := by
  have hterm : ∀ k : ℕ,
      (((k + 2 : ℕ) : ℝ) ^ (-2 : ℝ)) ≤
        (3 : ℝ) / 2 *
          ((((k + 2 : ℕ) : ℝ)⁻¹) -
            (((k + 3 : ℕ) : ℝ)⁻¹)) := by
    intro k
    have h2 : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_left 2 k
    have hpos : 0 < ((k + 2 : ℕ) : ℝ) := lt_of_lt_of_le (by norm_num) h2
    rw [show (((k + 2 : ℕ) : ℝ) ^ (-2 : ℝ)) =
        (((k + 2 : ℕ) : ℝ)⁻¹) ^ 2 by
      rw [Real.rpow_neg (le_of_lt hpos), Real.rpow_two]
      field_simp]
    field_simp
    norm_num at h2 ⊢
    nlinarith
  calc
    (∑ k ∈ Finset.range M, (((k + 2 : ℕ) : ℝ) ^ (-2 : ℝ))) ≤
        ∑ k ∈ Finset.range M,
          ((3 : ℝ) / 2 *
            ((((k + 2 : ℕ) : ℝ)⁻¹) -
              (((k + 3 : ℕ) : ℝ)⁻¹))) := by
      exact Finset.sum_le_sum fun k _ ↦ hterm k
    _ = (3 : ℝ) / 2 *
        ((1 : ℝ) / 2 - (((M + 2 : ℕ) : ℝ)⁻¹)) := by
      rw [← Finset.mul_sum]
      congr 1
      induction M with
      | zero => norm_num
      | succ M ih =>
          rw [Finset.sum_range_succ, ih]
          push_cast
          ring
    _ ≤ (3 : ℝ) / 4 := by
      have : 0 ≤ (((M + 2 : ℕ) : ℝ)⁻¹) := by positivity
      nlinarith

/-- A completely explicit uniform ratio, strictly below one. -/
def canonicalTiltTailRatio : ℝ :=
  (3 : ℝ) / 4 * ((6 : ℝ) / 5) ^ ((3 : ℝ) / 2)

theorem canonicalTiltTailRatio_pos : 0 < canonicalTiltTailRatio := by
  unfold canonicalTiltTailRatio
  positivity

theorem canonicalTiltTailRatio_sq :
    canonicalTiltTailRatio ^ 2 = (243 : ℝ) / 250 := by
  unfold canonicalTiltTailRatio
  rw [mul_pow]
  have hbase : 0 ≤ (6 : ℝ) / 5 := by norm_num
  have hpow :
      (((6 : ℝ) / 5) ^ ((3 : ℝ) / 2)) ^ 2 =
        ((6 : ℝ) / 5) ^ (3 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hbase]
    norm_num
  rw [hpow]
  norm_num [Real.rpow_natCast]

theorem canonicalTiltTailRatio_lt_one : canonicalTiltTailRatio < 1 := by
  have hpos := canonicalTiltTailRatio_pos
  have hsq := canonicalTiltTailRatio_sq
  nlinarith

theorem canonicalTilt_ratio_kernel_bound
    {delta : ℝ} (hdelta : -(1 : ℝ) / 2 < delta)
    {n : ℕ} (hn : 2 ≤ n) :
    ((n : ℝ) ^ (-(1 : ℝ) / 2)) *
        (((3 : ℝ) / (3 * (n : ℝ) - 1)) ^ (delta + 2)) ≤
      (((6 : ℝ) / 5) ^ ((3 : ℝ) / 2)) *
        ((n : ℝ) ^ (-2 : ℝ)) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hn2
  have hdenpos : 0 < 3 * (n : ℝ) - 1 := by nlinarith
  have hxpos : 0 < (3 : ℝ) / (3 * (n : ℝ) - 1) := div_pos (by norm_num) hdenpos
  have hxle1 : (3 : ℝ) / (3 * (n : ℝ) - 1) ≤ 1 := by
    apply (div_le_one hdenpos).2
    nlinarith
  have hexp : (3 : ℝ) / 2 ≤ delta + 2 := by linarith
  have hpowexp :
      ((3 : ℝ) / (3 * (n : ℝ) - 1)) ^ (delta + 2) ≤
        ((3 : ℝ) / (3 * (n : ℝ) - 1)) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hxpos hxle1 hexp
  have hxmajor :
      (3 : ℝ) / (3 * (n : ℝ) - 1) ≤
        ((6 : ℝ) / 5) / (n : ℝ) := by
    apply (div_le_div_iff₀ hdenpos hnpos).2
    nlinarith
  have hpowbase :
      ((3 : ℝ) / (3 * (n : ℝ) - 1)) ^ ((3 : ℝ) / 2) ≤
        (((6 : ℝ) / 5) / (n : ℝ)) ^ ((3 : ℝ) / 2) := by
    exact Real.rpow_le_rpow (le_of_lt hxpos) hxmajor (by norm_num)
  have hnscale : 0 ≤ (n : ℝ) ^ (-(1 : ℝ) / 2) := by positivity
  calc
    ((n : ℝ) ^ (-(1 : ℝ) / 2)) *
        (((3 : ℝ) / (3 * (n : ℝ) - 1)) ^ (delta + 2)) ≤
      ((n : ℝ) ^ (-(1 : ℝ) / 2)) *
        (((3 : ℝ) / (3 * (n : ℝ) - 1)) ^ ((3 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hpowexp hnscale
    _ ≤ ((n : ℝ) ^ (-(1 : ℝ) / 2)) *
        ((((6 : ℝ) / 5) / (n : ℝ)) ^ ((3 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hpowbase hnscale
    _ = (((6 : ℝ) / 5) ^ ((3 : ℝ) / 2)) *
        ((n : ℝ) ^ (-2 : ℝ)) := by
      rw [Real.div_rpow (by norm_num) (le_of_lt hnpos)]
      have hinv :
          (((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹) =
            (n : ℝ) ^ (-((3 : ℝ) / 2)) := by
        exact (Real.rpow_neg (le_of_lt hnpos) ((3 : ℝ) / 2)).symm
      change
        (n : ℝ) ^ (-(1 : ℝ) / 2) *
            (((6 : ℝ) / 5) ^ ((3 : ℝ) / 2) *
              (((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹)) =
          ((6 : ℝ) / 5) ^ ((3 : ℝ) / 2) *
            (n : ℝ) ^ (-2 : ℝ)
      rw [hinv]
      calc
        (n : ℝ) ^ (-(1 : ℝ) / 2) *
            (((6 : ℝ) / 5) ^ ((3 : ℝ) / 2) *
              (n : ℝ) ^ (-((3 : ℝ) / 2))) =
          ((6 : ℝ) / 5) ^ ((3 : ℝ) / 2) *
            ((n : ℝ) ^ (-(1 : ℝ) / 2) *
              (n : ℝ) ^ (-((3 : ℝ) / 2))) := by ring
        _ = ((6 : ℝ) / 5) ^ ((3 : ℝ) / 2) *
            (n : ℝ) ^ (-2 : ℝ) := by
          rw [← Real.rpow_add hnpos]
          congr 2
          ring

private theorem rpow_neg_eq_three_scale
    {den : ℝ} (hden : 0 < den) (a : ℝ) :
    den ^ (-a) =
      (3 : ℝ) ^ (-a) * (((3 : ℝ) / den) ^ a) := by
  rw [Real.rpow_neg (le_of_lt hden),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3),
    Real.div_rpow (by norm_num : (0 : ℝ) ≤ 3) (le_of_lt hden)]
  have h3pow : 0 < (3 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) _
  have hdpow : 0 < den ^ a := Real.rpow_pos_of_pos hden _
  field_simp

/-- The analytic upper envelope factors as the first-block scale times the
dimensionless kernel controlled above. -/
theorem canonicalTilt_upperEnvelope_factorization
    (delta : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    ((3 : ℝ) * (n : ℝ)) ^ (-(1 : ℝ) / 2) *
        (|delta * (delta + 1)| *
          (((3 : ℝ) * (n : ℝ) - 1) ^ (-delta - 2))) =
      ((3 : ℝ) ^ (-(1 : ℝ) / 2) *
          (|delta * (delta + 1)| * (3 : ℝ) ^ (-delta - 2))) *
        (((n : ℝ) ^ (-(1 : ℝ) / 2)) *
          (((3 : ℝ) / ((3 : ℝ) * (n : ℝ) - 1)) ^
            (delta + 2))) := by
  have hnpos : 0 < (n : ℝ) := by positivity
  have hden : 0 < (3 : ℝ) * (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (le_of_lt hnpos)]
  have hpow := rpow_neg_eq_three_scale hden (delta + 2)
  rw [show -delta - 2 = -(delta + 2) by ring, hpow]
  ring

/-- The common positive lower scale used for the first block and the tail. -/
def canonicalTiltFirstScale (s : ℂ) : ℝ :=
  (3 : ℝ) ^ (-(1 : ℝ) / 2) *
    (|criticalDisplacement s.re * (criticalDisplacement s.re + 1)| *
      (3 : ℝ) ^ (-criticalDisplacement s.re - 2))

theorem canonicalTiltFirstScale_pos
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    0 < canonicalTiltFirstScale s := by
  have hdBounds := criticalDisplacement_mem_openHalf_of_mem_strip hs
  have hdne := criticalDisplacement_ne_zero_of_re_ne_half hoff
  have hdplus : 0 < criticalDisplacement s.re + 1 := by linarith
  unfold canonicalTiltFirstScale
  have hprod : criticalDisplacement s.re *
      (criticalDisplacement s.re + 1) ≠ 0 := mul_ne_zero hdne (ne_of_gt hdplus)
  positivity

/-- Every later C3 tilt block is controlled by the first scale times an
explicit reciprocal-square envelope. -/
theorem norm_canonicalCriticalWeightedTiltBlock_succ_le_scale
    (k : ℕ) {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    ‖canonicalCriticalWeightedTiltBlock (k + 1) s‖ ≤
      canonicalTiltFirstScale s *
        (((6 : ℝ) / 5) ^ ((3 : ℝ) / 2) *
          (((k + 2 : ℕ) : ℝ) ^ (-2 : ℝ))) := by
  have hu := canonicalCriticalWeightedTiltBlock_upper_bound (k + 1) hs hoff
  have hn : 2 ≤ k + 2 := by omega
  have hfactor := canonicalTilt_upperEnvelope_factorization
    (criticalDisplacement s.re) hn
  have hkernel := canonicalTilt_ratio_kernel_bound
    (criticalDisplacement_mem_openHalf_of_mem_strip hs).1 hn
  have hscale : 0 ≤ canonicalTiltFirstScale s :=
    le_of_lt (canonicalTiltFirstScale_pos hs hoff)
  have hscaled := mul_le_mul_of_nonneg_left hkernel hscale
  unfold canonicalTiltFirstScale at hscaled
  rw [← hfactor] at hscaled
  unfold canonicalRealCpCenter at hu
  change ‖canonicalCriticalWeightedTiltBlock (k + 1) s‖ ≤
      ((3 : ℝ) * ((k + 2 : ℕ) : ℝ)) ^ (-(1 : ℝ) / 2) *
        (|criticalDisplacement s.re * (criticalDisplacement s.re + 1)| *
          (((3 : ℝ) * ((k + 2 : ℕ) : ℝ) - 1) ^
            (-criticalDisplacement s.re - 2))) at hu
  exact hu.trans hscaled

theorem finiteCanonicalCriticalWeightedTiltTailNorm_le_ratio_scale
    (M : ℕ) {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    finiteCanonicalCriticalWeightedTiltTailNorm M s ≤
      canonicalTiltTailRatio * canonicalTiltFirstScale s := by
  unfold finiteCanonicalCriticalWeightedTiltTailNorm
  calc
    (∑ k ∈ Finset.range M, ‖canonicalCriticalWeightedTiltBlock (k + 1) s‖) ≤
        ∑ k ∈ Finset.range M,
          canonicalTiltFirstScale s *
            (((6 : ℝ) / 5) ^ ((3 : ℝ) / 2) *
              (((k + 2 : ℕ) : ℝ) ^ (-2 : ℝ))) := by
      exact Finset.sum_le_sum fun k _ ↦
        norm_canonicalCriticalWeightedTiltBlock_succ_le_scale k hs hoff
    _ = canonicalTiltFirstScale s *
        (((6 : ℝ) / 5) ^ ((3 : ℝ) / 2) *
          ∑ k ∈ Finset.range M,
            (((k + 2 : ℕ) : ℝ) ^ (-2 : ℝ))) := by
      rw [Finset.mul_sum]
      rw [Finset.mul_sum]
    _ ≤ canonicalTiltFirstScale s *
        (((6 : ℝ) / 5) ^ ((3 : ℝ) / 2) * ((3 : ℝ) / 4)) := by
      have hsum := invSq_add_two_le_three_quarters M
      have hconst : 0 ≤ ((6 : ℝ) / 5) ^ ((3 : ℝ) / 2) := by
        positivity
      have hinner := mul_le_mul_of_nonneg_left hsum hconst
      exact mul_le_mul_of_nonneg_left hinner
        (le_of_lt (canonicalTiltFirstScale_pos hs hoff))
    _ = canonicalTiltTailRatio * canonicalTiltFirstScale s := by
      unfold canonicalTiltTailRatio
      ring

theorem canonicalCriticalTiltFirstBlockDominates_of_strip_offCritical
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    CanonicalCriticalTiltFirstBlockDominatesAt s := by
  intro M
  have htail :=
    finiteCanonicalCriticalWeightedTiltTailNorm_le_ratio_scale M hs hoff
  have hfirst := canonicalCriticalWeightedTiltBlock_zero_lower_bound hs hoff
  have hscalePos := canonicalTiltFirstScale_pos hs hoff
  have hrho := canonicalTiltTailRatio_lt_one
  calc
    finiteCanonicalCriticalWeightedTiltTailNorm M s ≤
        canonicalTiltTailRatio * canonicalTiltFirstScale s := htail
    _ < canonicalTiltFirstScale s := by nlinarith
    _ ≤ ‖canonicalCriticalWeightedTiltBlock 0 s‖ := hfirst

theorem summable_norm_canonicalCriticalWeightedTiltBlock_tail
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    Summable (fun k : ℕ ↦
      ‖canonicalCriticalWeightedTiltBlock (k + 1) s‖) := by
  apply summable_of_sum_range_le
  · intro k
    positivity
  · intro M
    simpa [finiteCanonicalCriticalWeightedTiltTailNorm] using
      finiteCanonicalCriticalWeightedTiltTailNorm_le_ratio_scale M hs hoff

theorem summable_canonicalCriticalWeightedTiltBlock
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    Summable (fun k : ℕ ↦ canonicalCriticalWeightedTiltBlock k s) := by
  have htailNorm :=
    summable_norm_canonicalCriticalWeightedTiltBlock_tail hs hoff
  have htail : Summable (fun k : ℕ ↦
      canonicalCriticalWeightedTiltBlock (k + 1) s) :=
    summable_norm_iff.mp htailNorm
  exact (summable_nat_add_iff 1).mp (by
    simpa [Nat.add_comm] using htail)

/-- Infinite phase-bearing canonical tilt trace, before adding any carrier
remainder. -/
def canonicalCriticalWeightedTiltTrace (s : ℂ) : ℂ :=
  ∑' k : ℕ, canonicalCriticalWeightedTiltBlock k s

theorem norm_canonicalCriticalWeightedTiltTrace_tail_le
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    ‖∑' k : ℕ, canonicalCriticalWeightedTiltBlock (k + 1) s‖ ≤
      canonicalTiltTailRatio * canonicalTiltFirstScale s := by
  have hnorm := summable_norm_canonicalCriticalWeightedTiltBlock_tail hs hoff
  calc
    ‖∑' k : ℕ, canonicalCriticalWeightedTiltBlock (k + 1) s‖ ≤
        ∑' k : ℕ, ‖canonicalCriticalWeightedTiltBlock (k + 1) s‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ canonicalTiltTailRatio * canonicalTiltFirstScale s := by
      apply Real.tsum_le_of_sum_range_le
      · intro k
        positivity
      · intro M
        simpa [finiteCanonicalCriticalWeightedTiltTailNorm] using
          finiteCanonicalCriticalWeightedTiltTailNorm_le_ratio_scale M hs hoff

/-- The complete center tail cannot self-cancel the first phase-bearing tilt
block.  This is a genuinely cofinal, cutoff-independent noncancellation
result, but it deliberately says nothing about the separate carrier
remainder. -/
theorem canonicalCriticalWeightedTiltTrace_ne_zero_of_strip_offCritical
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    canonicalCriticalWeightedTiltTrace s ≠ 0 := by
  have hsum := summable_canonicalCriticalWeightedTiltBlock hs hoff
  have htail := norm_canonicalCriticalWeightedTiltTrace_tail_le hs hoff
  have hscalePos := canonicalTiltFirstScale_pos hs hoff
  have hrho := canonicalTiltTailRatio_lt_one
  have hfirst := canonicalCriticalWeightedTiltBlock_zero_lower_bound hs hoff
  have htailLtFirst :
      ‖∑' k : ℕ, canonicalCriticalWeightedTiltBlock (k + 1) s‖ <
        ‖canonicalCriticalWeightedTiltBlock 0 s‖ := by
    calc
      ‖∑' k : ℕ, canonicalCriticalWeightedTiltBlock (k + 1) s‖ ≤
          canonicalTiltTailRatio * canonicalTiltFirstScale s := htail
      _ < canonicalTiltFirstScale s := by nlinarith
      _ ≤ ‖canonicalCriticalWeightedTiltBlock 0 s‖ := hfirst
  rw [canonicalCriticalWeightedTiltTrace, hsum.tsum_eq_zero_add]
  intro hzero
  have heq : canonicalCriticalWeightedTiltBlock 0 s =
      -(∑' k : ℕ, canonicalCriticalWeightedTiltBlock (k + 1) s) :=
    eq_neg_of_add_eq_zero_left hzero
  have hnorm : ‖canonicalCriticalWeightedTiltBlock 0 s‖ =
      ‖∑' k : ℕ, canonicalCriticalWeightedTiltBlock (k + 1) s‖ := by
    rw [heq, norm_neg]
  linarith

/-- Backwards-compatible short name for the cofinal tilt noncancellation
theorem. -/
theorem canonicalCriticalWeightedTiltTrace_ne_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    canonicalCriticalWeightedTiltTrace s ≠ 0 :=
  canonicalCriticalWeightedTiltTrace_ne_zero_of_strip_offCritical hs hoff

/-! ## Exact remaining carrier ledger -/

/-- Off the half-abscissa, the critical-carrier remainder blocks form a
summable series. -/
theorem summable_canonicalCriticalCarrierRemainderBlock
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    Summable (fun k : ℕ ↦ canonicalCriticalCarrierRemainderBlock k s) := by
  have hfull : Summable (fun k : ℕ ↦ realCpSaturatedBracket 3 k s) :=
    summable_realCpSaturatedBracket 3 (by norm_num) (by linarith [hs.1])
  have htilt := summable_canonicalCriticalWeightedTiltBlock hs hoff
  have hsub := hfull.sub htilt
  exact hsub.congr fun k ↦ by
    rw [realCpSaturatedBracket_three_eq_weightedTilt_add_carrierRemainder]
    ring

/-- Cofinal trace of the critical-carrier curvature and cross-term
remainder, kept separate from the weighted tilt trace. -/
def canonicalCriticalCarrierRemainderTrace (s : ℂ) : ℂ :=
  ∑' k : ℕ, canonicalCriticalCarrierRemainderBlock k s

/-- The complete bracket trace splits exactly into the nonzero tilt channel
and the independently retained carrier remainder. -/
theorem canonicalBracketTrace_eq_infiniteTilt_add_carrier
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    canonicalBracketTrace s =
      canonicalCriticalWeightedTiltTrace s +
        canonicalCriticalCarrierRemainderTrace s := by
  have htilt := summable_canonicalCriticalWeightedTiltBlock hs hoff
  have hrem := summable_canonicalCriticalCarrierRemainderBlock hs hoff
  unfold canonicalBracketTrace canonicalCriticalWeightedTiltTrace
    canonicalCriticalCarrierRemainderTrace
  calc
    ∑' k : ℕ, realCpSaturatedBracket 3 k s =
        ∑' k : ℕ, (canonicalCriticalWeightedTiltBlock k s +
          canonicalCriticalCarrierRemainderBlock k s) := by
      apply tsum_congr
      intro k
      exact
        realCpSaturatedBracket_three_eq_weightedTilt_add_carrierRemainder k s
    _ = (∑' k : ℕ, canonicalCriticalWeightedTiltBlock k s) +
        ∑' k : ℕ, canonicalCriticalCarrierRemainderBlock k s := by
      exact htilt.tsum_add hrem

/-- Exact description of the only scalar compensation mechanism left by
the tilt-tail theorem.  A hypothetical off-critical Genuine zero would force
the carrier plus the seed to cancel a provably nonzero cofinal tilt trace. -/
theorem carrierRemainder_eq_neg_one_sub_infiniteTilt_of_genuine_zero_offCritical
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    canonicalCriticalCarrierRemainderTrace s =
        -1 - canonicalCriticalWeightedTiltTrace s ∧
      canonicalCriticalWeightedTiltTrace s ≠ 0 := by
  have hledger := canonicalBracketTrace_eq_infiniteTilt_add_carrier hs hoff
  have htrace :=
    canonicalBracketTrace_eq_neg_one_of_genuineContinuation_zero hs hzero
  constructor
  · linear_combination htrace - hledger
  · exact
      canonicalCriticalWeightedTiltTrace_ne_zero_of_strip_offCritical hs hoff

/-! ## Scope guard: completeness is not carrier orthogonality -/

/-- At the boundary parameter `s = 0`, the first C3 cell (center `3`, legs
`2` and `4`) is complete and its scalar bracket nevertheless vanishes. -/
theorem completeC3Cell_zero_at_s_zero :
    realCpSaturatedBracket 3 0 0 = 0 := by
  simp [realCpSaturatedBracket, realCpPairBracket,
    CPFormal.Genuine.Cp.halfRange, realDirichletPower]
  ring

/-- The phase-bearing tilt in that complete cell is nonzero. -/
theorem completeC3Cell_weightedTilt_ne_zero_at_s_zero :
    canonicalCriticalWeightedTiltBlock 0 0 ≠ 0 := by
  unfold canonicalCriticalWeightedTiltBlock canonicalRealCpCenter
  apply mul_ne_zero
  · unfold localCriticalLineCarrier criticalLineDirichletCarrier
    apply Complex.cpow_ne_zero_iff.mpr
    left
    norm_num
  · simp only [Complex.zero_re, zero_add, criticalDisplacement]
    apply Complex.ofReal_ne_zero.mpr
    exact ne_of_lt
      (cpTilt_neg_of_neg_one_lt_delta 3 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
        (by norm_num [CPFormal.Genuine.Cp.halfRange]))

/-- The scalar carrier remainder can cancel the nonzero tilt even when the
cell contains both legs.  Hence complete-cell bookkeeping alone does not
provide carrier orthogonality. -/
theorem completeC3Cell_carrierRemainder_eq_neg_weightedTilt_at_s_zero :
    canonicalCriticalCarrierRemainderBlock 0 0 =
      -canonicalCriticalWeightedTiltBlock 0 0 := by
  have h :=
    realCpSaturatedBracket_three_eq_weightedTilt_add_carrierRemainder 0 0
  rw [completeC3Cell_zero_at_s_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

end

end CPFormal.Analytic.Cp
