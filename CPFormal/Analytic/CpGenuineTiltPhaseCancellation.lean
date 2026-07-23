import CPFormal.Analytic.CpGenuineTiltProductRule

/-!
# Phase-unwound tilt detector and scalar cancellation criterion

The local product-rule ledger writes every canonical Genuine bracket block as

`weighted tilt + carrier remainder`.

The weighted tilt has a real factor of rigid sign and a nonzero critical
carrier carrying the phase.  This module removes that carrier *before* scalar
synthesis and proves that the resulting finite tilt detector is strictly
positive to the right of the half-abscissa and strictly negative to the left.
Thus the native bracket curvature detects the transverse displacement without
phase cancellation when its block provenance is retained.

For the original phase-bearing scalar tilt trace, the module also isolates a
fully explicit sufficient condition: the first block cannot be cancelled when
its norm strictly dominates the sum of the norms of all later blocks.  Proving
that analytic domination uniformly in the strip is a separate quantitative
estimate; it is not assumed as a Genuine/Green bridge.
-/

open scoped BigOperators

namespace CPFormal.Analytic.Cp

noncomputable section

/-- The nonzero critical carrier attached to the `k`-th canonical block. -/
def canonicalCriticalTiltCarrier (k : ℕ) (s : ℂ) : ℂ :=
  localCriticalLineCarrier s (canonicalRealCpCenter k) 0

/-- Every canonical critical carrier is nonzero. -/
theorem canonicalCriticalTiltCarrier_ne_zero (k : ℕ) (s : ℂ) :
    canonicalCriticalTiltCarrier k s ≠ 0 := by
  unfold canonicalCriticalTiltCarrier localCriticalLineCarrier
    criticalLineDirichletCarrier canonicalRealCpCenter
  apply (Complex.cpow_ne_zero_iff).2
  left
  norm_num
  positivity

/-- Remove the native carrier phase before summing the local tilt blocks. -/
def canonicalPhaseUnwoundTiltBlock (k : ℕ) (s : ℂ) : ℂ :=
  canonicalCriticalWeightedTiltBlock k s /
    canonicalCriticalTiltCarrier k s

/-- Phase unwinding recovers exactly the real local tilt. -/
theorem canonicalPhaseUnwoundTiltBlock_eq (k : ℕ) (s : ℂ) :
    canonicalPhaseUnwoundTiltBlock k s =
      (cpTilt 3 (criticalDisplacement s.re) (canonicalRealCpCenter k) : ℂ) := by
  unfold canonicalPhaseUnwoundTiltBlock
    canonicalCriticalWeightedTiltBlock canonicalCriticalTiltCarrier
  field_simp [canonicalCriticalTiltCarrier_ne_zero]

/-- Every canonical center lies strictly outside the radius-one camera. -/
theorem halfRange_three_lt_canonicalRealCpCenter (k : ℕ) :
    ((CPFormal.Genuine.Cp.halfRange 3 : ℕ) : ℝ) <
      canonicalRealCpCenter k := by
  unfold canonicalRealCpCenter CPFormal.Genuine.Cp.halfRange
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  norm_num
  nlinarith

/-- To the right of the half-abscissa, every phase-unwound block is positive. -/
theorem canonicalPhaseUnwoundTiltBlock_re_pos
    (k : ℕ) {s : ℂ}
    (hdelta : 0 < criticalDisplacement s.re) :
    0 < (canonicalPhaseUnwoundTiltBlock k s).re := by
  rw [canonicalPhaseUnwoundTiltBlock_eq]
  simpa using
    (cpTilt_pos_of_delta_pos 3 (by norm_num) (by norm_num)
      hdelta (halfRange_three_lt_canonicalRealCpCenter k))

/-- To the left of the half-abscissa inside `re(s)>0`, every phase-unwound
block is negative. -/
theorem canonicalPhaseUnwoundTiltBlock_re_neg
    (k : ℕ) {s : ℂ}
    (hre : 0 < s.re)
    (hdelta : criticalDisplacement s.re < 0) :
    (canonicalPhaseUnwoundTiltBlock k s).re < 0 := by
  have hdeltaLower : -1 < criticalDisplacement s.re := by
    unfold criticalDisplacement
    linarith
  rw [canonicalPhaseUnwoundTiltBlock_eq]
  simpa using
    (cpTilt_neg_of_neg_one_lt_delta 3 (by norm_num) (by norm_num)
      hdeltaLower hdelta (halfRange_three_lt_canonicalRealCpCenter k))

/-- Finite pre-compression detector obtained by unwinding every carrier before
adding the tagged blocks. -/
def finiteCanonicalPhaseUnwoundTiltTrace (M : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.range M, canonicalPhaseUnwoundTiltBlock k s

/-- The pre-compression detector is strictly positive on the right half of the
strip as soon as one block is present. -/
theorem finiteCanonicalPhaseUnwoundTiltTrace_re_pos
    {M : ℕ} (hM : 0 < M) {s : ℂ}
    (hdelta : 0 < criticalDisplacement s.re) :
    0 < (finiteCanonicalPhaseUnwoundTiltTrace M s).re := by
  unfold finiteCanonicalPhaseUnwoundTiltTrace
  simp only [map_sum]
  apply Finset.sum_pos
  · intro k hk
    exact canonicalPhaseUnwoundTiltBlock_re_pos k hdelta
  · exact ⟨0, Finset.mem_range.mpr hM⟩

/-- The pre-compression detector is strictly negative on the left half of the
strip as soon as one block is present. -/
theorem finiteCanonicalPhaseUnwoundTiltTrace_re_neg
    {M : ℕ} (hM : 0 < M) {s : ℂ}
    (hre : 0 < s.re)
    (hdelta : criticalDisplacement s.re < 0) :
    (finiteCanonicalPhaseUnwoundTiltTrace M s).re < 0 := by
  unfold finiteCanonicalPhaseUnwoundTiltTrace
  simp only [map_sum]
  apply Finset.sum_neg
  · intro k hk
    exact canonicalPhaseUnwoundTiltBlock_re_neg k hre hdelta
  · exact ⟨0, Finset.mem_range.mpr hM⟩

/-- The phase-unwound finite detector vanishes exactly on the half-abscissa. -/
theorem finiteCanonicalPhaseUnwoundTiltTrace_eq_zero_iff_re_eq_half
    {M : ℕ} (hM : 0 < M) {s : ℂ} (hre : 0 < s.re) :
    finiteCanonicalPhaseUnwoundTiltTrace M s = 0 ↔
      s.re = (1 : ℝ) / 2 := by
  constructor
  · intro hzero
    by_contra hoff
    have hdelta : criticalDisplacement s.re ≠ 0 := by
      unfold criticalDisplacement
      linarith
    rcases lt_or_gt_of_ne hdelta with hneg | hpos
    · have hsign := finiteCanonicalPhaseUnwoundTiltTrace_re_neg
        hM hre hneg
      rw [hzero] at hsign
      norm_num at hsign
    · have hsign := finiteCanonicalPhaseUnwoundTiltTrace_re_pos
        hM hpos
      rw [hzero] at hsign
      norm_num at hsign
  · intro hhalf
    unfold finiteCanonicalPhaseUnwoundTiltTrace
    apply Finset.sum_eq_zero
    intro k hk
    rw [canonicalPhaseUnwoundTiltBlock_eq]
    have hdelta : criticalDisplacement s.re = 0 := by
      unfold criticalDisplacement
      rw [hhalf]
      ring
    rw [hdelta]
    simp

/-! ## Original phase-bearing trace: exact domination firewall -/

/-- All phase-bearing weighted tilt blocks after the first one. -/
def finiteCanonicalCriticalWeightedTiltTail (M : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.range M, canonicalCriticalWeightedTiltBlock (k + 1) s

/-- Sum of their norms, the phase-independent budget relevant to the reverse
triangle inequality. -/
def finiteCanonicalCriticalWeightedTiltTailNorm (M : ℕ) (s : ℂ) : ℝ :=
  ∑ k ∈ Finset.range M, ‖canonicalCriticalWeightedTiltBlock (k + 1) s‖

/-- Split a nonempty finite weighted tilt trace into its first block and tail. -/
theorem finiteCanonicalCriticalWeightedTiltTrace_succ_eq_first_add_tail
    (M : ℕ) (s : ℂ) :
    finiteCanonicalCriticalWeightedTiltTrace (M + 1) s =
      canonicalCriticalWeightedTiltBlock 0 s +
        finiteCanonicalCriticalWeightedTiltTail M s := by
  unfold finiteCanonicalCriticalWeightedTiltTrace
    finiteCanonicalCriticalWeightedTiltTail
  rw [Finset.sum_range_succ']

/-- The norm of the complex tail is bounded by the sum of the block norms. -/
theorem norm_finiteCanonicalCriticalWeightedTiltTail_le
    (M : ℕ) (s : ℂ) :
    ‖finiteCanonicalCriticalWeightedTiltTail M s‖ ≤
      finiteCanonicalCriticalWeightedTiltTailNorm M s := by
  unfold finiteCanonicalCriticalWeightedTiltTail
    finiteCanonicalCriticalWeightedTiltTailNorm
  exact norm_sum_le _ _

/-- Quantitative no-cancellation theorem for the original phase-bearing tilt:
if the first block dominates the complete later norm budget, no arrangement of
carrier phases can make the finite trace vanish. -/
theorem finiteCanonicalCriticalWeightedTiltTrace_ne_zero_of_first_dominates
    (M : ℕ) (s : ℂ)
    (hdom : finiteCanonicalCriticalWeightedTiltTailNorm M s <
      ‖canonicalCriticalWeightedTiltBlock 0 s‖) :
    finiteCanonicalCriticalWeightedTiltTrace (M + 1) s ≠ 0 := by
  rw [finiteCanonicalCriticalWeightedTiltTrace_succ_eq_first_add_tail]
  intro hzero
  have heq : canonicalCriticalWeightedTiltBlock 0 s =
      -finiteCanonicalCriticalWeightedTiltTail M s := by
    exact eq_neg_of_add_eq_zero_left hzero
  have hnormEq : ‖canonicalCriticalWeightedTiltBlock 0 s‖ =
      ‖finiteCanonicalCriticalWeightedTiltTail M s‖ := by
    rw [heq, norm_neg]
  have htail := norm_finiteCanonicalCriticalWeightedTiltTail_le M s
  linarith

end

end CPFormal.Analytic.Cp
