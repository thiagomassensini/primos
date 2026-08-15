import CPFormal.Analytic.CpGenuineTiltTailNoncompensation
import CPFormal.Analytic.CpGenuineGreenKernelInclusion

/-!
# Exact C3 carrier-compensation gate

The complete C3 tilt tail is already known not to cancel its first center away
from the half-abscissa.  This module isolates the remaining scalar mechanism:
the seed together with the critical-carrier remainder.

First, the full cofinal tilt trace is shown to remain in the strict open
half-plane determined by its first complete center.  Second, the carrier
remainder is written both blockwise, as the two carrier increments along the
legs, and globally, as an exact closed ledger.  Finally, the statement that
the seed and carrier never cancel the tilt off the half-abscissa is proved
equivalent to strong Genuine nonvanishing in the strip.

Thus the last noncompensation statement is not obtained by deleting a tail or
by rearranging the scalar TFVD ledger.  Any proof must instead use the exact
state-level coherence that ties the carrier, endpoint, reconstructed bulk and
Green boundary form to the same geometric state.
-/

open scoped BigOperators ComplexConjugate

namespace CPFormal.Analytic.Cp

noncomputable section

/-- The real part of a complex pairing is bounded below by minus the product
of the two norms. -/
lemma re_conj_mul_ge_neg_norm_mul (a b : ℂ) :
    -‖a‖ * ‖b‖ ≤ ((starRingEnd ℂ) a * b).re := by
  have habs : |((starRingEnd ℂ) a * b).re| ≤
      ‖(starRingEnd ℂ) a * b‖ :=
    Complex.abs_re_le_norm _
  have hnorm : ‖(starRingEnd ℂ) a * b‖ = ‖a‖ * ‖b‖ := by
    rw [norm_mul]
    simp
  rw [hnorm] at habs
  linarith [neg_abs_le ((starRingEnd ℂ a * b).re)]

/-- Away from the half-abscissa, the full cofinal tilt trace has strictly
positive projection onto its first complete C3 tilt block.  This is stronger
than mere nonvanishing and uses no Genuine-zero hypothesis. -/
theorem canonicalCriticalWeightedTiltTrace_firstBlockProjection_pos
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    0 < ((starRingEnd ℂ) (canonicalCriticalWeightedTiltBlock 0 s) *
      canonicalCriticalWeightedTiltTrace s).re := by
  let first := canonicalCriticalWeightedTiltBlock 0 s
  let tail := ∑' k : ℕ, canonicalCriticalWeightedTiltBlock (k + 1) s
  have hsum := summable_canonicalCriticalWeightedTiltBlock hs hoff
  have hsplit : canonicalCriticalWeightedTiltTrace s = first + tail := by
    dsimp [first, tail]
    rw [canonicalCriticalWeightedTiltTrace, hsum.tsum_eq_zero_add]
  have htail := norm_canonicalCriticalWeightedTiltTrace_tail_le hs hoff
  have hscalePos := canonicalTiltFirstScale_pos hs hoff
  have hrho := canonicalTiltTailRatio_lt_one
  have hfirst := canonicalCriticalWeightedTiltBlock_zero_lower_bound hs hoff
  have htailLt : ‖tail‖ < ‖first‖ := by
    dsimp [tail, first]
    calc
      ‖∑' k : ℕ, canonicalCriticalWeightedTiltBlock (k + 1) s‖ ≤
          canonicalTiltTailRatio * canonicalTiltFirstScale s := htail
      _ < canonicalTiltFirstScale s := by nlinarith
      _ ≤ ‖canonicalCriticalWeightedTiltBlock 0 s‖ := hfirst
  have hcross := re_conj_mul_ge_neg_norm_mul first tail
  rw [hsplit, mul_add, Complex.add_re, Complex.conj_mul']
  rw [← Complex.ofReal_pow]
  change 0 < ‖first‖ ^ 2 + ((starRingEnd ℂ) first * tail).re
  have hfirstPos : 0 < ‖first‖ := by
    dsimp [first]
    exact lt_of_lt_of_le hscalePos hfirst
  nlinarith

/-- The critical-carrier remainder of one complete C3 cell is exactly the sum
of the two carrier increments along its legs, weighted by their transverse
profiles.  In particular it has no scalar sign forced by the central tilt. -/
theorem canonicalCriticalCarrierRemainderBlock_eq_two_leg_increment
    (k : ℕ) (s : ℂ) :
    canonicalCriticalCarrierRemainderBlock k s =
      (localCriticalLineCarrier s (canonicalRealCpCenter k) (-1) -
          localCriticalLineCarrier s (canonicalRealCpCenter k) 0) *
        complexTransversePowerProfile
          (criticalDisplacement s.re) (canonicalRealCpCenter k) (-1) +
      (localCriticalLineCarrier s (canonicalRealCpCenter k) 1 -
          localCriticalLineCarrier s (canonicalRealCpCenter k) 0) *
        complexTransversePowerProfile
          (criticalDisplacement s.re) (canonicalRealCpCenter k) 1 := by
  unfold canonicalCriticalCarrierRemainderBlock
    localCriticalCarrierCurvature localCriticalCarrierCross
    CPFormal.centeredSecondDifference
  ring_nf

/-- Exact closed form for the cofinal carrier remainder.  This identity is
valid before assuming a Genuine zero. -/
theorem canonicalCriticalCarrierRemainderTrace_closed_form
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    canonicalCriticalCarrierRemainderTrace s =
      cpChartFactor 3 s * genuineContinuation s - 1 -
        canonicalCriticalWeightedTiltTrace s := by
  have hfactor :=
    bracketedDirichletChart_eq_cpChartFactor_mul_genuineContinuation
      3 (by norm_num) (by norm_num) hs
  have hseed := bracketedDirichletChart_three_eq_one_add_trace s
  have hsplit := canonicalBracketTrace_eq_infiniteTilt_add_carrier hs hoff
  linear_combination hfactor - hseed - hsplit

/-- Closed seed-plus-carrier ledger. -/
theorem one_add_canonicalCriticalCarrierRemainderTrace_closed_form
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    1 + canonicalCriticalCarrierRemainderTrace s =
      cpChartFactor 3 s * genuineContinuation s -
        canonicalCriticalWeightedTiltTrace s := by
  rw [canonicalCriticalCarrierRemainderTrace_closed_form hs hoff]
  ring

/-- The full seed/tilt/carrier ledger is exactly the factored Genuine
continuation. -/
theorem seed_add_infiniteTilt_add_carrier_eq_factor_mul_genuine
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    1 + canonicalCriticalWeightedTiltTrace s +
        canonicalCriticalCarrierRemainderTrace s =
      cpChartFactor 3 s * genuineContinuation s := by
  rw [canonicalCriticalCarrierRemainderTrace_closed_form hs hoff]
  ring

/-- In the open strip, exact cancellation of the nonzero cofinal tilt by the
seed and carrier is equivalent to scalar Genuine vanishing. -/
theorem carrierSeed_cancels_infiniteTilt_iff_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    (1 + canonicalCriticalCarrierRemainderTrace s =
        -canonicalCriticalWeightedTiltTrace s) ↔
      genuineContinuation s = 0 := by
  rw [one_add_canonicalCriticalCarrierRemainderTrace_closed_form hs hoff]
  have hfactor : cpChartFactor 3 s ≠ 0 :=
    cpChartFactor_ne_zero_on_genuineCriticalStrip 3 (by norm_num) hs
  constructor
  · intro h
    have hprod : cpChartFactor 3 s * genuineContinuation s = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp hprod).resolve_left hfactor
  · intro hzero
    simp [hzero]

/-- Global carrier/seed noncompensation away from the half-abscissa.  This is
named as a separate proposition so its precise logical strength can be
audited. -/
def CarrierSeedDoesNotCancelInfiniteTiltOffCritical : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    s.re ≠ (1 : ℝ) / 2 →
      1 + canonicalCriticalCarrierRemainderTrace s ≠
        -canonicalCriticalWeightedTiltTrace s

/-- Scope guard: global carrier/seed noncompensation is exactly strong
Genuine nonvanishing in the strip.  It is therefore not a weaker consequence
of the scalar complete-cell ledger; a proof has to use additional exact
state-level coherence. -/
theorem carrierSeedDoesNotCancelInfiniteTiltOffCritical_iff_strongNonvanishing :
    CarrierSeedDoesNotCancelInfiniteTiltOffCritical ↔
      GenuineStrongNonvanishingInStrip := by
  constructor
  · intro h s hs hoff hzero
    exact h hs hoff
      ((carrierSeed_cancels_infiniteTilt_iff_genuine_zero hs hoff).2 hzero)
  · intro hstrong s hs hoff hcancel
    exact hstrong hs hoff
      ((carrierSeed_cancels_infiniteTilt_iff_genuine_zero hs hoff).1 hcancel)

end

end CPFormal.Analytic.Cp
