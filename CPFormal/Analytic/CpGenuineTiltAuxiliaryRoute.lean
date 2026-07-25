import CPFormal.Analytic.CpGenuineTiltTailDomination

/-!
# Auxiliary no-cancellation route for the Genuine tilt

This module freezes the first-block-versus-tail strategy as an explicitly
auxiliary route.  It records two independent quantitative certificates:

1. domination of the phase-bearing tilt tail by the first tilt block;
2. a directional or norm bound preventing the carrier remainder from erasing
   the already nonzero tilt trace.

No instance of either global certificate is declared.  In particular, these
lemmas do not identify the tilt-only trace with `genuineContinuation`; the
exact product-rule ledger still contains the carrier remainder.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Uniform finite-cutoff form of the first-block domination obligation. -/
def CanonicalCriticalTiltFirstBlockDominatesAt (s : ℂ) : Prop :=
  ∀ M : ℕ,
    finiteCanonicalCriticalWeightedTiltTailNorm M s <
      ‖canonicalCriticalWeightedTiltBlock 0 s‖

/-- A first-block domination certificate prevents cancellation in every
nonempty finite phase-bearing tilt trace. -/
theorem finiteCanonicalCriticalWeightedTiltTrace_ne_zero_of_firstBlockCertificate
    {s : ℂ} (hdom : CanonicalCriticalTiltFirstBlockDominatesAt s)
    (M : ℕ) :
    finiteCanonicalCriticalWeightedTiltTrace (M + 1) s ≠ 0 :=
  finiteCanonicalCriticalWeightedTiltTrace_ne_zero_of_first_dominates
    M s (hdom M)

/-- A positive projection onto the tilt direction prevents a complex sum from
vanishing.  This criterion is weaker than requiring the remainder norm to be
smaller than the tilt norm. -/
theorem complex_add_ne_zero_of_conj_mul_add_re_pos
    (tilt remainder : ℂ)
    (hprojection :
      0 < ((starRingEnd ℂ) tilt * (tilt + remainder)).re) :
    tilt + remainder ≠ 0 := by
  intro hzero
  rw [hzero, mul_zero] at hprojection
  norm_num at hprojection

/-- Directional finite-cutoff certificate for the carrier remainder. -/
def CanonicalCriticalCarrierRemainderProjectionPositiveAt
    (M : ℕ) (s : ℂ) : Prop :=
  0 <
    ((starRingEnd ℂ) (finiteCanonicalCriticalWeightedTiltTrace M s) *
      (finiteCanonicalCriticalWeightedTiltTrace M s +
        finiteCanonicalCriticalCarrierRemainderTrace M s)).re

/-- Under the directional certificate, the complete canonical bracket trace is
nonzero.  The proof uses the exact product-rule ledger, not an identification
of the remainder with zero. -/
theorem finiteCanonicalBracketTrace_ne_zero_of_remainderProjectionPositive
    (M : ℕ) (s : ℂ)
    (hprojection :
      CanonicalCriticalCarrierRemainderProjectionPositiveAt M s) :
    finiteCanonicalBracketTrace M s ≠ 0 := by
  rw [finiteCanonicalBracketTrace_eq_weightedTilt_add_carrierRemainder]
  exact complex_add_ne_zero_of_conj_mul_add_re_pos
    (finiteCanonicalCriticalWeightedTiltTrace M s)
    (finiteCanonicalCriticalCarrierRemainderTrace M s)
    hprojection

/-- The stronger but elementary norm firewall: if the complete carrier
remainder is shorter than the tilt trace, exact cancellation is impossible. -/
theorem finiteCanonicalBracketTrace_ne_zero_of_remainder_norm_lt_tilt
    (M : ℕ) (s : ℂ)
    (hrem :
      ‖finiteCanonicalCriticalCarrierRemainderTrace M s‖ <
        ‖finiteCanonicalCriticalWeightedTiltTrace M s‖) :
    finiteCanonicalBracketTrace M s ≠ 0 := by
  rw [finiteCanonicalBracketTrace_eq_weightedTilt_add_carrierRemainder]
  intro hzero
  have heq :
      finiteCanonicalCriticalWeightedTiltTrace M s =
        -finiteCanonicalCriticalCarrierRemainderTrace M s :=
    eq_neg_of_add_eq_zero_left hzero
  have hnorm :
      ‖finiteCanonicalCriticalWeightedTiltTrace M s‖ =
        ‖finiteCanonicalCriticalCarrierRemainderTrace M s‖ := by
    rw [heq, norm_neg]
  linarith

end

end CPFormal.Analytic.Cp
