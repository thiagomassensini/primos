import CPFormal.Analytic.CpPairedGenuineBridgeIdentity

/-!
# Native paired Genuine target and the bridge identity

This module defines, natively inside `primos`, the paired Genuine target used by
the coercive `book-cash` route (historically `genuineCentralContinuationC2` in the
`formalizacao_C2` repository), and proves that on the open critical strip it is
exactly the explicit nowhere-vanishing factor `C(s) = pairedBridgeFactor s`
times the canonical `genuineContinuation`.

As a corollary the two objects share the same zeros on the strip, which is the
adapter connecting the coercive route to the canonical Genuine of the main
development.
-/

open Complex

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Native paired Genuine target: `2 · (q²/(1-q)) · ((1-2^{-s})/(1-2^{1-s})) · P`,
with `q = pairedBridgeRatio s = 2^{-1-s}` and `P = pairedAltChannel s`.  This is
the `primos`-native form of `genuineCentralContinuationC2`. -/
def genuineCentralContinuationC2 (s : ℂ) : ℂ :=
  2 * (pairedBridgeRatio s ^ 2 / (1 - pairedBridgeRatio s)) *
    ((1 - (2 : ℂ) ^ (-s)) / (1 - (2 : ℂ) ^ (1 - s))) *
    pairedAltChannel s

/-- The paired Genuine target factors, on the strip, as the explicit
nowhere-vanishing bridge factor times the canonical Genuine continuation. -/
theorem genuineCentralContinuationC2_eq
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    genuineCentralContinuationC2 s = pairedBridgeFactor s * genuineContinuation s := by
  have hq_ne : 1 - pairedBridgeRatio s ≠ 0 := one_sub_pairedBridgeRatio_ne_zero hs.1
  have hden_ne : (1 : ℂ) - (2 : ℂ) ^ (1 - s) ≠ 0 :=
    one_sub_two_cpow_one_sub_ne_zero hs
  have hq : pairedBridgeRatio s = (2 : ℂ) ^ (-s) / 2 := by
    have hneg1 : (2 : ℂ) ^ (-1 : ℂ) = 2⁻¹ := by
      rw [Complex.cpow_neg, Complex.cpow_one]
    rw [pairedBridgeRatio, show (-1 - s : ℂ) = (-s) + (-1) by ring,
      Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0), hneg1, div_eq_mul_inv]
  have h1s : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
    rw [show (1 - s : ℂ) = 1 + (-s) by ring,
      Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_one]
  rw [genuineCentralContinuationC2, pairedBridgeFactor,
    pairedAltChannel_eq_genuineContinuation hs, hq, h1s]
  rw [hq] at hq_ne
  rw [h1s] at hden_ne
  field_simp

/-- Native zero-equivalence: the paired Genuine target and the canonical Genuine
continuation vanish at exactly the same points of the strip. -/
theorem genuineCentralContinuationC2_eq_zero_iff
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    genuineCentralContinuationC2 s = 0 ↔ genuineContinuation s = 0 := by
  rw [genuineCentralContinuationC2_eq hs]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (pairedBridgeFactor_ne_zero hs)
  · intro h; rw [h, mul_zero]

end

end CPFormal.Analytic.Cp
