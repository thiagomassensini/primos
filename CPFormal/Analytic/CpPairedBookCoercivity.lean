import CPFormal.Analytic.CpPairedGenuineBridge

/-!
# Coercive kernel of the paired book-cash route

This module isolates the reusable *analytic heart* of the coercive (Livro-Caixa)
route: the pieces that force a scalar decomposition `T = K + E` to stay away from
zero after the scalar compression, independently of height.  None of the results
here use interval certificates or numerics; they are exact, phase-uniform
inequalities.

The four bricks are:

* `no_zero_of_dominance` — the abstract dominance consumer: if the principal part
  dominates the residual in norm, the total cannot vanish.
* `quartet_norm_lower` — the **sharp, phase-uniform** lower bound for the quartet
  factor `1 + q + q^2 + q^3`.  Its minimum over all phases of `q` is attained at
  `q = -‖q‖`, giving `(1 - ‖q‖)(1 + ‖q‖^2)`; crucially it does not degrade with
  the imaginary part.
* `verticalDebt_norm_le` — the vertical-debt upper bound `‖q^6/(1-q)‖ ≤
  ‖q‖^6/(1-‖q‖)`.
* `structural_gap` — the structural surplus `5·(r^6/(1-r)) < r^2(1-r)(1+r^2)` for
  `0 < r < 1/2`, i.e. the debt is beaten by the quartet floor with margin.

The bridge variable `q = pairedBridgeRatio s` satisfies `‖q‖ < 1/2` on the open
right half-plane (`norm_pairedBridgeRatio_lt_half`), so all four bricks apply
there simultaneously.
-/

open Complex

namespace CPFormal.Analytic.Cp

/-- **Abstract dominance consumer.**  If `F = K + E`, the principal part `K` has
norm at least `L`, the residual `E` has norm at most `R`, and `R < L`, then the
total cannot vanish.  This is the coercivity "after the scalar compression". -/
theorem no_zero_of_dominance {F K E : ℂ} {L R : ℝ}
    (hFE : F = K + E) (hK : L ≤ ‖K‖) (hE : ‖E‖ ≤ R) (hLR : R < L) : F ≠ 0 := by
  intro hF
  have hKE : K = -E := by
    have hz : K + E = 0 := by rw [← hFE, hF]
    linear_combination hz
  have hnorm : ‖K‖ = ‖E‖ := by rw [hKE, norm_neg]
  rw [hnorm] at hK
  linarith

/-- **Sharp phase-uniform quartet floor (squared form).**  For every `q`,
`((1 - ‖q‖)(1 + ‖q‖^2))^2 ≤ ‖1 + q + q^2 + q^3‖^2`.  The bound is exact: it is
attained at `q = -‖q‖`.  The proof is the factorisation identity
`normSq = ((1-r)(1+r^2))^2 + (2a+2r)·bracket` with both extra factors nonnegative,
where `a = q.re`, `r = ‖q‖`. -/
theorem quartet_normSq_lower (q : ℂ) :
    ((1 - ‖q‖) * (1 + ‖q‖ ^ 2)) ^ 2 ≤ Complex.normSq (1 + q + q ^ 2 + q ^ 3) := by
  have hr0 : 0 ≤ ‖q‖ := norm_nonneg q
  have hrsq : ‖q‖ ^ 2 = q.re ^ 2 + q.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hare : |q.re| ≤ ‖q‖ := Complex.abs_re_le_norm q
  have hnorm : Complex.normSq (1 + q + q ^ 2 + q ^ 3)
      = (1 + q.re + (q.re ^ 2 - q.im ^ 2) + (q.re ^ 3 - 3 * q.re * q.im ^ 2)) ^ 2
        + (q.im + 2 * q.re * q.im + (3 * q.re ^ 2 * q.im - q.im ^ 3)) ^ 2 := by
    rw [Complex.normSq_apply]
    simp only [pow_two, pow_three, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im]
    ring
  rw [hnorm]
  have hfac1 : 0 ≤ 2 * q.re + 2 * ‖q‖ := by
    have := (abs_le.mp hare).1; linarith
  have hfac2 : 0 ≤ (2 * q.re) ^ 2 + (1 - ‖q‖) ^ 2 * (2 * q.re)
      + (1 - ‖q‖) ^ 2 * (1 + ‖q‖ ^ 2) := by
    nlinarith [sq_nonneg (4 * q.re + (1 - ‖q‖) ^ 2),
      mul_nonneg (sq_nonneg (1 - ‖q‖)) hr0,
      mul_nonneg (sq_nonneg (1 - ‖q‖)) (mul_nonneg hr0 hr0),
      sq_nonneg (1 - ‖q‖)]
  have hid : (1 + q.re + (q.re ^ 2 - q.im ^ 2) + (q.re ^ 3 - 3 * q.re * q.im ^ 2)) ^ 2
        + (q.im + 2 * q.re * q.im + (3 * q.re ^ 2 * q.im - q.im ^ 3)) ^ 2
      = ((1 - ‖q‖) * (1 + ‖q‖ ^ 2)) ^ 2
        + (2 * q.re + 2 * ‖q‖)
          * ((2 * q.re) ^ 2 + (1 - ‖q‖) ^ 2 * (2 * q.re)
              + (1 - ‖q‖) ^ 2 * (1 + ‖q‖ ^ 2)) := by
    linear_combination (-q.re ^ 4 - 2 * q.re ^ 3 - 2 * q.re ^ 2 * q.im ^ 2
      - q.re ^ 2 * ‖q‖ ^ 2 - 3 * q.re ^ 2 - 2 * q.re * q.im ^ 2
      - 2 * q.re * ‖q‖ ^ 2 + 4 * q.re - q.im ^ 4 - q.im ^ 2 * ‖q‖ ^ 2
      + q.im ^ 2 - ‖q‖ ^ 4 + ‖q‖ ^ 2 + 1) * hrsq
  rw [hid]
  nlinarith [mul_nonneg hfac1 hfac2]

/-- **Sharp phase-uniform quartet floor (norm form).**  For `‖q‖ ≤ 1`,
`(1 - ‖q‖)(1 + ‖q‖^2) ≤ ‖1 + q + q^2 + q^3‖`. -/
theorem quartet_norm_lower (q : ℂ) (hq : ‖q‖ ≤ 1) :
    (1 - ‖q‖) * (1 + ‖q‖ ^ 2) ≤ ‖1 + q + q ^ 2 + q ^ 3‖ := by
  have hL : 0 ≤ (1 - ‖q‖) * (1 + ‖q‖ ^ 2) :=
    mul_nonneg (by linarith) (by positivity)
  have hsq : ((1 - ‖q‖) * (1 + ‖q‖ ^ 2)) ^ 2 ≤ ‖1 + q + q ^ 2 + q ^ 3‖ ^ 2 := by
    conv_rhs => rw [Complex.sq_norm]
    exact quartet_normSq_lower q
  have h1 : (1 - ‖q‖) * (1 + ‖q‖ ^ 2)
      = Real.sqrt (((1 - ‖q‖) * (1 + ‖q‖ ^ 2)) ^ 2) := (Real.sqrt_sq hL).symm
  have h2 : ‖1 + q + q ^ 2 + q ^ 3‖
      = Real.sqrt (‖1 + q + q ^ 2 + q ^ 3‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
  rw [h1, h2]
  exact Real.sqrt_le_sqrt hsq

/-- **Vertical-debt upper bound.**  For `‖q‖ < 1`,
`‖q^6/(1-q)‖ ≤ ‖q‖^6/(1-‖q‖)`. -/
theorem verticalDebt_norm_le (q : ℂ) (hq : ‖q‖ < 1) :
    ‖q ^ 6 / (1 - q)‖ ≤ ‖q‖ ^ 6 / (1 - ‖q‖) := by
  have hden : 0 < 1 - ‖q‖ := by linarith
  have hb : 1 - ‖q‖ ≤ ‖1 - q‖ := by simpa using norm_sub_norm_le (1 : ℂ) q
  have hinv : 1 / ‖1 - q‖ ≤ 1 / (1 - ‖q‖) := one_div_le_one_div_of_le hden hb
  rw [norm_div, norm_pow]
  calc ‖q‖ ^ 6 / ‖1 - q‖ = ‖q‖ ^ 6 * (1 / ‖1 - q‖) := by ring
    _ ≤ ‖q‖ ^ 6 * (1 / (1 - ‖q‖)) := mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = ‖q‖ ^ 6 / (1 - ‖q‖) := by ring

/-- **Structural surplus.**  For `0 < r < 1/2` the quartet floor beats five times
the vertical debt, via `(1-r)^2(1+r^2) - 5r^4 = (1-2r)(1+2r^2+2r^3) > 0`. -/
theorem structural_gap (r : ℝ) (h0 : 0 < r) (h1 : r < 1 / 2) :
    5 * (r ^ 6 / (1 - r)) < r ^ 2 * (1 - r) * (1 + r ^ 2) := by
  have hden : 0 < 1 - r := by linarith
  have hrw : 5 * (r ^ 6 / (1 - r)) = 5 * r ^ 6 / (1 - r) := by ring
  rw [hrw, div_lt_iff₀ hden]
  have key : 0 < r ^ 2 * (1 - 2 * r) * (1 + 2 * r ^ 2 + 2 * r ^ 3) :=
    mul_pos (mul_pos (pow_pos h0 2) (by linarith))
      (by nlinarith [pow_pos h0 3, sq_nonneg r])
  nlinarith [key]

/-- On the open right half-plane the bridge variable satisfies `‖q‖ < 1/2`, so the
quartet floor and the structural surplus both apply. -/
theorem norm_pairedBridgeRatio_lt_half {s : ℂ} (hs : 0 < s.re) :
    ‖pairedBridgeRatio s‖ < 1 / 2 := by
  rw [norm_pairedBridgeRatio]
  have h : (2 : ℝ) ^ (-1 - s.re) < (2 : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  rwa [Real.rpow_neg_one, show ((2 : ℝ)⁻¹) = 1 / 2 by norm_num] at h

end CPFormal.Analytic.Cp
