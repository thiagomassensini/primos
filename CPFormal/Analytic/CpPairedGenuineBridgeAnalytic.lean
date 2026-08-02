import CPFormal.Analytic.CpPairedGenuineBridge

/-!
# Analytic input for the paired Genuine bridge

The paired odd–even channel converges on the open right half-plane because the
adjacent cancellation gives each term the decay of a single derivative step.
This module proves the key mean-value bound

`‖pairedAltTerm s n‖ ≤ ‖s‖ · (2n+1)^(-re s - 1)`

and the summability of the dominating envelope on `re s > 0`.  These feed the
Weierstrass `M`-test and the holomorphy of the limit developed downstream.
-/

open Complex

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Mean-value bound for a single paired term: adjacent cancellation contributes
one derivative step of decay. -/
theorem norm_pairedAltTerm_le {s : ℂ} (hs0 : s ≠ 0) (hs : 0 < s.re) (n : ℕ) :
    ‖pairedAltTerm s n‖ ≤ ‖s‖ * (2 * (n : ℝ) + 1) ^ (-s.re - 1) := by
  have hr : (-s) ≠ 0 := neg_ne_zero.mpr hs0
  set a : ℝ := 2 * (n : ℝ) + 1 with ha_def
  set b : ℝ := 2 * (n : ℝ) + 2 with hb_def
  have ha0 : (0 : ℝ) < a := by rw [ha_def]; positivity
  have hab : a ≤ b := by rw [ha_def, hb_def]; linarith
  set F : ℝ → ℂ := fun t => (t : ℂ) ^ (-s) with hF_def
  have hderiv : ∀ x ∈ Set.Icc a b, HasDerivAt F (-s * (x : ℂ) ^ (-s - 1)) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le ha0 hx.1)
    have h := hasDerivAt_ofReal_cpow_const hx0 hr
    simpa [hF_def, sub_eq_add_neg] using h
  have hdiff : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ F x :=
    fun x hx => (hderiv x hx).differentiableAt
  set C : ℝ := ‖s‖ * a ^ (-s.re - 1) with hC_def
  have hbound : ∀ x ∈ Set.Icc a b, ‖deriv F x‖ ≤ C := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
    rw [(hderiv x hx).deriv, norm_mul, norm_neg]
    have hnx : ‖(x : ℂ) ^ (-s - 1)‖ = x ^ (-s.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      congr 1
    rw [hnx, hC_def]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg s)
    exact Real.rpow_le_rpow_of_nonpos ha0 hx.1 (by linarith)
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
    (convex_Icc a b) (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
  have hba : ‖b - a‖ = 1 := by
    rw [hb_def, ha_def, show (2 * (n : ℝ) + 2) - (2 * (n : ℝ) + 1) = 1 by ring]
    norm_num
  rw [hba, mul_one] at hmvt
  have hpt : pairedAltTerm s n = F a - F b := by
    simp only [pairedAltTerm, hF_def, ha_def, hb_def]
    push_cast
    ring
  rw [hpt, show F a - F b = -(F b - F a) by ring, norm_neg]
  exact hmvt

/-- The dominating envelope is summable on the open right half-plane. -/
theorem summable_pairedAltEnvelope {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun n : ℕ => (2 * (n : ℝ) + 1) ^ (-δ - 1)) := by
  have hbase : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-δ - 1)) := by
    have h := (Real.summable_one_div_nat_rpow (p := δ + 1)).mpr (by linarith)
    have hshift : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (δ + 1)) := by
      have hc := h.comp_injective (add_left_injective 1)
      refine hc.congr (fun n => ?_)
      simp [Nat.cast_add, Nat.cast_one]
    refine hshift.congr (fun n => ?_)
    rw [one_div, ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
    congr 1
    ring
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hbase
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : ((n : ℝ) + 1) ≤ 2 * (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  exact Real.rpow_le_rpow_of_nonpos h1 h2 (by linarith)

/-- The paired odd–even channel is holomorphic on the open right half-plane. -/
theorem analyticOnNhd_pairedAltChannel :
    AnalyticOnNhd ℂ pairedAltChannel {s : ℂ | 0 < s.re} := by
  refine DifferentiableOn.analyticOnNhd ?_
    (isOpen_lt continuous_const Complex.continuous_re)
  intro s₀ hs₀
  have hs₀re : 0 < s₀.re := hs₀
  set δ : ℝ := s₀.re / 2 with hδ_def
  have hδpos : 0 < δ := by rw [hδ_def]; linarith
  set U : Set ℂ := Metric.ball s₀ δ with hU_def
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hs₀U : s₀ ∈ U := Metric.mem_ball_self hδpos
  set R : ℝ := ‖s₀‖ + δ with hR_def
  have hballRe : ∀ w ∈ U, δ ≤ w.re := by
    intro w hw
    rw [hU_def, Metric.mem_ball, dist_eq_norm] at hw
    have hre : |w.re - s₀.re| ≤ ‖w - s₀‖ := by
      calc |w.re - s₀.re| = |(w - s₀).re| := by rw [Complex.sub_re]
        _ ≤ ‖w - s₀‖ := Complex.abs_re_le_norm _
    have hlt : |w.re - s₀.re| < δ := lt_of_le_of_lt hre hw
    have := (abs_lt.mp hlt).1
    rw [hδ_def] at this ⊢; linarith
  have hballNorm : ∀ w ∈ U, ‖w‖ ≤ R := by
    intro w hw
    rw [hU_def, Metric.mem_ball, dist_eq_norm] at hw
    have htri : ‖w‖ ≤ ‖s₀‖ + ‖w - s₀‖ := by
      have h := norm_add_le s₀ (w - s₀)
      simpa using h
    rw [hR_def]; linarith [le_of_lt hw]
  have hdiffU : DifferentiableOn ℂ (fun w => ∑' n : ℕ, pairedAltTerm w n) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (u := fun n => R * (2 * (n : ℝ) + 1) ^ (-δ - 1)) ?_ ?_ hUopen ?_
    · exact (summable_pairedAltEnvelope hδpos).mul_left R
    · intro n
      have h1 : ((2 * n + 1 : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast (show (2 * n + 1 : ℕ) ≠ 0 by omega)
      have h2 : ((2 * n + 2 : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast (show (2 * n + 2 : ℕ) ≠ 0 by omega)
      have hd : Differentiable ℂ (fun w : ℂ => pairedAltTerm w n) := by
        unfold pairedAltTerm
        fun_prop (disch := first | exact h1 | exact h2)
      exact hd.differentiableOn
    · intro n w hw
      have hwre : δ ≤ w.re := hballRe w hw
      have hwre0 : 0 < w.re := lt_of_lt_of_le hδpos hwre
      have hw0 : w ≠ 0 := by
        intro h; rw [h] at hwre0; simp at hwre0
      have hbase : (1 : ℝ) ≤ 2 * (n : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      refine (norm_pairedAltTerm_le hw0 hwre0 n).trans ?_
      calc
        ‖w‖ * (2 * (n : ℝ) + 1) ^ (-w.re - 1)
            ≤ R * (2 * (n : ℝ) + 1) ^ (-w.re - 1) := by
              apply mul_le_mul_of_nonneg_right (hballNorm w hw)
              positivity
        _ ≤ R * (2 * (n : ℝ) + 1) ^ (-δ - 1) := by
              apply mul_le_mul_of_nonneg_left _ (by rw [hR_def]; positivity)
              exact Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  have hdiffU' : DifferentiableOn ℂ pairedAltChannel U := hdiffU
  exact (hdiffU'.differentiableAt (hUopen.mem_nhds hs₀U)).differentiableWithinAt

end

end CPFormal.Analytic.Cp
