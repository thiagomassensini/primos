import CPFormal.Analytic.CpGenuineFirstTermDominanceNonempty

/-!
# Fronteira esquerda no eixo real: zero-free em todo `(0, 1)`

No eixo real (`t = 0`, `s = σ`), cada termo pareado é estritamente positivo:
`(2n+1)^{-σ} - (2n+2)^{-σ} > 0` para `σ > 0`, pois `x ↦ x^{-σ}` é decrescente.
Logo `pairedAltChannel σ` é uma soma de reais positivos, portanto positiva, e
`genuineContinuation σ ≠ 0`.

Isto resolve a fronteira esquerda **no eixo real**: todo `σ ∈ (0, 1)` — em
particular toda a semifaixa off-critical `(1/2, 1)` e também `(0, 1/2)` — é
zero-free, sem necessidade de estimativa de dominância.  O refinamento das
estimativas fica reservado ao caso off-axis (`t ≠ 0`), onde as fases podem
cancelar.

Genuine First: nenhum zeta, equação funcional ou RH.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-- No eixo real, cada termo pareado é estritamente positivo. -/
theorem pairedAltTerm_ofReal_pos {σ : ℝ} (h0 : 0 < σ) (n : ℕ) :
    0 < (2 * (n : ℝ) + 1) ^ (-σ) - (2 * (n : ℝ) + 2) ^ (-σ) := by
  have h := (Real.rpow_lt_rpow_iff_of_neg
    (show (0 : ℝ) < 2 * (n : ℝ) + 2 by positivity)
    (show (0 : ℝ) < 2 * (n : ℝ) + 1 by positivity)
    (show -σ < 0 by linarith)).2 (by linarith)
  linarith

/-- No eixo real, o termo pareado complexo é o real positivo correspondente. -/
theorem pairedAltTerm_ofReal_eq {σ : ℝ} (n : ℕ) :
    pairedAltTerm ((σ : ℝ) : ℂ) n
      = (((2 * (n : ℝ) + 1) ^ (-σ) - (2 * (n : ℝ) + 2) ^ (-σ) : ℝ) : ℂ) := by
  rw [pairedAltTerm, Complex.ofReal_sub,
    Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ) + 1),
    Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ) + 2),
    Complex.ofReal_neg]
  push_cast
  ring_nf

/-- **Fronteira esquerda no eixo real.**  Para todo `σ ∈ (0, 1)`,
`genuineContinuation σ ≠ 0` — a soma pareada é positiva por termos. -/
theorem genuineContinuation_ofReal_ne_zero {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    genuineContinuation ((σ : ℝ) : ℂ) ≠ 0 := by
  have hstrip : ((σ : ℝ) : ℂ) ∈ genuineCriticalStrip :=
    ⟨by rw [Complex.ofReal_re]; exact h0, by rw [Complex.ofReal_re]; exact h1⟩
  have hs0 : ((σ : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; linarith
  have hsre : 0 < ((σ : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; exact h0
  set g : ℕ → ℝ := fun n => (2 * (n : ℝ) + 1) ^ (-σ) - (2 * (n : ℝ) + 2) ^ (-σ) with hg
  have hpos : ∀ n, 0 < g n := fun n => pairedAltTerm_ofReal_pos h0 n
  have hnorm_eq : ∀ n, ‖pairedAltTerm ((σ : ℝ) : ℂ) n‖ = g n := by
    intro n
    rw [pairedAltTerm_ofReal_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos n)]
  have hsummable_g : Summable g :=
    (summable_norm_pairedAltTerm hs0 hsre).congr hnorm_eq
  have hchannel : pairedAltChannel ((σ : ℝ) : ℂ) = ((∑' n, g n : ℝ) : ℂ) := by
    rw [pairedAltChannel, Complex.ofReal_tsum]
    exact tsum_congr (fun n => pairedAltTerm_ofReal_eq n)
  rw [Ne, ← pairedAltChannel_eq_zero_iff_genuineContinuation hstrip, hchannel,
    Complex.ofReal_eq_zero]
  have : 0 < ∑' n, g n := hsummable_g.tsum_pos (fun n => (hpos n).le) 0 (hpos 0)
  linarith

end

end CPFormal.Analytic.Cp
