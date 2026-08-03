import CPFormal.Analytic.CpGenuineFirstTermDominanceNonempty

/-!
# Extensão a um intervalo: `genuineContinuation ≠ 0` em toda a faixa `[4/5, 1)`

A não-vacuidade dava um ponto (`4/5`).  Aqui, cotas monótonas de `rpow` estendem
o resultado a **toda** a faixa real `σ ∈ [4/5, 1)`: para `σ ≥ 4/5`,

* `3^{-σ-1} ≤ 3^{-9/5} ≤ 1/7`,   `3^{-σ} ≤ 3^{-4/5} ≤ 5/12`,   `2^{-σ} ≤ 2^{-4/5} ≤ 3/5`,

logo a envelope da cauda `≤ 1/7 + 5/24 = 295/840 < 336/840 ≤ 1 - 2^{-σ}`.

Assim `genuineContinuation` é não nula em todo o segmento real `[4/5, 1)`, um
intervalo off-critical inteiro sem zeros.

Genuine First: nenhum zeta, equação funcional ou RH.
-/

namespace CPFormal.Analytic.Cp

/-- `3^{-9/5} ≤ 1/7`. -/
theorem rpow_bound_three_nine_fifths : (3 : ℝ) ^ (-(9 : ℝ) / 5) ≤ 1 / 7 := by
  have h := rpow_neg_div_le (a := 3) (c := 7) (m := 9) (k := 5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rwa [show (-(9 : ℝ) / 5) = -((9 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) by push_cast; norm_num]

/-- `3^{-4/5} ≤ 5/12`. -/
theorem rpow_bound_three_four_fifths : (3 : ℝ) ^ (-(4 : ℝ) / 5) ≤ 5 / 12 := by
  have h := rpow_neg_div_le (a := 3) (c := 12 / 5) (m := 4) (k := 5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) / (12 / 5) = 5 / 12 by norm_num] at h
  rwa [show (-(4 : ℝ) / 5) = -((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) by push_cast; norm_num]

/-- `2^{-4/5} ≤ 3/5`. -/
theorem rpow_bound_two_four_fifths : (2 : ℝ) ^ (-(4 : ℝ) / 5) ≤ 3 / 5 := by
  have h := rpow_neg_div_le (a := 2) (c := 5 / 3) (m := 4) (k := 5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) / (5 / 3) = 3 / 5 by norm_num] at h
  rwa [show (-(4 : ℝ) / 5) = -((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) by push_cast; norm_num]

/-- **Não-anulação em toda a faixa `[4/5, 1)`.**  Cotas monótonas de `rpow`
estendem a dominância do primeiro termo a um intervalo real inteiro. -/
theorem genuineContinuation_ne_zero_on_realInterval {σ : ℝ}
    (hlo : 4 / 5 ≤ σ) (hhi : σ < 1) :
    genuineContinuation ((σ : ℝ) : ℂ) ≠ 0 := by
  have hσ0 : 0 < σ := by linarith
  apply genuineContinuation_ne_zero_on_firstTermDominanceRegion
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Complex.ofReal_re]; exact hσ0
  · rw [Complex.ofReal_re]; exact hhi
  · rw [Complex.ofReal_re]
    have hbound := pairedAltEnvelopeTail_ofReal_le hσ0
    have m1 : (3 : ℝ) ^ (-σ - 1) ≤ 1 / 7 :=
      le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
        rpow_bound_three_nine_fifths
    have m2 : (3 : ℝ) ^ (-σ) ≤ 5 / 12 :=
      le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
        rpow_bound_three_four_fifths
    have m3 : (2 : ℝ) ^ (-σ) ≤ 3 / 5 :=
      le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
        rpow_bound_two_four_fifths
    have hpos1 : (0 : ℝ) ≤ 3 ^ (-σ - 1) := Real.rpow_nonneg (by norm_num) _
    calc pairedAltEnvelopeTail ((σ : ℝ) : ℂ)
        ≤ σ * 3 ^ (-σ - 1) + 3 ^ (-σ) / 2 := hbound
      _ ≤ 1 * (1 / 7) + (5 / 12) / 2 := by
          apply add_le_add
          · exact mul_le_mul (le_of_lt hhi) m1 hpos1 (by norm_num)
          · linarith [m2]
      _ < 1 - 2 ^ (-σ) := by linarith [m3]

/-- Corolário off-critical: todo ponto real de `(1/2, 1)` a partir de `4/5` é
zero-free e fora da linha crítica. -/
theorem genuineContinuation_ne_zero_and_offCritical_on_realInterval {σ : ℝ}
    (hlo : 4 / 5 ≤ σ) (hhi : σ < 1) :
    ((σ : ℝ) : ℂ).re ≠ 1 / 2 ∧ genuineContinuation ((σ : ℝ) : ℂ) ≠ 0 := by
  refine ⟨?_, genuineContinuation_ne_zero_on_realInterval hlo hhi⟩
  rw [Complex.ofReal_re]; linarith

end CPFormal.Analytic.Cp
