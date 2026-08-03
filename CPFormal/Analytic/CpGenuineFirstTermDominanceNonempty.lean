import CPFormal.Analytic.CpGenuineFirstTermDominanceRegion
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Cota fechada da cauda da envelope pareada (teste da integral)

Prova, via o teste da integral do Mathlib (`AntitoneOn.tsum_le_integral`) e o TFC
em `Ioi` (`integral_Ioi_of_hasDerivAt_of_nonneg'`), a cota fechada

`∑ₙ (2n+3)^{-σ-1} ≤ 3^{-σ-1} + 3^{-σ}/(2σ)`   (0 < σ).

Esta é a peça analítica que faltava para tornar concreta (não-vacua) a região de
dominância do primeiro termo: com ela a envelope da cauda tem cota explícita e
computável.

Genuine First: nenhum zeta, equação funcional ou RH.
-/

open MeasureTheory Filter Set

namespace CPFormal.Analytic.Cp

noncomputable section

/-- **Cota da cauda pela integral.**  `∑ₙ (2n+3)^{-σ-1} ≤ 3^{-σ-1} + 3^{-σ}/(2σ)`. -/
theorem envelopeTail_le {σ : ℝ} (hσ : 0 < σ) :
    ∑' n : ℕ, (2 * (n : ℝ) + 3) ^ (-σ - 1) ≤
      3 ^ (-σ - 1) + 3 ^ (-σ) / (2 * σ) := by
  set f : ℝ → ℝ := fun x => (2 * x + 3) ^ (-σ - 1) with hf
  set F : ℝ → ℝ := fun x => -(2 * x + 3) ^ (-σ) / (2 * σ) with hF
  have h2σ : (2 * σ) ≠ 0 := by positivity
  -- f é antítona em [0,∞)
  have hanti : AntitoneOn f (Ici 0) := by
    intro x hx y hy hxy
    simp only [mem_Ici] at hx hy
    exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  -- derivada: F' = f em [0,∞)
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt F (f x) x := by
    intro x hx
    simp only [mem_Ici] at hx
    have hx0 : (0 : ℝ) < 2 * x + 3 := by linarith
    have hb : HasDerivAt (fun x : ℝ => 2 * x + 3) 2 x := by
      simpa using ((hasDerivAt_id x).const_mul 2).add_const 3
    have hr : HasDerivAt (fun x : ℝ => (2 * x + 3) ^ (-σ))
        (2 * (-σ) * (2 * x + 3) ^ (-σ - 1)) x :=
      hb.rpow_const (Or.inl (ne_of_gt hx0))
    have hFd := hr.const_mul (-(1 / (2 * σ)))
    have efn : (fun x : ℝ => -(1 / (2 * σ)) * (2 * x + 3) ^ (-σ)) = F := by
      funext y; rw [hF]; ring
    have eder : -(1 / (2 * σ)) * (2 * (-σ) * (2 * x + 3) ^ (-σ - 1)) = f x := by
      rw [hf]; field_simp
    rw [efn, eder] at hFd
    exact hFd
  -- f ≥ 0 em (0,∞)
  have hnonneg : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ f t := by
    intro t ht
    simp only [mem_Ioi] at ht
    rw [hf]; exact Real.rpow_nonneg (by linarith) _
  -- F → 0 no infinito
  have hg : Tendsto (fun x : ℝ => 2 * x + 3) atTop atTop := by
    apply tendsto_atTop_add_const_right
    exact Tendsto.const_mul_atTop (by norm_num) tendsto_id
  have hrpow0 : Tendsto (fun x : ℝ => (2 * x + 3) ^ (-σ)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hσ).comp hg
  have htend : Tendsto F atTop (nhds 0) := by
    have hFeq : F = fun x : ℝ => -(1 / (2 * σ)) * (2 * x + 3) ^ (-σ) := by
      funext y; rw [hF]; ring
    rw [hFeq]; simpa using hrpow0.const_mul (-(1 / (2 * σ)))
  -- valor da integral
  have hintval : ∫ x in Ioi (0 : ℝ), f x = 3 ^ (-σ) / (2 * σ) := by
    have h := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hnonneg htend
    have hF0 : F 0 = -(3 ^ (-σ)) / (2 * σ) := by rw [hF]; norm_num
    rw [h, hF0]; ring
  have hintegrable : IntegrableOn f (Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg' hderiv hnonneg htend
  -- montagem
  have hstep := hanti.tsum_le_integral hintegrable hnonneg
  rw [hintval] at hstep
  have hf0 : f 0 = 3 ^ (-σ - 1) := by rw [hf]; norm_num
  rw [hf0] at hstep
  exact hstep

/-- Helper: `c ≤ a^(m/k)` a partir de `c^k ≤ a^m`. -/
theorem le_rpow_div_of_pow_le {a c : ℝ} {m k : ℕ} (ha : 0 < a) (_hc : 0 ≤ c)
    (hk : k ≠ 0) (h : c ^ k ≤ a ^ m) : c ≤ a ^ ((m : ℝ) / k) := by
  have hpos : 0 < a ^ ((m : ℝ) / k) := Real.rpow_pos_of_pos ha _
  by_contra hlt
  rw [not_le] at hlt
  have hpk : (a ^ ((m : ℝ) / k)) ^ k = a ^ m := by
    rw [← Real.rpow_natCast (a ^ ((m : ℝ) / k)) k, ← Real.rpow_mul ha.le,
      div_mul_cancel₀ _ (by exact_mod_cast hk), Real.rpow_natCast]
  have hcontra : (a ^ ((m : ℝ) / k)) ^ k < c ^ k := pow_lt_pow_left₀ hlt hpos.le hk
  rw [hpk] at hcontra
  exact absurd h (not_le.mpr hcontra)

/-- Helper: `a^(-(m)/k) ≤ 1/c` a partir de `c^k ≤ a^m`. -/
theorem rpow_neg_div_le {a c : ℝ} {m k : ℕ} (ha : 0 < a) (hc : 0 < c)
    (hk : k ≠ 0) (h : c ^ k ≤ a ^ m) : a ^ (-(m : ℝ) / k) ≤ 1 / c := by
  have hle := le_rpow_div_of_pow_le ha hc.le hk h
  rw [neg_div, Real.rpow_neg ha.le, ← one_div]
  exact one_div_le_one_div_of_le hc hle

/-- Cota da envelope da cauda num ponto real `s = σ`: `≤ σ·3^{-σ-1} + 3^{-σ}/2`. -/
theorem pairedAltEnvelopeTail_ofReal_le {σ : ℝ} (hσ : 0 < σ) :
    pairedAltEnvelopeTail ((σ : ℝ) : ℂ) ≤ σ * 3 ^ (-σ - 1) + 3 ^ (-σ) / 2 := by
  rw [pairedAltEnvelopeTail]
  have hre : ((σ : ℝ) : ℂ).re = σ := Complex.ofReal_re σ
  have hnorm : ‖((σ : ℝ) : ℂ)‖ = σ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ]
  rw [hre, hnorm]
  have h2σ : (2 * σ) ≠ 0 := by positivity
  calc σ * ∑' n : ℕ, (2 * (n : ℝ) + 3) ^ (-σ - 1)
      ≤ σ * (3 ^ (-σ - 1) + 3 ^ (-σ) / (2 * σ)) :=
        mul_le_mul_of_nonneg_left (envelopeTail_le hσ) (le_of_lt hσ)
    _ = σ * 3 ^ (-σ - 1) + 3 ^ (-σ) / 2 := by field_simp

/-- **Não-vacuidade da região.**  O ponto real `s = 4/5` é off-critical
(`Re = 4/5 ≠ 1/2`) e satisfaz a dominância do primeiro termo. -/
theorem firstTermDominanceRegion_nonempty :
    ∃ s : ℂ, s ∈ firstTermDominanceRegion ∧ s.re ≠ 1 / 2 := by
  refine ⟨((4 / 5 : ℝ) : ℂ), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [Complex.ofReal_re]; norm_num
  · rw [Complex.ofReal_re]; norm_num
  · have hbound := pairedAltEnvelopeTail_ofReal_le (σ := 4 / 5) (by norm_num)
    have e1 : (3 : ℝ) ^ (-(4 / 5 : ℝ) - 1) ≤ 1 / 7 := by
      have h := rpow_neg_div_le (a := 3) (c := 7) (m := 9) (k := 5)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rwa [show (-(4 / 5 : ℝ) - 1) = -((9 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) by push_cast; norm_num]
    have e2 : (3 : ℝ) ^ (-(4 / 5 : ℝ)) ≤ 5 / 12 := by
      have h := rpow_neg_div_le (a := 3) (c := 12 / 5) (m := 4) (k := 5)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rw [show (1 : ℝ) / (12 / 5) = 5 / 12 by norm_num] at h
      rwa [show (-(4 / 5 : ℝ)) = -((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) by push_cast; norm_num]
    have e3 : (2 : ℝ) ^ (-(4 / 5 : ℝ)) ≤ 3 / 5 := by
      have h := rpow_neg_div_le (a := 2) (c := 5 / 3) (m := 4) (k := 5)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      rw [show (1 : ℝ) / (5 / 3) = 3 / 5 by norm_num] at h
      rwa [show (-(4 / 5 : ℝ)) = -((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) by push_cast; norm_num]
    rw [Complex.ofReal_re]
    calc pairedAltEnvelopeTail ((4 / 5 : ℝ) : ℂ)
        ≤ (4 / 5) * 3 ^ (-(4 / 5 : ℝ) - 1) + 3 ^ (-(4 / 5 : ℝ)) / 2 := hbound
      _ < 1 - 2 ^ (-(4 / 5 : ℝ)) := by nlinarith [e1, e2, e3]
  · rw [Complex.ofReal_re]; norm_num

/-- **Ponto off-critical incondicional.**  Existe `s` no strip, com `Re(s) ≠ 1/2`,
onde `genuineContinuation s ≠ 0` — o primeiro zero-free off-critical nativo. -/
theorem exists_offCritical_genuineContinuation_ne_zero :
    ∃ s : ℂ, s ∈ genuineCriticalStrip ∧ s.re ≠ 1 / 2 ∧ genuineContinuation s ≠ 0 := by
  obtain ⟨s, hs, hoff⟩ := firstTermDominanceRegion_nonempty
  exact ⟨s, hs.1, hoff, genuineContinuation_ne_zero_on_firstTermDominanceRegion hs⟩

end

end CPFormal.Analytic.Cp
