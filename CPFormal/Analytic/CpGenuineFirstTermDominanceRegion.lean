import CPFormal.Analytic.CpPairedGenuineBridgeIdentity
import CPFormal.Analytic.CpPairedBookCoercivity

/-!
# Região explícita de não-anulação: o primeiro termo pareado domina a cauda

Este módulo instancia o minorante coercivo de forma **incondicional e nativa**,
sem certificado numérico externo.  A ideia: no canal pareado

`pairedAltChannel s = ∑ₙ ((2n+1)^{-s} - (2n+2)^{-s})`,

o primeiro termo é `1 - 2^{-s}`, com piso `‖1 - 2^{-s}‖ ≥ 1 - 2^{-σ}`, e a cauda
tem o decaimento de uma diferença adjacente, majorada pela envelope de valor médio
`‖s‖ · (2n+3)^{-σ-1}` (`norm_pairedAltTerm_le`).  Onde a envelope da cauda é
estritamente menor que o piso do primeiro termo, o consumidor de dominância
(`no_zero_of_dominance`) garante `pairedAltChannel s ≠ 0`, e pelo adaptador de
zeros isso é `genuineContinuation s ≠ 0`.

O resultado é uma **região explícita** (definida pela própria desigualdade de
dominância) onde o Genuine canônico não se anula — logo, confinamento vacuoso
(não há zero algum nessa região).  Nenhuma dominância é fabricada: ela é provada
das cotas analíticas.  A não-vacuidade concreta da região (um ponto explícito
off-critical) é um passo numérico subsequente.

Genuine First: nenhum zeta, equação funcional ou RH.
-/

open Complex

namespace CPFormal.Analytic.Cp

noncomputable section

/-- A cauda do canal pareado, a partir do índice 1. -/
def pairedAltTail (s : ℂ) : ℂ := ∑' n : ℕ, pairedAltTerm s (n + 1)

/-- Envelope de valor médio para a cauda: `‖s‖ · ∑ₙ (2n+3)^{-σ-1}`. -/
def pairedAltEnvelopeTail (s : ℂ) : ℝ :=
  ‖s‖ * ∑' n : ℕ, (2 * (n : ℝ) + 3) ^ (-s.re - 1)

/-- Os termos pareados são somáveis no semiplano direito. -/
theorem summable_pairedAltTerm {s : ℂ} (hs0 : s ≠ 0) (hs : 0 < s.re) :
    Summable (pairedAltTerm s) :=
  Summable.of_norm_bounded ((summable_pairedAltEnvelope hs).mul_left ‖s‖)
    (fun n => norm_pairedAltTerm_le hs0 hs n)

/-- As normas dos termos pareados são somáveis. -/
theorem summable_norm_pairedAltTerm {s : ℂ} (hs0 : s ≠ 0) (hs : 0 < s.re) :
    Summable (fun n => ‖pairedAltTerm s n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => norm_pairedAltTerm_le hs0 hs n)
    ((summable_pairedAltEnvelope hs).mul_left ‖s‖)

/-- A envelope deslocada `(2n+3)^{-σ-1}` é somável. -/
theorem summable_shiftedEnvelope {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n : ℕ => (2 * (n : ℝ) + 3) ^ (-s.re - 1)) := by
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_)
    (summable_pairedAltEnvelope hs)
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)

/-- **Cota da cauda.**  A norma da cauda pareada é majorada pela envelope. -/
theorem norm_pairedAltTail_le {s : ℂ} (hs0 : s ≠ 0) (hs : 0 < s.re) :
    ‖pairedAltTail s‖ ≤ pairedAltEnvelopeTail s := by
  have hshiftnorm : Summable (fun n : ℕ => ‖pairedAltTerm s (n + 1)‖) :=
    (summable_nat_add_iff 1).mpr (summable_norm_pairedAltTerm hs0 hs)
  have henv : Summable (fun n : ℕ => ‖s‖ * (2 * (n : ℝ) + 3) ^ (-s.re - 1)) :=
    (summable_shiftedEnvelope hs).mul_left ‖s‖
  calc ‖pairedAltTail s‖
      ≤ ∑' n : ℕ, ‖pairedAltTerm s (n + 1)‖ := norm_tsum_le_tsum_norm hshiftnorm
    _ ≤ ∑' n : ℕ, ‖s‖ * (2 * (n : ℝ) + 3) ^ (-s.re - 1) := by
        refine Summable.tsum_le_tsum (fun n => ?_) hshiftnorm henv
        have hb := norm_pairedAltTerm_le hs0 hs (n + 1)
        have hcast : (2 * ((n + 1 : ℕ) : ℝ) + 1) = 2 * (n : ℝ) + 3 := by
          push_cast; ring
        rwa [hcast] at hb
    _ = pairedAltEnvelopeTail s := by rw [pairedAltEnvelopeTail, tsum_mul_left]

/-- O primeiro termo pareado é `1 - 2^{-s}`. -/
theorem pairedAltTerm_zero_eq (s : ℂ) :
    pairedAltTerm s 0 = 1 - (2 : ℂ) ^ (-s) := by
  show ((2 * 0 + 1 : ℕ) : ℂ) ^ (-s) - ((2 * 0 + 2 : ℕ) : ℂ) ^ (-s)
      = 1 - (2 : ℂ) ^ (-s)
  norm_num [Complex.one_cpow]

/-- **Piso do primeiro termo.**  `1 - 2^{-σ} ≤ ‖pairedAltTerm s 0‖`. -/
theorem one_sub_two_rpow_le_norm_pairedAltTerm_zero (s : ℂ) :
    1 - (2 : ℝ) ^ (-s.re) ≤ ‖pairedAltTerm s 0‖ := by
  rw [pairedAltTerm_zero_eq]
  have hnorm2 : ‖(2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-s.re) := by
    have h := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) (-s)
    simpa using h
  calc 1 - (2 : ℝ) ^ (-s.re) = ‖(1 : ℂ)‖ - ‖(2 : ℂ) ^ (-s)‖ := by
        rw [hnorm2, norm_one]
    _ ≤ ‖(1 : ℂ) - (2 : ℂ) ^ (-s)‖ := norm_sub_norm_le _ _

/-- **Critério nativo de não-anulação.**  Se, no strip, a envelope da cauda é
estritamente menor que o piso do primeiro termo, então `genuineContinuation s ≠ 0`.
É o minorante coercivo instanciado, provado das cotas analíticas. -/
theorem genuineContinuation_ne_zero_of_firstTerm_dominates
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hdom : pairedAltEnvelopeTail s < 1 - (2 : ℝ) ^ (-s.re)) :
    genuineContinuation s ≠ 0 := by
  have hsre : 0 < s.re := hs.1
  have hs0 : s ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hsre; exact lt_irrefl 0 hsre
  have hsplit : pairedAltChannel s = pairedAltTerm s 0 + pairedAltTail s := by
    rw [pairedAltTail, pairedAltChannel]
    exact (summable_pairedAltTerm hs0 hsre).tsum_eq_zero_add
  have hchannel_ne : pairedAltChannel s ≠ 0 := by
    rw [hsplit]
    exact no_zero_of_dominance rfl
      (one_sub_two_rpow_le_norm_pairedAltTerm_zero s)
      (norm_pairedAltTail_le hs0 hsre) hdom
  intro hzero
  exact hchannel_ne ((pairedAltChannel_eq_zero_iff_genuineContinuation hs).2 hzero)

/-- Região explícita onde o primeiro termo pareado domina a cauda. -/
def firstTermDominanceRegion : Set ℂ :=
  {s | s ∈ genuineCriticalStrip ∧
    pairedAltEnvelopeTail s < 1 - (2 : ℝ) ^ (-s.re)}

/-- **Não-anulação incondicional na região.**  `genuineContinuation` não se anula
em nenhum ponto da região de dominância do primeiro termo. -/
theorem genuineContinuation_ne_zero_on_firstTermDominanceRegion
    {s : ℂ} (hs : s ∈ firstTermDominanceRegion) :
    genuineContinuation s ≠ 0 :=
  genuineContinuation_ne_zero_of_firstTerm_dominates hs.1 hs.2

/-- **Confinamento (vacuoso) na região.**  Como não há zero Genuine algum na
região de dominância, todo zero dela está trivialmente em `Re(s)=1/2`. -/
theorem genuineConfined_on_firstTermDominanceRegion :
    ∀ ⦃s : ℂ⦄, s ∈ firstTermDominanceRegion → genuineContinuation s = 0 →
      s.re = 1 / 2 :=
  fun _ hs hzero =>
    absurd hzero (genuineContinuation_ne_zero_on_firstTermDominanceRegion hs)

end

end CPFormal.Analytic.Cp
