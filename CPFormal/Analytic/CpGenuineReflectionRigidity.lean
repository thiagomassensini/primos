import CPFormal.Analytic.CpGenuineRealAxisPositivity
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Rigidez por reflexão do canal escalar (Schwarz nativo)

Tentativa honesta da rota conformal/reflexão.  O canal escalar é holomorfo e,
como cada base `(2n+1), (2n+2)` é um real positivo, satisfaz a reflexão de
Schwarz sobre o eixo real:

`pairedAltChannel (conj s) = conj (pairedAltChannel s)`.

Consequências (rigidez, não confinamento):

* os zeros Genuine vêm em **pares conjugados** `(σ, t), (σ, -t)`;
* combinado com a positividade do eixo real, **nenhum** zero tem `t = 0`.

**Até onde isto chega — honestamente.**  A reflexão de Schwarz é a simetria
`t → -t` (espelho no eixo real).  Ela isola e espelha os zeros, mas **não** os
prende em `σ = 1/2`: não há aqui simetria `σ → 1-σ` nativa, e mesmo se houvesse,
simetria sozinha não confina (esse é o cerne clássico da dificuldade).  O
`pinning` em `σ = 1/2` continua sendo uma questão de **positividade radial** (o
acoplamento escalar → balanço radial), não de simetria.  Este módulo mapeia
exatamente a fronteira da rota conformal.

Genuine First: nenhum zeta, equação funcional ou RH.
-/

open Complex

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Reflexão de Schwarz por termo: a base real positiva conjuga o expoente. -/
theorem pairedAltTerm_conj (s : ℂ) (n : ℕ) :
    pairedAltTerm (starRingEnd ℂ s) n = starRingEnd ℂ (pairedAltTerm s n) := by
  have harg : ∀ m : ℕ, (((m : ℕ) : ℂ)).arg ≠ Real.pi := by
    intro m
    rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg (by positivity)]
    exact Real.pi_pos.ne
  simp only [pairedAltTerm, map_sub]
  congr 1
  · rw [show -(starRingEnd ℂ s) = starRingEnd ℂ (-s) from (map_neg _ _).symm,
      Complex.cpow_conj _ _ (harg (2 * n + 1)), map_natCast]
  · rw [show -(starRingEnd ℂ s) = starRingEnd ℂ (-s) from (map_neg _ _).symm,
      Complex.cpow_conj _ _ (harg (2 * n + 2)), map_natCast]

/-- **Reflexão de Schwarz do canal escalar.**  `pairedAltChannel (conj s) =
conj (pairedAltChannel s)`. -/
theorem pairedAltChannel_conj (s : ℂ) :
    pairedAltChannel (starRingEnd ℂ s) = starRingEnd ℂ (pairedAltChannel s) := by
  rw [pairedAltChannel, pairedAltChannel, conj_tsum]
  exact tsum_congr (fun n => pairedAltTerm_conj s n)

/-- `conj s` está no strip exatamente quando `s` está (mesma parte real). -/
theorem conj_mem_genuineCriticalStrip {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    (starRingEnd ℂ s) ∈ genuineCriticalStrip :=
  ⟨by rw [Complex.conj_re]; exact hs.1, by rw [Complex.conj_re]; exact hs.2⟩

/-- **Pareamento conjugado dos zeros.**  Se `s` é um zero Genuine no strip, então
o seu espelho `conj s` também é. -/
theorem genuineContinuation_conj_eq_zero {s : ℂ}
    (hs : s ∈ genuineCriticalStrip) (hzero : genuineContinuation s = 0) :
    genuineContinuation (starRingEnd ℂ s) = 0 := by
  rw [← pairedAltChannel_eq_zero_iff_genuineContinuation (conj_mem_genuineCriticalStrip hs),
    pairedAltChannel_conj,
    (pairedAltChannel_eq_zero_iff_genuineContinuation hs).mpr hzero, map_zero]

/-- **Rigidez por reflexão.**  Todo zero Genuine do strip é off-eixo (`t ≠ 0`) e
tem um espelho conjugado.  Rigidez `t → -t`; o `pinning` em `σ = 1/2` fica aberto. -/
theorem genuineContinuation_zero_offReal_and_conjPaired {s : ℂ}
    (hs : s ∈ genuineCriticalStrip) (hzero : genuineContinuation s = 0) :
    s.im ≠ 0 ∧ genuineContinuation (starRingEnd ℂ s) = 0 := by
  refine ⟨?_, genuineContinuation_conj_eq_zero hs hzero⟩
  intro him
  have hsreal : s = ((s.re : ℝ) : ℂ) :=
    Complex.ext (Complex.ofReal_re s.re).symm (him.trans (Complex.ofReal_im s.re).symm)
  rw [hsreal] at hzero
  exact genuineContinuation_ofReal_ne_zero hs.1 hs.2 hzero

end

end CPFormal.Analytic.Cp
