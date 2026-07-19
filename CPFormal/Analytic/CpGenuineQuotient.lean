import CPFormal.Analytic.CpBracketHolomorphic
import Mathlib.Analysis.Analytic.Constructions

/-!
# Fator regular da carta Cp e quociente Genuine

Este modulo fecha a consequencia algebrica minima da continuacao bracketada.
Para primo `p`, o modulo de

`p^(1-s)`

e `p^(1-re(s))`. Portanto `1-p^(1-s)` so pode zerar sobre a reta
`re(s)=1`, e em particular nunca zera no interior da faixa critica.

Definimos entao o quociente Cp

`cpGenuineQuotient p s = bracketedDirichletChart p s / cpChartFactor p s`.

Ele e holomorfo no interior da faixa, coincide com a serie Genuine original
em `re(s)>1` e possui exatamente os mesmos zeros da carta onde o fator nao
zera. O indice `p` permanece explicito: compatibilidade entre quocientes de
cameras primas distintas nao e presumida neste checkpoint.
-/

open scoped Topology

namespace CPFormal.Analytic.Cp

open Set

noncomputable section

attribute [local instance 10000]
  NormedAddCommGroup.toAddCommGroup
  CommCStarAlgebra.toNonUnitalCommCStarAlgebra
  NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra
  NonUnitalCStarAlgebra.toNormedSpace
  NormedSpace.toModule

/-- Fator local que relaciona a carta Cp ao canal Genuine. -/
def cpChartFactor (p : ℕ) (s : ℂ) : ℂ :=
  1 - (p : ℂ) ^ (1 - s)

/-- Interior usual da faixa critica. -/
def genuineCriticalStrip : Set ℂ :=
  {s : ℂ | 0 < s.re ∧ s.re < 1}

/-- Norma exata da potencia prima que aparece no fator da carta. -/
theorem norm_prime_cpow_one_sub
    (p : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    ‖(p : ℂ) ^ (1 - s)‖ = (p : ℝ) ^ (1 - s.re) := by
  have hpReal : 0 < (p : ℝ) := by
    exact_mod_cast hp.pos
  simpa using
    (Complex.norm_cpow_eq_rpow_re_of_pos hpReal (1 - s))

/-- Abaixo da reta `re(s)=1`, a potencia prima possui modulo estritamente
maior que um e nao pode ser igual a um. -/
theorem prime_cpow_one_sub_ne_one_of_re_lt_one
    (p : ℕ) (hp : Nat.Prime p) {s : ℂ} (hs : s.re < 1) :
    (p : ℂ) ^ (1 - s) ≠ 1 := by
  intro hpower
  have hnorm := congrArg norm hpower
  rw [norm_prime_cpow_one_sub p hp s, norm_one] at hnorm
  have hpReal : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp.one_lt
  have hexponent : 0 < (1 : ℝ) - s.re := by
    linarith
  have hstrict := Real.one_lt_rpow hpReal hexponent
  linarith

/-- Acima da reta `re(s)=1`, a potencia prima possui modulo estritamente
menor que um e tambem nao pode ser igual a um. -/
theorem prime_cpow_one_sub_ne_one_of_one_lt_re
    (p : ℕ) (hp : Nat.Prime p) {s : ℂ} (hs : 1 < s.re) :
    (p : ℂ) ^ (1 - s) ≠ 1 := by
  intro hpower
  have hnorm := congrArg norm hpower
  rw [norm_prime_cpow_one_sub p hp s, norm_one] at hnorm
  have hpReal : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp.one_lt
  have hexponent : (1 : ℝ) - s.re < 0 := by
    linarith
  have hstrict := Real.rpow_lt_one_of_one_lt_of_neg hpReal hexponent
  linarith

theorem cpChartFactor_ne_zero_of_re_lt_one
    (p : ℕ) (hp : Nat.Prime p) {s : ℂ} (hs : s.re < 1) :
    cpChartFactor p s ≠ 0 := by
  intro hzero
  apply prime_cpow_one_sub_ne_one_of_re_lt_one p hp hs
  exact (sub_eq_zero.mp hzero).symm

theorem cpChartFactor_ne_zero_of_one_lt_re
    (p : ℕ) (hp : Nat.Prime p) {s : ℂ} (hs : 1 < s.re) :
    cpChartFactor p s ≠ 0 := by
  intro hzero
  apply prime_cpow_one_sub_ne_one_of_one_lt_re p hp hs
  exact (sub_eq_zero.mp hzero).symm

/-- Forma forte: fora da reta `re(s)=1`, o fator Cp nao zera. -/
theorem cpChartFactor_ne_zero_of_re_ne_one
    (p : ℕ) (hp : Nat.Prime p) {s : ℂ} (hs : s.re ≠ 1) :
    cpChartFactor p s ≠ 0 := by
  rcases lt_or_gt_of_ne hs with hleft | hright
  · exact cpChartFactor_ne_zero_of_re_lt_one p hp hleft
  · exact cpChartFactor_ne_zero_of_one_lt_re p hp hright

/-- Consequentemente, todo zero do fator esta confinado a `re(s)=1`. -/
theorem cpChartFactor_zero_implies_re_eq_one
    (p : ℕ) (hp : Nat.Prime p) {s : ℂ}
    (hzero : cpChartFactor p s = 0) :
    s.re = 1 := by
  by_contra hne
  exact cpChartFactor_ne_zero_of_re_ne_one p hp hne hzero

/-- Corolario diretamente usado na faixa critica. -/
theorem cpChartFactor_ne_zero_on_genuineCriticalStrip
    (p : ℕ) (hp : Nat.Prime p) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip) :
    cpChartFactor p s ≠ 0 :=
  cpChartFactor_ne_zero_of_re_lt_one p hp hs.2

/-- O fator Cp e inteiro na variavel espectral. -/
theorem differentiable_cpChartFactor
    (p : ℕ) (hp : Nat.Prime p) :
    Differentiable ℂ (cpChartFactor p) := by
  have hpComplex : (p : ℂ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  letI : NeZero (p : ℂ) := ⟨hpComplex⟩
  change Differentiable ℂ (fun s : ℂ ↦ 1 - (p : ℂ) ^ (1 - s))
  exact differentiable_const.sub
    ((differentiable_const_cpow_of_neZero (p : ℂ)).comp
      (differentiable_const.sub differentiable_id))

/-- Quociente Cp que recupera o canal Genuine onde o fator e regular. -/
def cpGenuineQuotient (p : ℕ) (s : ℂ) : ℂ :=
  bracketedDirichletChart p s / cpChartFactor p s

/-- No semiplano original de convergencia absoluta, o quociente recupera
literalmente a serie Genuine usada na construcao. -/
theorem cpGenuineQuotient_eq_genuineDirichlet
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {s : ℂ} (hs : 1 < s.re) :
    cpGenuineQuotient p s = genuineDirichlet s := by
  have hfactor := cpChartFactor_ne_zero_of_one_lt_re p hp hs
  rw [cpGenuineQuotient,
    bracketedDirichletChart_eq_genuine_factor p hp hpodd hs]
  simp [cpChartFactor, hfactor]

/-- No interior da faixa, a carta volta a ser fator vezes quociente. -/
theorem bracketedDirichletChart_eq_factor_mul_cpGenuineQuotient
    (p : ℕ) (hp : Nat.Prime p) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip) :
    bracketedDirichletChart p s =
      cpChartFactor p s * cpGenuineQuotient p s := by
  have hfactor := cpChartFactor_ne_zero_on_genuineCriticalStrip p hp hs
  unfold cpGenuineQuotient
  field_simp

/-- O quociente Cp e holomorfo no interior da faixa critica. -/
theorem analyticOnNhd_cpGenuineQuotient_genuineCriticalStrip
    (p : ℕ) (hp : Nat.Prime p) :
    AnalyticOnNhd ℂ (cpGenuineQuotient p) genuineCriticalStrip := by
  have hchart : AnalyticOnNhd ℂ
      (bracketedDirichletChart p) genuineCriticalStrip :=
    (analyticOnNhd_bracketedDirichletChart p hp).mono (by
      intro s hs
      change -1 < s.re
      linarith [hs.1])
  have hfactorAll : AnalyticOnNhd ℂ (cpChartFactor p) Set.univ :=
    (differentiable_cpChartFactor p hp).differentiableOn.analyticOnNhd
      isOpen_univ
  have hfactor : AnalyticOnNhd ℂ
      (cpChartFactor p) genuineCriticalStrip :=
    hfactorAll.mono (subset_univ _)
  exact hchart.div hfactor fun s hs ↦
    cpChartFactor_ne_zero_on_genuineCriticalStrip p hp hs

/-- Zero da carta e zero do quociente Genuine Cp sao equivalentes no
interior da faixa critica. -/
theorem bracketedDirichletChart_zero_iff_cpGenuineQuotient_zero
    (p : ℕ) (hp : Nat.Prime p) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip) :
    bracketedDirichletChart p s = 0 ↔ cpGenuineQuotient p s = 0 := by
  constructor
  · intro hchart
    simp [cpGenuineQuotient, hchart]
  · intro hquotient
    rw [bracketedDirichletChart_eq_factor_mul_cpGenuineQuotient p hp hs,
      hquotient, mul_zero]

end

end CPFormal.Analytic.Cp
