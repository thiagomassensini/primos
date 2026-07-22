import CPFormal.Analytic.CpGenuineQuotient

/-!
# Compatibilidade Genuine entre cameras Cp

Este modulo fecha a independencia prima minima sem importar uma zeta externa.
Para duas cameras primas impares `p` e `q`, consideramos os produtos cruzados

`F_q * B_p` e `F_p * B_q`,

onde `F_p = 1-p^(1-s)` e `B_p` e a carta bracketada. Em `re(s)>1`, as duas
cartas ja foram obtidas como `F_p * genuineDirichlet`; portanto os produtos
cruzados coincidem literalmente. Como ambos sao holomorfos em `re(s)>-1`, o
principio da identidade prolonga essa igualdade sem dividir por nenhum fator.

Somente depois restringimos ao interior da faixa critica, onde os fatores ja
foram provados nao nulos. O cancelamento fornece a igualdade dos quocientes
de todas as cameras primas impares. Assim podemos escolher a camera `p=3`
apenas como representante canonico de um unico objeto Genuine na faixa.
-/

open scoped Topology

namespace CPFormal.Analytic.Cp

open Filter Set

noncomputable section

attribute [local instance 10000]
  NormedAddCommGroup.toAddCommGroup
  CommCStarAlgebra.toNonUnitalCommCStarAlgebra
  NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra
  NonUnitalCStarAlgebra.toNormedSpace
  NormedSpace.toModule

/-- Produto cruzado: o fator da camera `q` aplicado a carta da camera `p`. -/
def crossNormalizedChart (p q : ℕ) (s : ℂ) : ℂ :=
  cpChartFactor q s * bracketedDirichletChart p s

/-- Forma nomeada da identidade ja obtida no semiplano de convergencia. -/
theorem bracketedDirichletChart_eq_cpChartFactor_mul_genuineDirichlet
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {s : ℂ} (hs : 1 < s.re) :
    bracketedDirichletChart p s =
      cpChartFactor p s * genuineDirichlet s := by
  simpa [cpChartFactor] using
    (bracketedDirichletChart_eq_genuine_factor p hp hpodd hs)

/-- Cada produto cruzado e holomorfo no semiplano bracketado inteiro. -/
theorem analyticOnNhd_crossNormalizedChart
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    AnalyticOnNhd ℂ (crossNormalizedChart p q) bracketHalfPlane := by
  have hfactorAll : AnalyticOnNhd ℂ (cpChartFactor q) Set.univ :=
    (differentiable_cpChartFactor q hq).differentiableOn.analyticOnNhd
      isOpen_univ
  have hfactor : AnalyticOnNhd ℂ (cpChartFactor q) bracketHalfPlane :=
    hfactorAll.mono (subset_univ _)
  exact hfactor.mul (analyticOnNhd_bracketedDirichletChart p hp)

/-- No dominio inicial, os produtos cruzados sao o mesmo produto
`F_p * F_q * genuineDirichlet`. -/
theorem crossNormalizedChart_eq_swap_of_one_lt_re
    (p q : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : 1 < s.re) :
    crossNormalizedChart p q s = crossNormalizedChart q p s := by
  unfold crossNormalizedChart
  rw [bracketedDirichletChart_eq_cpChartFactor_mul_genuineDirichlet
      p hp hpodd hs,
    bracketedDirichletChart_eq_cpChartFactor_mul_genuineDirichlet
      q hq hqodd hs]
  ring

/-!
Coracao do checkpoint: a identidade cruzada e prolongada antes de qualquer
divisao. Portanto nenhum zero de fator cria um buraco no argumento de
continuacao.
-/
theorem crossNormalizedChart_eq_swap
    (p q : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q) :
    Set.EqOn (crossNormalizedChart p q)
      (crossNormalizedChart q p) bracketHalfPlane := by
  have hrightOpen : IsOpen {s : ℂ | 1 < s.re} := by
    exact isOpen_lt continuous_const Complex.continuous_re
  have hrightMem : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
    hrightOpen.mem_nhds (by norm_num)
  have heventually :
      crossNormalizedChart p q =ᶠ[𝓝 (2 : ℂ)]
        crossNormalizedChart q p := by
    filter_upwards [hrightMem] with s hs
    exact crossNormalizedChart_eq_swap_of_one_lt_re
      p q hp hpodd hq hqodd hs
  have hleft := analyticOnNhd_crossNormalizedChart p q hp hq
  exact hleft.eqOn_of_preconnected_of_eventuallyEq
      (analyticOnNhd_crossNormalizedChart q p hq hp)
      isPreconnected_bracketHalfPlane
      (by norm_num [bracketHalfPlane]) heventually

/-- Forma pontual da identidade cruzada no semiplano maior. -/
theorem crossNormalizedChart_eq_swap_at
    (p q : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : -1 < s.re) :
    crossNormalizedChart p q s = crossNormalizedChart q p s :=
  crossNormalizedChart_eq_swap p q hp hpodd hq hqodd hs

/-- Cancelando os fatores regulares, quaisquer duas cameras primas impares
produzem o mesmo quociente Genuine no interior da faixa critica. -/
theorem cpGenuineQuotient_eq_cpGenuineQuotient
    (p q : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    cpGenuineQuotient p s = cpGenuineQuotient q s := by
  have hfactorP := cpChartFactor_ne_zero_on_genuineCriticalStrip p hp hs
  have hfactorQ := cpChartFactor_ne_zero_on_genuineCriticalStrip q hq hs
  have hcross := crossNormalizedChart_eq_swap_at
    p q hp hpodd hq hqodd (s := s) (by linarith [hs.1])
  unfold cpGenuineQuotient
  field_simp [hfactorP, hfactorQ]
  simpa [crossNormalizedChart, mul_comm] using hcross

/-- Representante canonico do Genuine continuado, escolhido pela menor
camera prima impar. A independencia da camera e provada abaixo. -/
def genuineContinuation (s : ℂ) : ℂ :=
  cpGenuineQuotient 3 s

/-- O representante canonico recupera a serie Genuine original em
`re(s)>1`. -/
theorem genuineContinuation_eq_genuineDirichlet
    {s : ℂ} (hs : 1 < s.re) :
    genuineContinuation s = genuineDirichlet s := by
  simpa [genuineContinuation] using
    (cpGenuineQuotient_eq_genuineDirichlet 3 (by norm_num) (by norm_num) hs)

/-- O Genuine canonico e holomorfo no interior da faixa critica. -/
theorem analyticOnNhd_genuineContinuation_genuineCriticalStrip :
    AnalyticOnNhd ℂ genuineContinuation genuineCriticalStrip := by
  change AnalyticOnNhd ℂ (cpGenuineQuotient 3) genuineCriticalStrip
  exact analyticOnNhd_cpGenuineQuotient_genuineCriticalStrip 3 (by norm_num)

/-- Toda camera prima impar produz o representante canonico na faixa. -/
theorem cpGenuineQuotient_eq_genuineContinuation
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    cpGenuineQuotient p s = genuineContinuation s := by
  change cpGenuineQuotient p s = cpGenuineQuotient 3 s
  exact cpGenuineQuotient_eq_cpGenuineQuotient
    p 3 hp hpodd (by norm_num) (by norm_num) hs

/-- Fatoracao Genuine independente da camera no interior da faixa. -/
theorem bracketedDirichletChart_eq_cpChartFactor_mul_genuineContinuation
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    bracketedDirichletChart p s =
      cpChartFactor p s * genuineContinuation s := by
  rw [bracketedDirichletChart_eq_factor_mul_cpGenuineQuotient p hp hs,
    cpGenuineQuotient_eq_genuineContinuation p hp hpodd hs]

/-- Os zeros de qualquer carta prima impar sao exatamente os zeros do mesmo
Genuine canonico dentro da faixa critica. -/
theorem bracketedDirichletChart_zero_iff_genuineContinuation_zero
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    bracketedDirichletChart p s = 0 ↔ genuineContinuation s = 0 := by
  rw [bracketedDirichletChart_zero_iff_cpGenuineQuotient_zero p hp hs,
    cpGenuineQuotient_eq_genuineContinuation p hp hpodd hs]

end

end CPFormal.Analytic.Cp
