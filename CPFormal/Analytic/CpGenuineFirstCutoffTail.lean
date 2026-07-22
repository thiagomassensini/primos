import CPFormal.Analytic.CpRealSpectralGenerator

/-!
# Proveniencia Genuine-first do residuo de cutoff

Este modulo registra a identidade estrutural mais simples por tras do residuo
observado em uma camera finita. A serie bracketada absolutamente convergente e
separada, em qualquer corte `M`, em duas partes:

`carta infinita = prefixo finito + cauda bracketada`.

Logo, quando o readout Genuine zera, o valor que permanece no prefixo finito
nao e descartado como erro numerico: ele e exatamente o negativo da cauda que
ainda nao entrou no corte.

A prova usa somente a somabilidade dos blocos bracketados e a decomposicao de
uma serie em cabeca e cauda. Nao usa zeta, equacao funcional, tabela de zeros
ou argumento de continuacao analitica.
-/

open scoped BigOperators

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Informacao bracketada ainda nao incorporada depois do corte `M`. -/
def realCpBracketCutoffTail (p M : ℕ) (s : ℂ) : ℂ :=
  ∑' k : ℕ, realCpSaturatedBracket p (k + M) s

/-- Decomposicao exata da carta bracketada em prefixo visivel e cauda. -/
theorem bracketedDirichletChart_eq_finite_add_cutoffTail
    (p M : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : -1 < s.re) :
    bracketedDirichletChart p s =
      finiteBracketedDirichletChart p M s +
        realCpBracketCutoffTail p M s := by
  unfold bracketedDirichletChart finiteBracketedDirichletChart
    realCpBracketCutoffTail
  have hsplit :=
    (summable_realCpSaturatedBracket p hp hs).sum_add_tsum_nat_add M
  rw [← hsplit]
  ring

/-- A mesma decomposicao escrita na carta finita Genuine ja auditada. -/
theorem bracketedDirichletChart_eq_finiteChart_add_cutoffTail
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {s : ℂ} (hs : -1 < s.re) :
    bracketedDirichletChart p s =
      CPFormal.Genuine.Cp.finiteChart p M (dirichletTerm s) +
        realCpBracketCutoffTail p M s := by
  calc
    bracketedDirichletChart p s =
        finiteBracketedDirichletChart p M s +
          realCpBracketCutoffTail p M s :=
      bracketedDirichletChart_eq_finite_add_cutoffTail p M hp hs
    _ = CPFormal.Genuine.Cp.finiteChart p M (dirichletTerm s) +
          realCpBracketCutoffTail p M s := by
      rw [finiteBracketedDirichletChart_eq_finiteChart p M hp hpodd s]

/--
No zero da carta infinita, o residuo do cutoff e exatamente a cauda ainda nao
resolvida, com sinal oposto.
-/
theorem finiteBracketedDirichletChart_eq_neg_cutoffTail_of_chart_zero
    (p M : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : -1 < s.re)
    (hzero : bracketedDirichletChart p s = 0) :
    finiteBracketedDirichletChart p M s =
      -realCpBracketCutoffTail p M s := by
  have hsplit :=
    bracketedDirichletChart_eq_finite_add_cutoffTail p M hp hs
  calc
    finiteBracketedDirichletChart p M s =
        (finiteBracketedDirichletChart p M s +
          realCpBracketCutoffTail p M s) -
            realCpBracketCutoffTail p M s := by ring
    _ = bracketedDirichletChart p s -
          realCpBracketCutoffTail p M s := by rw [← hsplit]
    _ = -realCpBracketCutoffTail p M s := by rw [hzero]; ring

/-- Versao do teorema anterior diretamente na carta Genuine finita. -/
theorem finiteChart_eq_neg_cutoffTail_of_chart_zero
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {s : ℂ} (hs : -1 < s.re)
    (hzero : bracketedDirichletChart p s = 0) :
    CPFormal.Genuine.Cp.finiteChart p M (dirichletTerm s) =
      -realCpBracketCutoffTail p M s := by
  calc
    CPFormal.Genuine.Cp.finiteChart p M (dirichletTerm s) =
        finiteBracketedDirichletChart p M s :=
      (finiteBracketedDirichletChart_eq_finiteChart
        p M hp hpodd s).symm
    _ = -realCpBracketCutoffTail p M s :=
      finiteBracketedDirichletChart_eq_neg_cutoffTail_of_chart_zero
        p M hp hs hzero

/--
Forma real-espectral Genuine-first: em uma ressonancia, toda corrente finita
remanescente e exatamente o negativo da cauda bracketada nao resolvida.
-/
theorem finiteRealSpectralChart_eq_neg_cutoffTail_of_resonance
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) (t : ℝ)
    (hres : IsRealSpectralResonance t) :
    finiteRealSpectralChart p M t =
      -realCpBracketCutoffTail p M (criticalLineParameter t) := by
  unfold finiteRealSpectralChart
  exact finiteBracketedDirichletChart_eq_neg_cutoffTail_of_chart_zero
    p M hp (by norm_num)
      ((isRealSpectralResonance_iff_chart_zero p hp hpodd t).mp hres)

/--
Depois da calibracao da camera, o mesmo residuo e a cauda bracketada dividida
pelo fator de bordo nao nulo. A normalizacao nao apaga sua proveniencia.
-/
theorem finiteRealSpectralCamera_eq_neg_cutoffTail_div_factor_of_resonance
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) (t : ℝ)
    (hres : IsRealSpectralResonance t) :
    finiteRealSpectralCamera p M t =
      -(realCpBracketCutoffTail p M (criticalLineParameter t) /
        realSpectralChartFactor p t) := by
  unfold finiteRealSpectralCamera
  rw [finiteRealSpectralChart_eq_neg_cutoffTail_of_resonance
    p M hp hpodd t hres]
  ring

end

end CPFormal.Analytic.Cp
