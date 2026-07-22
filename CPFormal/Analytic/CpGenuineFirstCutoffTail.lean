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

/-!
## Transferencia horizontal--vertical entre bases
-/

/--
Num zero de uma camera, o prefixo horizontal junto da cauda bracketada ainda
nao resolvida recompõe exatamente a correcao vertical do mesmo cutoff.
-/
theorem blockPrefix_add_cutoffTail_eq_verticalCorrection_of_chart_zero
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {s : ℂ} (hs : -1 < s.re)
    (hzero : bracketedDirichletChart p s = 0) :
    CPFormal.Genuine.Cp.blockPrefix p M (dirichletTerm s) +
        realCpBracketCutoffTail p M s =
      CPFormal.Genuine.Cp.verticalCorrection p M (dirichletTerm s) := by
  have hfinite :=
    finiteChart_eq_neg_cutoffTail_of_chart_zero
      p M hp hpodd hs hzero
  have hblock :=
    CPFormal.Genuine.Cp.finiteChart_eq_blockPrefix_sub_verticalCorrection
      p hp M (dirichletTerm s)
  calc
    CPFormal.Genuine.Cp.blockPrefix p M (dirichletTerm s) +
        realCpBracketCutoffTail p M s =
      CPFormal.Genuine.Cp.finiteChart p M (dirichletTerm s) +
        CPFormal.Genuine.Cp.verticalCorrection p M (dirichletTerm s) +
        realCpBracketCutoffTail p M s := by
          rw [hblock]
          ring
    _ = -realCpBracketCutoffTail p M s +
        CPFormal.Genuine.Cp.verticalCorrection p M (dirichletTerm s) +
        realCpBracketCutoffTail p M s := by rw [hfinite]
    _ = CPFormal.Genuine.Cp.verticalCorrection p M (dirichletTerm s) := by
      ring

/--
Cutoffs cruzados por duas bases primas impares possuem o mesmo prefixo
horizontal literal. Na base `p` usamos `halfRange q` blocos; na base `q`,
`halfRange p`. Ambos terminam no inteiro `(p*q-1)/2`.
-/
theorem blockPrefix_cross_prime_aligned
    (p q : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    (f : ℤ → ℂ) :
    CPFormal.Genuine.Cp.blockPrefix p
        (CPFormal.Genuine.Cp.halfRange q) f =
      CPFormal.Genuine.Cp.blockPrefix q
        (CPFormal.Genuine.Cp.halfRange p) f := by
  rw [CPFormal.Genuine.Cp.blockPrefix_eq_positiveIntervalSum
      p hp hpodd,
    CPFormal.Genuine.Cp.blockPrefix_eq_positiveIntervalSum
      q hq hqodd]
  have hpformNat :=
    CPFormal.Carry.Cp.two_mul_halfRange_add_one hpodd
  have hqformNat :=
    CPFormal.Carry.Cp.two_mul_halfRange_add_one hqodd
  have hpformInt :
      (p : ℤ) =
        2 * (CPFormal.Genuine.Cp.halfRange p : ℤ) + 1 := by
    exact_mod_cast hpformNat.symm
  have hqformInt :
      (q : ℤ) =
        2 * (CPFormal.Genuine.Cp.halfRange q : ℤ) + 1 := by
    exact_mod_cast hqformNat.symm
  have hend :
      (p : ℤ) * (CPFormal.Genuine.Cp.halfRange q : ℤ) +
          (CPFormal.Genuine.Cp.halfRange p : ℤ) =
        (q : ℤ) * (CPFormal.Genuine.Cp.halfRange p : ℤ) +
          (CPFormal.Genuine.Cp.halfRange q : ℤ) := by
    rw [hpformInt, hqformInt]
    ring
  rw [hend]

/--
Lei multibase no zero Genuine: depois de alinhar o mesmo prefixo horizontal,
cada correcao vertical menos sua cauda bracketada produz o mesmo valor.
-/
theorem verticalCorrection_sub_cutoffTail_cross_prime_of_genuine_zero
    (p q : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    CPFormal.Genuine.Cp.verticalCorrection p
          (CPFormal.Genuine.Cp.halfRange q) (dirichletTerm s) -
        realCpBracketCutoffTail p
          (CPFormal.Genuine.Cp.halfRange q) s =
      CPFormal.Genuine.Cp.verticalCorrection q
          (CPFormal.Genuine.Cp.halfRange p) (dirichletTerm s) -
        realCpBracketCutoffTail q
          (CPFormal.Genuine.Cp.halfRange p) s := by
  have hconv : -1 < s.re := by linarith [hs.1]
  have hzeroP : bracketedDirichletChart p s = 0 :=
    (bracketedDirichletChart_zero_iff_genuineContinuation_zero
      p hp hpodd hs).2 hzero
  have hzeroQ : bracketedDirichletChart q s = 0 :=
    (bracketedDirichletChart_zero_iff_genuineContinuation_zero
      q hq hqodd hs).2 hzero
  have hpLedger :=
    blockPrefix_add_cutoffTail_eq_verticalCorrection_of_chart_zero
      p (CPFormal.Genuine.Cp.halfRange q)
      hp hpodd hconv hzeroP
  have hqLedger :=
    blockPrefix_add_cutoffTail_eq_verticalCorrection_of_chart_zero
      q (CPFormal.Genuine.Cp.halfRange p)
      hq hqodd hconv hzeroQ
  calc
    CPFormal.Genuine.Cp.verticalCorrection p
          (CPFormal.Genuine.Cp.halfRange q) (dirichletTerm s) -
        realCpBracketCutoffTail p
          (CPFormal.Genuine.Cp.halfRange q) s =
      (CPFormal.Genuine.Cp.blockPrefix p
          (CPFormal.Genuine.Cp.halfRange q) (dirichletTerm s) +
        realCpBracketCutoffTail p
          (CPFormal.Genuine.Cp.halfRange q) s) -
        realCpBracketCutoffTail p
          (CPFormal.Genuine.Cp.halfRange q) s := by rw [hpLedger]
    _ = CPFormal.Genuine.Cp.blockPrefix p
          (CPFormal.Genuine.Cp.halfRange q) (dirichletTerm s) := by ring
    _ = CPFormal.Genuine.Cp.blockPrefix q
          (CPFormal.Genuine.Cp.halfRange p) (dirichletTerm s) :=
      blockPrefix_cross_prime_aligned
        p q hp hpodd hq hqodd (dirichletTerm s)
    _ = (CPFormal.Genuine.Cp.blockPrefix q
          (CPFormal.Genuine.Cp.halfRange p) (dirichletTerm s) +
        realCpBracketCutoffTail q
          (CPFormal.Genuine.Cp.halfRange p) s) -
        realCpBracketCutoffTail q
          (CPFormal.Genuine.Cp.halfRange p) s := by ring
    _ = CPFormal.Genuine.Cp.verticalCorrection q
          (CPFormal.Genuine.Cp.halfRange p) (dirichletTerm s) -
        realCpBracketCutoffTail q
          (CPFormal.Genuine.Cp.halfRange p) s := by rw [hqLedger]

/--
Forma conservativa da mesma lei: o desacordo vertical entre duas bases e
exatamente o desacordo entre suas caudas bracketadas nao resolvidas.
-/
theorem verticalCorrection_cross_prime_defect_eq_cutoffTail_defect_of_genuine_zero
    (p q : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    CPFormal.Genuine.Cp.verticalCorrection p
          (CPFormal.Genuine.Cp.halfRange q) (dirichletTerm s) -
        CPFormal.Genuine.Cp.verticalCorrection q
          (CPFormal.Genuine.Cp.halfRange p) (dirichletTerm s) =
      realCpBracketCutoffTail p
          (CPFormal.Genuine.Cp.halfRange q) s -
        realCpBracketCutoffTail q
          (CPFormal.Genuine.Cp.halfRange p) s := by
  have htransport :=
    verticalCorrection_sub_cutoffTail_cross_prime_of_genuine_zero
      p q hp hpodd hq hqodd hs hzero
  linear_combination htransport

end

end CPFormal.Analytic.Cp
