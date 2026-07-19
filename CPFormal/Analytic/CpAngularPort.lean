import CPFormal.Analytic.CpBracketGreenFlux
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Porta angular finita da camera canonica

Este arquivo realiza, antes de qualquer operador de retorno, o traco angular
da camera `p = 3` diretamente sobre os gradientes de Dirichlet. No bloco
`m`, as tres arestas recebem os pesos periodicos `1, 2, 0`; portanto

`angularBlock m = -sum_{r=0}^2 ((r+1) mod 3) * gradient(3m+r)`.

Essa definicao nao usa a carta bracketada. A identidade finita provada abaixo
e que descobre a relacao entre os dois objetos:

`finiteChart 3 M = finiteAngularTrace M + outerValue M`.

O termo externo e literalmente `(3M+1)^(-s)`. Para `Re(s)>0` ele desaparece,
e o traco angular converge para a carta bracketada. Em particular, num zero
Genuine dentro da faixa critica, o traco angular converge a zero.

Nenhum retorno `Psi` e definido aqui: ele deve nascer de dados independentes
antes que uma identidade de Wronskiano possa ser usada.
-/

open scoped BigOperators Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-- Um bloco da porta angular canonica, com pesos residuais `1, 2, 0`. -/
def canonicalAngularGradientBlock (m : ℕ) (s : ℂ) : ℂ :=
  -∑ r ∈ Finset.range 3,
    ((((r + 1) % 3 : ℕ) : ℂ) *
      positiveDirichletGradient s (3 * m + r))

/-- O peso local do bloco e o mesmo peso global `n mod 3` da porta. -/
theorem canonicalAngularWeight_eq_globalResidue (m r : ℕ) :
    (r + 1) % 3 = (3 * m + r + 1) % 3 := by
  omega

/-- Forma explicita do bloco: a terceira aresta tem peso zero. -/
theorem canonicalAngularGradientBlock_eq_two_edges
    (m : ℕ) (s : ℂ) :
    canonicalAngularGradientBlock m s =
      -(positiveDirichletGradient s (3 * m) +
        2 * positiveDirichletGradient s (3 * m + 1)) := by
  norm_num [canonicalAngularGradientBlock, Finset.sum_range_succ]

/-- Soma dos primeiros `M` blocos da porta angular canonica. -/
def finiteCanonicalAngularTrace (M : ℕ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.range M, canonicalAngularGradientBlock m s

/-- Acrescentar um bloco acrescenta exatamente sua corrente ponderada. -/
theorem finiteCanonicalAngularTrace_succ (M : ℕ) (s : ℂ) :
    finiteCanonicalAngularTrace (M + 1) s =
      finiteCanonicalAngularTrace M s + canonicalAngularGradientBlock M s := by
  unfold finiteCanonicalAngularTrace
  rw [Finset.sum_range_succ]

/-- O bloco angular aberto em seus tres valores de Dirichlet. -/
theorem canonicalAngularGradientBlock_eq_values
    (m : ℕ) (s : ℂ) :
    canonicalAngularGradientBlock m s =
      natDirichletTerm s (3 * m + 1) +
        natDirichletTerm s (3 * m + 2) -
          2 * natDirichletTerm s (3 * m + 3) := by
  rw [canonicalAngularGradientBlock_eq_two_edges]
  simp [positiveDirichletGradient]
  ring

/-- O bracket `p = 3` aberto no mesmo bloco aritmetico. -/
theorem realCpSaturatedBracket_three_eq_values
    (m : ℕ) (s : ℂ) :
    realCpSaturatedBracket 3 m s =
      natDirichletTerm s (3 * m + 2) -
        2 * natDirichletTerm s (3 * m + 3) +
          natDirichletTerm s (3 * m + 4) := by
  have hcenter :
      CPFormal.Genuine.Cp.alignedCenter 3 m =
        (((3 * m + 3 : ℕ) : ℤ)) := by
    unfold CPFormal.Genuine.Cp.alignedCenter
    push_cast
    ring
  have hleft :
      CPFormal.Genuine.Cp.alignedCenter 3 m - 1 =
        (((3 * m + 2 : ℕ) : ℤ)) := by
    rw [hcenter]
    push_cast
    ring
  have hright :
      CPFormal.Genuine.Cp.alignedCenter 3 m + 1 =
        (((3 * m + 4 : ℕ) : ℤ)) := by
    rw [hcenter]
    push_cast
    ring
  rw [realCpSaturatedBracket_eq_saturatedBracket]
  norm_num [CPFormal.saturatedBracket, CPFormal.centeredSecondDifference,
    CPFormal.Genuine.Cp.halfRange]
  rw [hleft, hright, hcenter]
  simp [natDirichletTerm]

/-- Acrescentar um centro acrescenta exatamente seu bracket. -/
theorem finiteBracketedDirichletChart_three_succ (M : ℕ) (s : ℂ) :
    finiteBracketedDirichletChart 3 (M + 1) s =
      finiteBracketedDirichletChart 3 M s +
        realCpSaturatedBracket 3 M s := by
  unfold finiteBracketedDirichletChart
  rw [Finset.sum_range_succ]
  ring

/-!
Identidade finita central. A porta angular e a carta bracketada diferem
somente pelo valor no vertice externo `3M+1`; esse termo nao foi escolhido
como residual, mas saiu da telescopagem dos pesos `1,2,0`.
-/
theorem finiteBracketedDirichletChart_three_eq_angularTrace_add_outer
    (M : ℕ) (s : ℂ) :
    finiteBracketedDirichletChart 3 M s =
      finiteCanonicalAngularTrace M s +
        positiveDirichletValue s (3 * M) := by
  induction M with
  | zero =>
      rw [finiteBracketedDirichletChart_three_eq_one_add_trace]
      simp [finiteCanonicalBracketTrace, finiteCanonicalAngularTrace,
        positiveDirichletValue]
  | succ M ih =>
      rw [finiteBracketedDirichletChart_three_succ,
        finiteCanonicalAngularTrace_succ, ih,
        realCpSaturatedBracket_three_eq_values,
        canonicalAngularGradientBlock_eq_values]
      have houter : 3 * (M + 1) = 3 * M + 3 := by omega
      rw [houter]
      simp only [positiveDirichletValue_eq_natDirichletTerm]
      ring

/-- O vertice externo da porta angular desaparece quando `Re(s)>0`. -/
theorem canonicalAngularOuterValue_tendsto_zero
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun M : ℕ ↦ positiveDirichletValue s (3 * M))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnat : Tendsto (fun M : ℕ ↦ 3 * M + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with M hM
    omega
  have hreal :
      Tendsto (fun M : ℕ ↦ (((3 * M + 1 : ℕ) : ℝ))) atTop atTop := by
    exact
      (tendsto_natCast_atTop_atTop :
        Tendsto ((↑) : ℕ → ℝ) atTop atTop).comp hnat
  have hrpow :
      Tendsto (fun M : ℕ ↦ (((3 * M + 1 : ℕ) : ℝ)) ^ (-s.re))
        atTop (nhds 0) := by
    simpa only [Function.comp_def] using
      ((_root_.tendsto_rpow_neg_atTop hs).comp hreal)
  simpa only [norm_positiveDirichletValue] using hrpow

/-- Passagem ao limite da porta angular para a carta bracketada. -/
theorem finiteCanonicalAngularTrace_tendsto
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun M : ℕ ↦ finiteCanonicalAngularTrace M s)
      atTop (nhds (bracketedDirichletChart 3 s)) := by
  have hchart := finiteBracketedDirichletChart_tendsto
    3 (by norm_num) (show -1 < s.re by linarith)
  have houter := canonicalAngularOuterValue_tendsto_zero hs
  have hdifference := hchart.sub houter
  have hpoint : ∀ M : ℕ,
      finiteBracketedDirichletChart 3 M s -
          positiveDirichletValue s (3 * M) =
        finiteCanonicalAngularTrace M s := by
    intro M
    rw [finiteBracketedDirichletChart_three_eq_angularTrace_add_outer]
    ring
  simpa only [hpoint, sub_zero] using hdifference

/-!
Coracao Genuine-first: a porta angular foi definida sem usar o zero. A carta
bracketada a identifica no limite; somente entao o zero Genuine faz o limite
da porta ser zero.
-/
theorem finiteCanonicalAngularTrace_tendsto_zero_of_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto (fun M : ℕ ↦ finiteCanonicalAngularTrace M s)
      atTop (nhds 0) := by
  have htrace := finiteCanonicalAngularTrace_tendsto
    (s := s) (by linarith [hs.1])
  have hchart : bracketedDirichletChart 3 s = 0 :=
    (bracketedDirichletChart_zero_iff_genuineContinuation_zero
      3 (by norm_num) (by norm_num) hs).2 hzero
  simpa only [hchart] using htrace

end

end CPFormal.Analytic.Cp
