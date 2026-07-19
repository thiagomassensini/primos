import CPFormal.Analytic.CpFiniteGreenPositivity

/-!
# Porta bracketada e bordo Green canonico

Este arquivo liga duas construcoes que ate aqui estavam separadas:

* o endpoint interno `1` da identidade Green refletida;
* a semente da carta bracketada canonica `p = 3`.

Para essa camera, `halfRange 3 = 1`; portanto a semente e literalmente
`1^(-s) = 1`. Se `trace_M` denota a soma dos primeiros `M` brackets, entao

`finiteBracketedDirichletChart 3 M s = innerEndpoint + trace_M`.

Consequentemente, subtrair o traco bracketado do bordo Green cru nao apaga
um residual por definicao: produz a identidade independente

`rawBoundary - trace_M = outerEndpoint - finiteChart_M`.

Nos zeros do Genuine canonico, os dois termos do lado direito tendem a zero.
Isso fecha o bordo bracketado no limite. A anulacao do fluxo bulk permanece
uma obrigacao separada.
-/

open scoped BigOperators Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-- Soma finita dos brackets da camera canonica `p = 3`, sem a semente. -/
def finiteCanonicalBracketTrace (M : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.range M, realCpSaturatedBracket 3 k s

/-- Traco bracketado infinito da camera canonica, ainda sem a semente. -/
def canonicalBracketTrace (s : ℂ) : ℂ :=
  ∑' k : ℕ, realCpSaturatedBracket 3 k s

/-- A semente da camera `p = 3` e exatamente `1^(-s) = 1`. -/
@[simp] theorem seedSum_three_dirichlet_eq_one (s : ℂ) :
    CPFormal.Genuine.Cp.seedSum 3 (dirichletTerm s) = 1 := by
  norm_num [CPFormal.Genuine.Cp.seedSum,
    CPFormal.Genuine.Cp.halfRange, dirichletTerm]

/-- A semente canonica coincide com o endpoint Green interno refletido. -/
theorem seedSum_three_eq_reflectedInnerEndpoint (s : ℂ) :
    CPFormal.Genuine.Cp.seedSum 3 (dirichletTerm s) =
      finiteReflectedOuterEndpoint 0 s := by
  rw [seedSum_three_dirichlet_eq_one,
    finiteReflectedInnerEndpoint_eq_one]

/-- A carta finita canonica e `1` mais seu traco de brackets. -/
theorem finiteBracketedDirichletChart_three_eq_one_add_trace
    (M : ℕ) (s : ℂ) :
    finiteBracketedDirichletChart 3 M s =
      1 + finiteCanonicalBracketTrace M s := by
  unfold finiteBracketedDirichletChart finiteCanonicalBracketTrace
  rw [seedSum_three_dirichlet_eq_one]

/-- Forma que identifica literalmente a semente com o endpoint interno. -/
theorem finiteBracketedDirichletChart_three_eq_inner_add_trace
    (M : ℕ) (s : ℂ) :
    finiteBracketedDirichletChart 3 M s =
      finiteReflectedOuterEndpoint 0 s +
        finiteCanonicalBracketTrace M s := by
  rw [finiteBracketedDirichletChart_three_eq_one_add_trace,
    finiteReflectedInnerEndpoint_eq_one]

/-- A carta bracketada infinita e `1` mais o traco canonico. -/
theorem bracketedDirichletChart_three_eq_one_add_trace (s : ℂ) :
    bracketedDirichletChart 3 s = 1 + canonicalBracketTrace s := by
  unfold bracketedDirichletChart canonicalBracketTrace
  rw [seedSum_three_dirichlet_eq_one]

/-- Num zero Genuine, o traco dos brackets vale exatamente `-1`. -/
theorem canonicalBracketTrace_eq_neg_one_of_genuineContinuation_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    canonicalBracketTrace s = -1 := by
  have hchart : bracketedDirichletChart 3 s = 0 :=
    (bracketedDirichletChart_zero_iff_genuineContinuation_zero
      3 (by norm_num) (by norm_num) hs).2 hzero
  rw [bracketedDirichletChart_three_eq_one_add_trace] at hchart
  linear_combination hchart

/--
Bordo complexo depois de acoplar o traco bracketado independente. Nenhum dos
dois termos e definido como residual da identidade a provar.
-/
def finiteBracketCoupledBoundary (M : ℕ) (s : ℂ) : ℂ :=
  finiteReflectedBoundary M s - finiteCanonicalBracketTrace M s

/-!
Identidade finita central: o `1` interno e a semente da carta sao o mesmo
objeto, logo o bordo acoplado e endpoint externo menos carta finita.
-/
theorem finiteBracketCoupledBoundary_eq_outer_sub_finiteChart
    (M : ℕ) (s : ℂ) :
    finiteBracketCoupledBoundary M s =
      finiteReflectedOuterEndpoint M s -
        finiteBracketedDirichletChart 3 M s := by
  rw [finiteBracketedDirichletChart_three_eq_inner_add_trace]
  unfold finiteBracketCoupledBoundary finiteReflectedBoundary
  ring

/-- Versao real assinada do bordo acoplado. -/
def finiteBracketCoupledSignedBoundary (M : ℕ) (s : ℂ) : ℝ :=
  finiteSignedCpGreenBoundary M s -
    (finiteCanonicalBracketTrace M s).re

/-- O bordo real acoplado e a parte real do bordo complexo acoplado. -/
theorem finiteBracketCoupledSignedBoundary_eq_re
    (M : ℕ) (s : ℂ) :
    finiteBracketCoupledSignedBoundary M s =
      (finiteBracketCoupledBoundary M s).re := by
  rfl

/-- Fluxo finito depois de passar pela mesma porta bracketada. -/
def finiteBracketCoupledCpGreenFlux
    (p M : ℕ) (s : ℂ) : ℝ :=
  finiteSignedCpGreenFlux p M s -
    (finiteCanonicalBracketTrace M s).re

/-!
A porta bracketada e subtraida dos dois lados da identidade assinada. A
igualdade permanece exata e o bordo continua sendo um objeto independente.
-/
theorem finiteBracketCoupledCpGreen_identity
    (p M : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    finiteBracketCoupledCpGreenFlux p M s =
      2 * criticalDisplacement s.re * finiteRadialGreenEnergy p M s +
        finiteBracketCoupledSignedBoundary M s := by
  unfold finiteBracketCoupledCpGreenFlux finiteBracketCoupledSignedBoundary
  rw [finiteSignedCpGreen_identity p M hp s]
  ring

/-- O bordo acoplado converge para o negativo da carta bracketada. -/
theorem finiteBracketCoupledBoundary_tendsto_neg_chart
    {s : ℂ} (hs : -1 < s.re) :
    Tendsto (fun M : ℕ ↦ finiteBracketCoupledBoundary M s)
      atTop (nhds (-bracketedDirichletChart 3 s)) := by
  have houter := finiteReflectedOuterEndpoint_tendsto_zero s
  have hchart := finiteBracketedDirichletChart_tendsto
    3 (by norm_num) hs
  simpa only [finiteBracketCoupledBoundary_eq_outer_sub_finiteChart,
    zero_sub] using houter.sub hchart

/-!
Coracao Genuine-first deste checkpoint: num zero do Genuine canonico, o
endpoint externo e a carta finita convergem ambos a zero; portanto o bordo
acoplado ao bracket converge a zero.
-/
theorem finiteBracketCoupledBoundary_tendsto_zero_of_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto (fun M : ℕ ↦ finiteBracketCoupledBoundary M s)
      atTop (nhds 0) := by
  have hchart : bracketedDirichletChart 3 s = 0 :=
    (bracketedDirichletChart_zero_iff_genuineContinuation_zero
      3 (by norm_num) (by norm_num) hs).2 hzero
  simpa [hchart] using
    (finiteBracketCoupledBoundary_tendsto_neg_chart
      (s := s) (by linarith [hs.1]))

/-- A parte real do mesmo bordo tambem desaparece nos zeros Genuine. -/
theorem finiteBracketCoupledSignedBoundary_tendsto_zero_of_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto (fun M : ℕ ↦ finiteBracketCoupledSignedBoundary M s)
      atTop (nhds 0) := by
  have hcomplex :=
    finiteBracketCoupledBoundary_tendsto_zero_of_genuine_zero hs hzero
  have hreal := Complex.continuous_re.continuousAt.tendsto.comp hcomplex
  simpa only [finiteBracketCoupledSignedBoundary_eq_re,
    Complex.zero_re] using hreal

end

end CPFormal.Analytic.Cp
