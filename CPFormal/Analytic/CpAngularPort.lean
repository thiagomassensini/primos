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

A segunda parte constroi um candidato finito a `Psi` a partir do campo
log-pesado, independentemente de `Phi` e do Green. A identidade Wronskiana
entre essa corrente e o fluxo Green permanece uma obrigacao separada.
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

/-!
## Log-jet finito independente

Construimos agora o candidato finito a corrente `Psi` antes de qualquer
identidade de Green. O campo de vertices e obtido aplicando o gerador de
escala ao monomio de Dirichlet:

`log(n+1) * (n+1)^(-s)`.

Em linguagem analitica, esse e o coeficiente de `-d/ds`; aqui, porem, a
definicao e puramente finita e nao usa derivadas, zeros, Wronskianos ou um
residuo escolhido a posteriori. Os mesmos pesos angulares `1, 2, 0` da porta
`Phi` sao aplicados aos gradientes desse novo campo.

Ainda nao se afirma que esse traco e o retorno TFVD enriquecido, nem que seu
Wronskiano com `Phi` coincide com o fluxo Green ja formalizado. Essas
identificacoes exigem pontes tipadas adicionais.
-/

/-- Campo de Dirichlet vestido pelo gerador logaritmico no vertice `n+1`. -/
def positiveLogDirichletValue (s : ℂ) (n : ℕ) : ℂ :=
  (Real.log (((n + 1 : ℕ) : ℝ)) : ℂ) * positiveDirichletValue s n

/-- A semente em `1` desaparece porque `log 1 = 0`. -/
@[simp] theorem positiveLogDirichletValue_zero (s : ℂ) :
    positiveLogDirichletValue s 0 = 0 := by
  simp [positiveLogDirichletValue]

/-- Gradiente consecutivo do campo de Dirichlet log-pesado. -/
def positiveLogDirichletGradient (s : ℂ) (n : ℕ) : ℂ :=
  positiveLogDirichletValue s (n + 1) - positiveLogDirichletValue s n

/-- Bloco log-jet independente, com os pesos angulares canonicos `1, 2, 0`. -/
def canonicalAngularLogJetBlock (m : ℕ) (s : ℂ) : ℂ :=
  -∑ r ∈ Finset.range 3,
    ((((r + 1) % 3 : ℕ) : ℂ) *
      positiveLogDirichletGradient s (3 * m + r))

/-- Forma de duas arestas do bloco log-jet; a terceira tem peso zero. -/
theorem canonicalAngularLogJetBlock_eq_two_edges
    (m : ℕ) (s : ℂ) :
    canonicalAngularLogJetBlock m s =
      -(positiveLogDirichletGradient s (3 * m) +
        2 * positiveLogDirichletGradient s (3 * m + 1)) := by
  norm_num [canonicalAngularLogJetBlock, Finset.sum_range_succ]

/-- O bloco log-jet aberto em seus tres valores consecutivos. -/
theorem canonicalAngularLogJetBlock_eq_values
    (m : ℕ) (s : ℂ) :
    canonicalAngularLogJetBlock m s =
      positiveLogDirichletValue s (3 * m) +
        positiveLogDirichletValue s (3 * m + 1) -
          2 * positiveLogDirichletValue s (3 * m + 2) := by
  rw [canonicalAngularLogJetBlock_eq_two_edges]
  simp [positiveLogDirichletGradient]
  ring

/-- Soma dos primeiros `M` blocos da corrente log-jet canonica. -/
def finiteCanonicalAngularLogJetTrace (M : ℕ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.range M, canonicalAngularLogJetBlock m s

/-- Acrescentar um centro acrescenta exatamente seu bloco log-jet. -/
theorem finiteCanonicalAngularLogJetTrace_succ (M : ℕ) (s : ℂ) :
    finiteCanonicalAngularLogJetTrace (M + 1) s =
      finiteCanonicalAngularLogJetTrace M s +
        canonicalAngularLogJetBlock M s := by
  unfold finiteCanonicalAngularLogJetTrace
  rw [Finset.sum_range_succ]

/-- Segunda diferenca bracketada do campo log-pesado no centro `3m+3`. -/
def canonicalLogBracketBlock (m : ℕ) (s : ℂ) : ℂ :=
  positiveLogDirichletValue s (3 * m + 1) -
    2 * positiveLogDirichletValue s (3 * m + 2) +
      positiveLogDirichletValue s (3 * m + 3)

/-- Carta bracketada log-pesada ate o corte `M`; sua semente e zero. -/
def finiteCanonicalLogBracketChart (M : ℕ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.range M, canonicalLogBracketBlock m s

/-- Recorrencia de um passo da carta bracketada log-pesada. -/
theorem finiteCanonicalLogBracketChart_succ (M : ℕ) (s : ℂ) :
    finiteCanonicalLogBracketChart (M + 1) s =
      finiteCanonicalLogBracketChart M s + canonicalLogBracketBlock M s := by
  unfold finiteCanonicalLogBracketChart
  rw [Finset.sum_range_succ]

/-!
Identidade finita central: `Psi_M` nao e definido como o termo faltante.
Depois de ambos os lados terem sido construidos independentemente, os pesos
`1,2,0` telescopam e deixam somente o vertice externo `3M+1`.
-/
theorem finiteCanonicalLogBracketChart_eq_logJetTrace_add_outer
    (M : ℕ) (s : ℂ) :
    finiteCanonicalLogBracketChart M s =
      finiteCanonicalAngularLogJetTrace M s +
        positiveLogDirichletValue s (3 * M) := by
  induction M with
  | zero =>
      simp [finiteCanonicalLogBracketChart,
        finiteCanonicalAngularLogJetTrace]
  | succ M ih =>
      rw [finiteCanonicalLogBracketChart_succ,
        finiteCanonicalAngularLogJetTrace_succ, ih,
        canonicalLogBracketBlock,
        canonicalAngularLogJetBlock_eq_values]
      have houter : 3 * (M + 1) = 3 * M + 3 := by omega
      rw [houter]
      ring

/-- Norma exata de um vertice log-pesado. -/
theorem norm_positiveLogDirichletValue (s : ℂ) (n : ℕ) :
    ‖positiveLogDirichletValue s n‖ =
      Real.log (((n + 1 : ℕ) : ℝ)) *
        (((n + 1 : ℕ) : ℝ)) ^ (-s.re) := by
  have hone : (1 : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hlog : 0 ≤ Real.log (((n + 1 : ℕ) : ℝ)) :=
    Real.log_nonneg hone
  unfold positiveLogDirichletValue
  rw [norm_mul, norm_positiveDirichletValue]
  rw [Real.norm_of_nonneg hlog]

/-- O unico bordo externo logaritmico desaparece para `Re(s)>0`. -/
theorem canonicalAngularLogJetOuter_tendsto_zero
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun M : ℕ ↦ positiveLogDirichletValue s (3 * M))
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
  have hratio :
      Tendsto
        (fun M : ℕ ↦
          Real.log (((3 * M + 1 : ℕ) : ℝ)) /
            (((3 * M + 1 : ℕ) : ℝ)) ^ s.re)
        atTop (nhds 0) := by
    exact
      ((isLittleO_log_rpow_atTop hs).tendsto_div_nhds_zero).comp hreal
  have hpoint : ∀ M : ℕ,
      ‖positiveLogDirichletValue s (3 * M)‖ =
        Real.log (((3 * M + 1 : ℕ) : ℝ)) /
          (((3 * M + 1 : ℕ) : ℝ)) ^ s.re := by
    intro M
    rw [norm_positiveLogDirichletValue]
    rw [Real.rpow_neg (by positivity), div_eq_mul_inv]
  simpa only [hpoint] using hratio

end

end CPFormal.Analytic.Cp
