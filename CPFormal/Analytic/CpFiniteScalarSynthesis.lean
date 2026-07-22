import CPFormal.Analytic.CpFiniteGenuineOneSidedGreenBudget
import CPFormal.Analytic.CpGenuineSecondDifferenceIdentity

/-!
# Sintese escalar finita e setor fechado de proveniencia

A sintese `sum_m z_m` e um observador escalar. Ela nao apaga os registros
sem deixar um ledger: a parte invisivel e o campo centrado

`K_M(z)_m = M * z_m - sum_{j<M} z_j`.

Este modulo prova que `K_M(z)` tem soma zero, possui uma primitiva de prefixos
com os dois endpoints nulos e mede exatamente a diferenca entre parear antes
ou depois da sintese. A especializacao angular mantem separados o Green
diagonal, a correcao local do trio e o setor invisivel da sintese.

Nenhuma hipotese de zero entra nas identidades finitas. Um zero Genuine e
usado somente no fim, para anular o observavel escalar; ele nao e convertido
em anulacao coordenada.
-/

open scoped BigOperators Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-! ## Kernel escalado da sintese -/

/-- Coordenada centrada, sem divisao, perdida pela sintese escalar. -/
def finitePortSynthesisKernelValue
    (M : ℕ) (f : ℕ → ℂ) (m : ℕ) : ℂ :=
  (M : ℂ) * f m - finitePortSynthesis M f

/-- O campo centrado possui sintese exatamente nula em todo corte. -/
theorem finitePortSynthesisKernelValue_sum_eq_zero
    (M : ℕ) (f : ℕ → ℂ) :
    (∑ m ∈ Finset.range M,
      finitePortSynthesisKernelValue M f m) = 0 := by
  simp [finitePortSynthesisKernelValue, finitePortSynthesis,
    Finset.sum_sub_distrib, Finset.mul_sum]

/-- Primitiva causal do setor invisivel da sintese. -/
def finitePortSynthesisKernelPrefix
    (M : ℕ) (f : ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑ m ∈ Finset.range k, finitePortSynthesisKernelValue M f m

@[simp] theorem finitePortSynthesisKernelPrefix_zero
    (M : ℕ) (f : ℕ → ℂ) :
    finitePortSynthesisKernelPrefix M f 0 = 0 := by
  simp [finitePortSynthesisKernelPrefix]

/-- Cada coordenada centrada e o incremento da sua primitiva de prefixos. -/
theorem finitePortSynthesisKernelPrefix_succ
    (M : ℕ) (f : ℕ → ℂ) (k : ℕ) :
    finitePortSynthesisKernelPrefix M f (k + 1) =
      finitePortSynthesisKernelPrefix M f k +
        finitePortSynthesisKernelValue M f k := by
  simp [finitePortSynthesisKernelPrefix, Finset.sum_range_succ]

/-- O segundo endpoint tambem e zero: o setor invisivel e um fluxo fechado. -/
@[simp] theorem finitePortSynthesisKernelPrefix_cutoff
    (M : ℕ) (f : ℕ → ℂ) :
    finitePortSynthesisKernelPrefix M f M = 0 := by
  exact finitePortSynthesisKernelValue_sum_eq_zero M f

/-! ## Pareamento antes e depois da sintese -/

/-- Pareamento diagonal de duas familias, preservando o registro `m`. -/
def finitePortDiagonalPairing
    (M : ℕ) (f g : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.range M, (starRingEnd ℂ) (f m) * g m

/-- Pareamento do setor invisivel das duas familias. -/
def finitePortSynthesisKernelPairing
    (M : ℕ) (f g : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.range M,
    (starRingEnd ℂ) (finitePortSynthesisKernelValue M f m) *
      finitePortSynthesisKernelValue M g m

/--
Ledger exato da sintese: parear os vetores centrados mais parear as duas
somas escalares recupera `M^2` vezes o pareamento diagonal.
-/
theorem finitePortSynthesis_pairing_ledger
    (M : ℕ) (f g : ℕ → ℂ) :
    (M : ℂ) *
          ((starRingEnd ℂ) (finitePortSynthesis M f) *
            finitePortSynthesis M g) +
        finitePortSynthesisKernelPairing M f g =
      (M : ℂ) ^ 2 * finitePortDiagonalPairing M f g := by
  classical
  unfold finitePortSynthesisKernelPairing finitePortDiagonalPairing
  have hlocal (m : ℕ) :
      (starRingEnd ℂ)
            ((M : ℂ) * f m - finitePortSynthesis M f) *
          ((M : ℂ) * g m - finitePortSynthesis M g) =
        (M : ℂ) ^ 2 * (starRingEnd ℂ) (f m) * g m -
          (M : ℂ) * (starRingEnd ℂ) (f m) *
            finitePortSynthesis M g -
          (M : ℂ) * (starRingEnd ℂ) (finitePortSynthesis M f) * g m +
          (starRingEnd ℂ) (finitePortSynthesis M f) *
            finitePortSynthesis M g := by
    simp only [map_sub, map_mul, map_natCast]
    ring
  have hconjSum :
      (∑ m ∈ Finset.range M, (starRingEnd ℂ) (f m)) =
        (starRingEnd ℂ) (finitePortSynthesis M f) := by
    simp [finitePortSynthesis, map_sum]
  have hgSum :
      (∑ m ∈ Finset.range M, g m) = finitePortSynthesis M g := by
    rfl
  have hcrossF :
      (∑ m ∈ Finset.range M,
        (M : ℂ) * (starRingEnd ℂ) (f m) *
          finitePortSynthesis M g) =
        (M : ℂ) * (starRingEnd ℂ) (finitePortSynthesis M f) *
          finitePortSynthesis M g := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, hconjSum]
  have hcrossG :
      (∑ m ∈ Finset.range M,
        (M : ℂ) * (starRingEnd ℂ) (finitePortSynthesis M f) * g m) =
        (M : ℂ) * (starRingEnd ℂ) (finitePortSynthesis M f) *
          finitePortSynthesis M g := by
    rw [← Finset.mul_sum, hgSum]
  simp_rw [finitePortSynthesisKernelValue, hlocal]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hcrossF, hcrossG]
  simp [nsmul_eq_mul]
  rw [Finset.mul_sum]
  ring

/-- O Wronskiano diagonal geral e a diferenca dos dois pareamentos diagonais. -/
theorem finiteDiagonalPortWronskian_eq_pairings
    (M : ℕ) (phi psi phiSharp psiSharp : ℕ → ℂ) :
    finiteDiagonalPortWronskian M phi psi phiSharp psiSharp =
      finitePortDiagonalPairing M psi phiSharp -
        finitePortDiagonalPairing M phi psiSharp := by
  classical
  unfold finiteDiagonalPortWronskian finitePortDiagonalPairing
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  simp [finitePortWedgeEntry, hm]

/-- Wronskiano carregado pelo setor de soma zero das quatro portas. -/
def finitePortSynthesisKernelWronskian
    (M : ℕ) (phi psi phiSharp psiSharp : ℕ → ℂ) : ℂ :=
  finitePortSynthesisKernelPairing M psi phiSharp -
    finitePortSynthesisKernelPairing M phi psiSharp

/--
Versao Wronskiana do ledger: a compressao escalar e o setor fechado
reconstroem exatamente a diagonal preservada, sem identificar soma zero com
vetor zero.
-/
theorem finiteScalarPortWronskian_synthesis_ledger
    (M : ℕ) (phi psi phiSharp psiSharp : ℕ → ℂ) :
    (M : ℂ) *
          finiteScalarPortWronskian M phi psi phiSharp psiSharp +
        finitePortSynthesisKernelWronskian
          M phi psi phiSharp psiSharp =
      (M : ℂ) ^ 2 *
        finiteDiagonalPortWronskian M phi psi phiSharp psiSharp := by
  have hleft := finitePortSynthesis_pairing_ledger M psi phiSharp
  have hright := finitePortSynthesis_pairing_ledger M phi psiSharp
  unfold finiteScalarPortWronskian finitePortSynthesisKernelWronskian
  rw [finiteDiagonalPortWronskian_eq_pairings]
  linear_combination hleft - hright

/-- A interferencia off-diagonal e determinada pelo setor fechado e pela
diagonal; nao e um residual sem proveniencia. -/
theorem finiteOffDiagonalPortWronskian_synthesis_ledger
    (M : ℕ) (phi psi phiSharp psiSharp : ℕ → ℂ) :
    (M : ℂ) *
          finiteOffDiagonalPortWronskian
            M phi psi phiSharp psiSharp +
        finitePortSynthesisKernelWronskian
          M phi psi phiSharp psiSharp =
      ((M : ℂ) ^ 2 - (M : ℂ)) *
        finiteDiagonalPortWronskian M phi psi phiSharp psiSharp := by
  have hledger := finiteScalarPortWronskian_synthesis_ledger
    M phi psi phiSharp psiSharp
  have hsplit := finiteScalarPortWronskian_eq_diagonal_add_offDiagonal
    M phi psi phiSharp psiSharp
  rw [hsplit] at hledger
  linear_combination hledger

/-- Num corte cuja sintese zera, o kernel escalado retém cada coordenada. -/
theorem finitePortSynthesisKernelValue_of_synthesis_eq_zero
    {M : ℕ} {f : ℕ → ℂ}
    (hzero : finitePortSynthesis M f = 0) (m : ℕ) :
    finitePortSynthesisKernelValue M f m = (M : ℂ) * f m := by
  simp [finitePortSynthesisKernelValue, hzero]

/-- Se as duas sinteses zeram, todo o pareamento diagonal migra para o
setor fechado; ele nao desaparece coordenada a coordenada. -/
theorem finitePortSynthesisKernelPairing_of_syntheses_eq_zero
    {M : ℕ} {f g : ℕ → ℂ}
    (hf : finitePortSynthesis M f = 0)
    (hg : finitePortSynthesis M g = 0) :
    finitePortSynthesisKernelPairing M f g =
      (M : ℂ) ^ 2 * finitePortDiagonalPairing M f g := by
  have hledger := finitePortSynthesis_pairing_ledger M f g
  simpa [hf, hg] using hledger

/-! ## Especializacao Genuine--angular--Green -/

/-- Setor fechado produzido pelos blocos angulares canonicos. -/
def finiteCanonicalAngularSynthesisKernelPairing
    (M : ℕ) (s : ℂ) : ℂ :=
  finitePortSynthesisKernelPairing M
    (fun m ↦ canonicalAngularGradientBlock m s)
    (fun m ↦ canonicalAngularGradientBlock m (reflectedParameter s))

/-- A sintese angular finita e literalmente a soma das segundas diferencas
canonicas, com semente, menos o vertice externo. -/
theorem finiteCanonicalAngularTrace_eq_secondDifferenceSynthesis_sub_outer
    (M : ℕ) (s : ℂ) :
    finiteCanonicalAngularTrace M s =
      1 +
          ∑ k ∈ Finset.range M,
            CPFormal.centeredSecondDifference
              (dirichletTerm s)
              (CPFormal.Genuine.Cp.alignedCenter 3 k) 1 -
        positiveDirichletValue s (3 * M) := by
  have hentry (k : ℕ) :
      realCpSaturatedBracket 3 k s =
        CPFormal.centeredSecondDifference
          (dirichletTerm s)
          (CPFormal.Genuine.Cp.alignedCenter 3 k) 1 := by
    rw [realCpSaturatedBracket_eq_saturatedBracket]
    rw [← CPFormal.Genuine.Cp.bracket_eq_saturatedBracket
      3 (by norm_num) (by norm_num)]
    exact CPFormal.Genuine.Cp.bracket_three_eq_centeredSecondDifference
      (dirichletTerm s) (CPFormal.Genuine.Cp.alignedCenter 3 k)
  have hchart :=
    finiteBracketedDirichletChart_three_eq_angularTrace_add_outer M s
  have hone := finiteBracketedDirichletChart_three_eq_one_add_trace M s
  unfold finiteCanonicalBracketTrace at hone
  simp_rw [hentry] at hone
  linear_combination hone - hchart

/-- O ledger geral especializado a porta angular. -/
theorem finiteCanonicalAngularScalarPairing_synthesis_ledger
    (M : ℕ) (s : ℂ) :
    (M : ℂ) * finiteCanonicalAngularScalarPairing M s +
        finiteCanonicalAngularSynthesisKernelPairing M s =
      (M : ℂ) ^ 2 * finiteCanonicalAngularPairingDiagonal M s := by
  have hledger := finitePortSynthesis_pairing_ledger M
    (fun m ↦ canonicalAngularGradientBlock m s)
    (fun m ↦ canonicalAngularGradientBlock m (reflectedParameter s))
  simpa only [finiteCanonicalAngularSynthesisKernelPairing,
    finiteCanonicalAngularScalarPairing_eq_product,
    finiteCanonicalAngularTrace, finitePortSynthesis,
    finitePortDiagonalPairing,
    finiteCanonicalAngularPairingDiagonal_eq_sum,
    canonicalAngularPairingEntry] using hledger

/--
Forma Green do ledger: a diagonal se abre em energia Green e correcao local,
enquanto toda perda da sintese permanece no kernel fechado.
-/
theorem finiteCanonicalAngularScalarPairing_synthesis_green_ledger
    (M : ℕ) (s : ℂ) :
    (M : ℂ) * finiteCanonicalAngularScalarPairing M s +
        finiteCanonicalAngularSynthesisKernelPairing M s =
      (M : ℂ) ^ 2 *
        (finiteReflectedGradientPairing (3 * M) s +
          finiteCanonicalAngularLocalGreenCorrection M s) := by
  rw [finiteCanonicalAngularScalarPairing_synthesis_ledger,
    finiteCanonicalAngularPairingDiagonal_eq_green_add_localCorrection]

/--
O off-diagonal deixa de ser uma caixa preta: a correcao total e determinada
exatamente pelo setor fechado, pela energia Green e pela correcao local.
-/
theorem finiteCanonicalAngularGreenCorrection_synthesis_ledger
    (M : ℕ) (s : ℂ) :
    (M : ℂ) * finiteCanonicalAngularGreenCorrection M s +
        finiteCanonicalAngularSynthesisKernelPairing M s =
      ((M : ℂ) ^ 2 - (M : ℂ)) *
          finiteReflectedGradientPairing (3 * M) s +
        (M : ℂ) ^ 2 *
          finiteCanonicalAngularLocalGreenCorrection M s := by
  have hsynthesis :=
    finiteCanonicalAngularScalarPairing_synthesis_green_ledger M s
  have hbudget :=
    finiteCanonicalAngularScalarPairing_eq_green_add_correction M s
  rw [hbudget] at hsynthesis
  linear_combination hsynthesis

/-!
## Consequencia Genuine-first para o observavel escalar

O zero Genuine fecha somente o observavel. O ledger acima registra onde fica
a energia coordenada; o teorema abaixo deliberadamente nao conclui que o
kernel fechado ou a diagonal zeram.
-/

/-- Multiplicar o observavel escalar pelo coeficiente radial preserva seu
fechamento num unico zero Genuine. -/
theorem finiteCanonicalAngularRadialScalarPairing_tendsto_zero_of_genuine_zero
    (p : ℕ) {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
      (fun M : ℕ ↦
        ((cpRadialDifference p (criticalDisplacement s.re) : ℝ) : ℂ) *
          finiteCanonicalAngularScalarPairing M s)
      atTop (nhds 0) := by
  have hscalar :=
    finiteCanonicalAngularScalarPairing_tendsto_zero_of_genuine_zero
      hs hzero
  simpa using tendsto_const_nhds.mul hscalar

/-- A mesma afirmacao escrita no ledger `Green + correcao`, ainda sem
postular fechamento separado da correcao. -/
theorem finiteCanonicalAngularRadialGreenBudget_tendsto_zero_of_genuine_zero
    (p : ℕ) {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
      (fun M : ℕ ↦
        ((cpRadialDifference p (criticalDisplacement s.re) : ℝ) : ℂ) *
          (finiteReflectedGradientPairing (3 * M) s +
            finiteCanonicalAngularGreenCorrection M s))
      atTop (nhds 0) := by
  simpa only [← finiteCanonicalAngularScalarPairing_eq_green_add_correction]
    using
      finiteCanonicalAngularRadialScalarPairing_tendsto_zero_of_genuine_zero
        p hs hzero

end

end CPFormal.Analytic.Cp
