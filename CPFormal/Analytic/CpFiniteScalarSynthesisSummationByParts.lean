import CPFormal.Analytic.CpFiniteScalarSynthesis

/-!
# Somacao por partes do setor fechado da sintese escalar

O kernel centrado do checkpoint 0.42 possui uma primitiva causal `P_M` com
os dois endpoints nulos. Este modulo aplica a identidade finita de Abel a
essa primitiva sem comprimir os registros antes do pareamento.

O resultado central e uma igualdade exata:

`KernelPairing = M * ClosedBulk`.

Na especializacao angular, isso remove o fator artificial do ledger de
sintese e concentra toda a comparacao com a correcao local dos trios num
unico defeito fechado. Nenhuma hipotese de zero, limite ou linha critica e
usada nas identidades finitas.
-/

open scoped BigOperators

namespace CPFormal.Analytic.Cp

noncomputable section

/-! ## Abel para a primitiva fechada -/

/-- A diferenca forward da primitiva conjugada recupera a coordenada
conjugada do kernel. -/
theorem star_kernelPrefix_forwardDifference
    (M : ℕ) (f : ℕ → ℂ) (k : ℕ) :
    (starRingEnd ℂ) (finitePortSynthesisKernelPrefix M f (k + 1)) -
        (starRingEnd ℂ) (finitePortSynthesisKernelPrefix M f k) =
      (starRingEnd ℂ) (finitePortSynthesisKernelValue M f k) := by
  rw [finitePortSynthesisKernelPrefix_succ]
  simp only [map_add]
  ring

/-- A primitiva fechada tambem possui uma formula sem recursao: prefixo
parcial escalado menos a fracao inteira do observavel de cutoff. -/
theorem finitePortSynthesisKernelPrefix_eq_scaled_prefix_sub_cutoff
    (M : ℕ) (f : ℕ → ℂ) (k : ℕ) :
    finitePortSynthesisKernelPrefix M f k =
      (M : ℂ) * finitePortSynthesis k f -
        (k : ℂ) * finitePortSynthesis M f := by
  classical
  unfold finitePortSynthesisKernelPrefix finitePortSynthesisKernelValue
    finitePortSynthesis
  rw [Finset.sum_sub_distrib, Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Somacao por partes exata do pareamento do kernel. Os dois termos de
endpoint somem porque `P_M(0)=P_M(M)=0`. -/
theorem finitePortSynthesisKernelPairing_summation_by_parts
    (M : ℕ) (f g : ℕ → ℂ) :
    finitePortSynthesisKernelPairing M f g =
      ∑ m ∈ Finset.range (M - 1),
        (starRingEnd ℂ)
            (finitePortSynthesisKernelPrefix M f (m + 1)) *
          (finitePortSynthesisKernelValue M g m -
            finitePortSynthesisKernelValue M g (m + 1)) := by
  have hAbel := sum_range_forwardDifference_mul_eq_cutoff_add_bulk
    (fun k ↦
      (starRingEnd ℂ) (finitePortSynthesisKernelPrefix M f k))
    (fun m ↦ finitePortSynthesisKernelValue M g m) M
  unfold finitePortSynthesisKernelPairing
  simpa only [star_kernelPrefix_forwardDifference,
    finitePortSynthesisKernelPrefix_cutoff,
    finitePortSynthesisKernelPrefix_zero, map_zero, zero_mul,
    sub_zero, zero_add] using hAbel

/-- A constante subtraida pela centralizacao desaparece ao diferenciar o
kernel: resta `M` vezes a diferenca dos registros originais. -/
theorem finitePortSynthesisKernelValue_sub_succ
    (M : ℕ) (g : ℕ → ℂ) (m : ℕ) :
    finitePortSynthesisKernelValue M g m -
        finitePortSynthesisKernelValue M g (m + 1) =
      (M : ℂ) * (g m - g (m + 1)) := by
  simp only [finitePortSynthesisKernelValue]
  ring

/-- Bulk fechado apos Abel, ainda indexado pelos registros originais. -/
def finitePortSynthesisClosedBulk
    (M : ℕ) (f g : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.range (M - 1),
    (starRingEnd ℂ) (finitePortSynthesisKernelPrefix M f (m + 1)) *
      (g m - g (m + 1))

/-- O pareamento inteiro do setor invisivel e exatamente `M` vezes seu bulk
fechado. Nao sobra bordo. -/
theorem finitePortSynthesisKernelPairing_eq_mul_closedBulk
    (M : ℕ) (f g : ℕ → ℂ) :
    finitePortSynthesisKernelPairing M f g =
      (M : ℂ) * finitePortSynthesisClosedBulk M f g := by
  rw [finitePortSynthesisKernelPairing_summation_by_parts]
  simp_rw [finitePortSynthesisKernelValue_sub_succ]
  unfold finitePortSynthesisClosedBulk
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-! ## Especializacao angular e comparacao local -/

/-- Bulk da primitiva fechada dos blocos angulares Genuine. -/
def finiteCanonicalAngularClosedSynthesisBulk
    (M : ℕ) (s : ℂ) : ℂ :=
  finitePortSynthesisClosedBulk M
    (fun m ↦ canonicalAngularGradientBlock m s)
    (fun m ↦ canonicalAngularGradientBlock m (reflectedParameter s))

/-- Na porta Genuine, a primitiva e literalmente a diferenca entre o traco
parcial escalado e o traco completo escalado pelo comprimento parcial. -/
theorem finiteCanonicalAngularKernelPrefix_eq_centered_traces
    (M k : ℕ) (s : ℂ) :
    finitePortSynthesisKernelPrefix M
        (fun m ↦ canonicalAngularGradientBlock m s) k =
      (M : ℂ) * finiteCanonicalAngularTrace k s -
        (k : ℂ) * finiteCanonicalAngularTrace M s := by
  simpa only [finiteCanonicalAngularTrace, finitePortSynthesis] using
    finitePortSynthesisKernelPrefix_eq_scaled_prefix_sub_cutoff M
      (fun m ↦ canonicalAngularGradientBlock m s) k

/-- O bulk fechado aberto somente em tracos angulares Genuine e diferencas
de blocos consecutivos. Esta e a forma pronta para estimativas de cutoff. -/
theorem finiteCanonicalAngularClosedSynthesisBulk_eq_centeredTraceBulk
    (M : ℕ) (s : ℂ) :
    finiteCanonicalAngularClosedSynthesisBulk M s =
      ∑ m ∈ Finset.range (M - 1),
        (starRingEnd ℂ)
            ((M : ℂ) * finiteCanonicalAngularTrace (m + 1) s -
              ((m + 1 : ℕ) : ℂ) *
                finiteCanonicalAngularTrace M s) *
          (canonicalAngularGradientBlock m (reflectedParameter s) -
            canonicalAngularGradientBlock (m + 1)
              (reflectedParameter s)) := by
  unfold finiteCanonicalAngularClosedSynthesisBulk
    finitePortSynthesisClosedBulk
  simp_rw [finiteCanonicalAngularKernelPrefix_eq_centered_traces]

/-- Abel aplicado ao setor angular: o kernel de sintese e `M` vezes o bulk
fechado, coordenada por coordenada. -/
theorem finiteCanonicalAngularSynthesisKernelPairing_eq_mul_closedBulk
    (M : ℕ) (s : ℂ) :
    finiteCanonicalAngularSynthesisKernelPairing M s =
      (M : ℂ) * finiteCanonicalAngularClosedSynthesisBulk M s := by
  exact finitePortSynthesisKernelPairing_eq_mul_closedBulk M
    (fun m ↦ canonicalAngularGradientBlock m s)
    (fun m ↦ canonicalAngularGradientBlock m (reflectedParameter s))

/-- Ledger angular depois de Abel. Todos os termos possuem o mesmo fator
`M`; a igualdade vale inclusive no corte vazio. -/
theorem finiteCanonicalAngularGreenCorrection_closedBulk_scaled_ledger
    (M : ℕ) (s : ℂ) :
    (M : ℂ) *
        (finiteCanonicalAngularGreenCorrection M s +
          finiteCanonicalAngularClosedSynthesisBulk M s) =
      (M : ℂ) *
        (((M : ℂ) - 1) * finiteReflectedGradientPairing (3 * M) s +
          (M : ℂ) * finiteCanonicalAngularLocalGreenCorrection M s) := by
  have hledger :=
    finiteCanonicalAngularGreenCorrection_synthesis_ledger M s
  rw [finiteCanonicalAngularSynthesisKernelPairing_eq_mul_closedBulk]
    at hledger
  linear_combination hledger

/-- Em corte nao vazio, o fator comum pode ser cancelado: a correcao total
mais o bulk fechado e exatamente crescimento diagonal mais correcao local. -/
theorem finiteCanonicalAngularGreenCorrection_add_closedBulk
    {M : ℕ} (hM : 0 < M) (s : ℂ) :
    finiteCanonicalAngularGreenCorrection M s +
        finiteCanonicalAngularClosedSynthesisBulk M s =
      ((M : ℂ) - 1) * finiteReflectedGradientPairing (3 * M) s +
        (M : ℂ) * finiteCanonicalAngularLocalGreenCorrection M s := by
  have hscaled :=
    finiteCanonicalAngularGreenCorrection_closedBulk_scaled_ledger M s
  have hMne : (M : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hM)
  exact mul_left_cancel₀ hMne hscaled

/-- Unico residual que resta ao comparar o bulk de Abel com a correcao
local dos trios. -/
def finiteCanonicalAngularClosedBulkDefect
    (M : ℕ) (s : ℂ) : ℂ :=
  (M : ℂ) * finiteCanonicalAngularLocalGreenCorrection M s -
    finiteCanonicalAngularClosedSynthesisBulk M s

/-- No primeiro bloco nao existe aresta interbloco para o bulk de Abel. A
comparacao reduz-se exatamente a correcao local do unico trio; logo o
cancelamento local--bulk nao foi inserido por definicao. -/
theorem finiteCanonicalAngularClosedBulkDefect_one (s : ℂ) :
    finiteCanonicalAngularClosedBulkDefect 1 s =
      canonicalAngularLocalGreenCorrection 0 s := by
  simp [finiteCanonicalAngularClosedBulkDefect,
    finiteCanonicalAngularClosedSynthesisBulk,
    finitePortSynthesisClosedBulk,
    finiteCanonicalAngularLocalGreenCorrection]

/-- Witness aritmetico: no primeiro trio e em `s=2`, a correcao local vale
`-103/48`. O ponto esta fora do strip e serve somente para refutar uma
identidade universal de cancelamento local--bulk. -/
theorem canonicalAngularLocalGreenCorrection_zero_two :
    canonicalAngularLocalGreenCorrection 0 (2 : ℂ) =
      -(103 : ℂ) / 48 := by
  norm_num [canonicalAngularLocalGreenCorrection,
    positiveDirichletGradient, positiveDirichletValue,
    natDirichletTerm, dirichletTerm, reflectedParameter,
    Complex.cpow_neg, Complex.cpow_neg_one,
    Complex.conj_ofNat, Complex.cpow_one]

/-- O defeito fechado nao e zero por uma identidade algébrica universal. -/
theorem finiteCanonicalAngularClosedBulkDefect_one_two_ne_zero :
    finiteCanonicalAngularClosedBulkDefect 1 (2 : ℂ) ≠ 0 := by
  rw [finiteCanonicalAngularClosedBulkDefect_one,
    canonicalAngularLocalGreenCorrection_zero_two]
  norm_num

/-- Forma descomprimida final: a correcao angular e crescimento diagonal
mais um unico defeito fechado, sem off-diagonal opaco. -/
theorem finiteCanonicalAngularGreenCorrection_eq_diagonalGrowth_add_closedBulkDefect
    {M : ℕ} (hM : 0 < M) (s : ℂ) :
    finiteCanonicalAngularGreenCorrection M s =
      ((M : ℂ) - 1) * finiteReflectedGradientPairing (3 * M) s +
        finiteCanonicalAngularClosedBulkDefect M s := by
  have hledger := finiteCanonicalAngularGreenCorrection_add_closedBulk hM s
  unfold finiteCanonicalAngularClosedBulkDefect
  linear_combination hledger

/-- O observavel escalar inteiro possui agora somente duas parcelas: `M`
vezes a energia Green diagonal e o defeito fechado local--bulk. A igualdade
inclui o corte vazio. -/
theorem finiteCanonicalAngularScalarPairing_eq_mul_green_add_closedBulkDefect
    (M : ℕ) (s : ℂ) :
    finiteCanonicalAngularScalarPairing M s =
      (M : ℂ) * finiteReflectedGradientPairing (3 * M) s +
        finiteCanonicalAngularClosedBulkDefect M s := by
  cases M with
  | zero =>
      simp [finiteCanonicalAngularScalarPairing,
        finiteScalarPortWronskian, finitePortSynthesis,
        finiteCanonicalAngularClosedBulkDefect,
        finiteCanonicalAngularLocalGreenCorrection,
        finiteCanonicalAngularClosedSynthesisBulk,
        finitePortSynthesisClosedBulk]
  | succ M =>
      have hcorrection :=
        finiteCanonicalAngularGreenCorrection_eq_diagonalGrowth_add_closedBulkDefect
          (Nat.succ_pos M) s
      have hbudget :=
        finiteCanonicalAngularScalarPairing_eq_green_add_correction (M + 1) s
      rw [hcorrection] at hbudget
      norm_num at hbudget ⊢
      linear_combination hbudget

/-! ## Consequencia Genuine-first -/

/-- Num zero Genuine, a parcela `M * Green + defeito fechado` tende a zero
porque ela e exatamente o observavel escalar ja certificado, nao uma nova
hipotese sobre o Green. -/
theorem finiteCanonicalAngularMulGreenAddClosedBulkDefect_tendsto_zero_of_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Filter.Tendsto
      (fun M : ℕ ↦
        (M : ℂ) * finiteReflectedGradientPairing (3 * M) s +
          finiteCanonicalAngularClosedBulkDefect M s)
      Filter.atTop (nhds 0) := by
  simpa only [←
    finiteCanonicalAngularScalarPairing_eq_mul_green_add_closedBulkDefect]
    using
      finiteCanonicalAngularScalarPairing_tendsto_zero_of_genuine_zero
        hs hzero

/-- A mesma identidade depois do coeficiente radial do carry. O tilt nao e
reprovado: ele apenas multiplica o observavel Genuine que ja fecha. -/
theorem finiteCanonicalAngularRadialClosedBulkBudget_tendsto_zero_of_genuine_zero
    (p : ℕ) {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Filter.Tendsto
      (fun M : ℕ ↦
        ((cpRadialDifference p (criticalDisplacement s.re) : ℝ) : ℂ) *
          ((M : ℂ) * finiteReflectedGradientPairing (3 * M) s +
            finiteCanonicalAngularClosedBulkDefect M s))
      Filter.atTop (nhds 0) := by
  simpa only [←
    finiteCanonicalAngularScalarPairing_eq_mul_green_add_closedBulkDefect]
    using
      finiteCanonicalAngularRadialScalarPairing_tendsto_zero_of_genuine_zero
        p hs hzero

end

end CPFormal.Analytic.Cp
