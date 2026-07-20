import CPFormal.Analytic.CpFiniteTfvdLogJetCommutatorDefect

/-!
# Soma por blocos do canal residual log-jet

Este arquivo soma o canal residual do checkpoint 0.32 em cutoffs formados por
blocos completos `3m, 3m+1, 3m+2`. A parte de vertices e submetida a uma
integracao por partes discreta exata:

`sum (Delta log) * crossFlux = cutoff movel + bulk cruzado`.

O endpoint interno desaparece porque `log 1 = 0`. O termo Green permanece
separado e ja possui sua identidade finita independente. Nenhuma anulacao do
bulk cruzado e postulada.
-/

open scoped BigOperators

namespace CPFormal.Analytic.Cp

noncomputable section

/-!
## Integracao por partes finita
-/

/--
Somacao por partes para uma diferenca forward multiplicada por uma corrente
de aresta. A formulacao com `N-1` inclui `N=0` sem convencao externa.
-/
theorem sum_range_forwardDifference_mul_eq_cutoff_add_bulk
    (f g : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (f (n + 1) - f n) * g n) =
      f N * g (N - 1) - f 0 * g 0 +
        ∑ n ∈ Finset.range (N - 1),
          f (n + 1) * (g n - g (n + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      cases N with
      | zero =>
          simp
          ring
      | succ N =>
          rw [Finset.sum_range_succ]
          simp only [Nat.succ_sub_one]
          ring

/-- Peso logaritmico no vertice positivo `n+1`. -/
def positiveLogVertexWeight (n : ℕ) : ℂ :=
  (Real.log (((n + 1 : ℕ) : ℝ)) : ℂ)

/-- O peso do endpoint interno e zero. -/
@[simp] theorem positiveLogVertexWeight_zero :
    positiveLogVertexWeight 0 = 0 := by
  simp [positiveLogVertexWeight]

/-- O salto usado no wedge log-jet e a diferenca forward dos pesos. -/
theorem positiveLogGap_eq_forwardDifference (n : ℕ) :
    positiveLogGap n =
      positiveLogVertexWeight (n + 1) - positiveLogVertexWeight n := by
  rfl

/-- Corrente cruzada entre dois vertices consecutivos, antes do peso log. -/
def reflectedDirichletVertexCrossFlux (n : ℕ) (s : ℂ) : ℂ :=
  (starRingEnd ℂ) (positiveDirichletValue s n) *
      positiveDirichletValue (reflectedParameter s) (n + 1) -
    (starRingEnd ℂ) (positiveDirichletValue s (n + 1)) *
      positiveDirichletValue (reflectedParameter s) n

/-- Fatoracao definicional do fluxo log-jet de vertices. -/
theorem reflectedLogJetVertexFlux_eq_gap_mul_crossFlux
    (n : ℕ) (s : ℂ) :
    reflectedLogJetVertexFlux n s =
      positiveLogGap n * reflectedDirichletVertexCrossFlux n s := by
  rfl

/-- Soma do fluxo log-jet de vertices nas primeiras `N` arestas. -/
def finiteReflectedLogJetVertexFlux (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, reflectedLogJetVertexFlux n s

/-- Endpoint movel produzido pela somacao por partes. -/
def reflectedLogJetMovingCutoff (N : ℕ) (s : ℂ) : ℂ :=
  positiveLogVertexWeight N *
    reflectedDirichletVertexCrossFlux (N - 1) s

/-- Bulk cruzado: variacao consecutiva da corrente, pesada no vertice. -/
def finiteReflectedLogJetCrossBulk (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range (N - 1),
    positiveLogVertexWeight (n + 1) *
      (reflectedDirichletVertexCrossFlux n s -
        reflectedDirichletVertexCrossFlux (n + 1) s)

/-!
Decomposicao exata do fluxo de vertices. Nao ha endpoint interno restante:
seu coeficiente e literalmente `log 1 = 0`.
-/
theorem finiteReflectedLogJetVertexFlux_eq_cutoff_add_crossBulk
    (N : ℕ) (s : ℂ) :
    finiteReflectedLogJetVertexFlux N s =
      reflectedLogJetMovingCutoff N s +
        finiteReflectedLogJetCrossBulk N s := by
  unfold finiteReflectedLogJetVertexFlux reflectedLogJetMovingCutoff
    finiteReflectedLogJetCrossBulk
  simp_rw [reflectedLogJetVertexFlux_eq_gap_mul_crossFlux,
    positiveLogGap_eq_forwardDifference]
  simpa using
    (sum_range_forwardDifference_mul_eq_cutoff_add_bulk
      positiveLogVertexWeight
      (fun n ↦ reflectedDirichletVertexCrossFlux n s) N)

/-!
## Reagrupamento por blocos completos
-/

/-- Reagrupamento exato de uma soma de comprimento `3M` em trios. -/
theorem sum_range_threeBlocks_eq_range
    (f : ℕ → ℂ) (M : ℕ) :
    (∑ m ∈ Finset.range M,
      (f (3 * m) + f (3 * m + 1) + f (3 * m + 2))) =
        ∑ n ∈ Finset.range (3 * M), f n := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      have hcut : 3 * (M + 1) = 3 * M + 3 := by omega
      rw [hcut, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ]
      ring

/-- Sintese de um trio somente depois de manter suas tres coordenadas. -/
def TfvdWedgeTriple.total (x : TfvdWedgeTriple) : ℂ :=
  x.first + x.second + x.dormant

/-- Soma por blocos completos do canal residual do 0.32. -/
def finiteCanonicalLogJetCommutatorResidualTrace
    (p M : ℕ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.range M,
    TfvdWedgeTriple.total
      (canonicalLogJetCommutatorResidualTriple p m s)

/-- A soma de trios residuais e a soma consecutiva das primeiras `3M` arestas. -/
theorem finiteCanonicalLogJetCommutatorResidualTrace_eq_range
    (p M : ℕ) (s : ℂ) :
    finiteCanonicalLogJetCommutatorResidualTrace p M s =
      ∑ n ∈ Finset.range (3 * M),
        logJetCommutatorResidualChannel p n s := by
  unfold finiteCanonicalLogJetCommutatorResidualTrace
    TfvdWedgeTriple.total canonicalLogJetCommutatorResidualTriple
  exact sum_range_threeBlocks_eq_range
    (fun n ↦ logJetCommutatorResidualChannel p n s) M

/-- A soma das arestas Green canonicas e o fluxo Green orientado ja provado. -/
theorem sum_range_canonicalOrientedCpGreenEdge_eq_finiteOrientedCpGreenFlux
    (p N : ℕ) (s : ℂ) :
    (∑ n ∈ Finset.range N, canonicalOrientedCpGreenEdge p n s) =
      finiteOrientedCpGreenFlux p N s := by
  change finiteTfvdCpGreenDiagonal p N s = finiteOrientedCpGreenFlux p N s
  exact finiteTfvdCpGreenDiagonal_eq_finiteOrientedCpGreenFlux p N s

/--
Primeira forma fechada da soma residual: fluxo de vertices mais o canal
Green diagonal com o coeficiente herdado do 0.32.
-/
theorem finiteCanonicalLogJetCommutatorResidualTrace_eq_vertex_add_green
    (p M : ℕ) (s : ℂ) :
    finiteCanonicalLogJetCommutatorResidualTrace p M s =
      finiteReflectedLogJetVertexFlux (3 * M) s +
        ((Real.log (p : ℝ) : ℂ) - 1) *
          finiteOrientedCpGreenFlux p (3 * M) s := by
  rw [finiteCanonicalLogJetCommutatorResidualTrace_eq_range]
  simp only [logJetCommutatorResidualChannel]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_range_canonicalOrientedCpGreenEdge_eq_finiteOrientedCpGreenFlux]
  rfl

/-!
Coracao da soma residual: endpoint movel + bulk cruzado + Green diagonal.
-/
theorem finiteCanonicalLogJetCommutatorResidualTrace_eq_cutoff_add_bulk_add_green
    (p M : ℕ) (s : ℂ) :
    finiteCanonicalLogJetCommutatorResidualTrace p M s =
      (reflectedLogJetMovingCutoff (3 * M) s +
        finiteReflectedLogJetCrossBulk (3 * M) s) +
          ((Real.log (p : ℝ) : ℂ) - 1) *
            finiteOrientedCpGreenFlux p (3 * M) s := by
  rw [finiteCanonicalLogJetCommutatorResidualTrace_eq_vertex_add_green,
    finiteReflectedLogJetVertexFlux_eq_cutoff_add_crossBulk]

/-!
## Tracos completos do comutador e do defeito
-/

/-- Soma por blocos do wedge do comutador. -/
def finiteCanonicalCpLogJetCommutatorWedgeTrace
    (p M : ℕ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.range M,
    TfvdWedgeTriple.total
      (canonicalReflectedCpLogJetCommutatorWedgeTriple p m s)

/-- Reagrupamento consecutivo do wedge do comutador. -/
theorem finiteCanonicalCpLogJetCommutatorWedgeTrace_eq_range
    (p M : ℕ) (s : ℂ) :
    finiteCanonicalCpLogJetCommutatorWedgeTrace p M s =
      ∑ n ∈ Finset.range (3 * M),
        canonicalReflectedCpLogJetCommutatorWedge p n s := by
  unfold finiteCanonicalCpLogJetCommutatorWedgeTrace
    TfvdWedgeTriple.total
    canonicalReflectedCpLogJetCommutatorWedgeTriple
  exact sum_range_threeBlocks_eq_range
    (fun n ↦ canonicalReflectedCpLogJetCommutatorWedge p n s) M

/-- O traco completo do comutador continua sendo `-log(p)` vezes Green. -/
theorem finiteCanonicalCpLogJetCommutatorWedgeTrace_eq_neg_log_mul_green
    (p : ℕ) (hp : Nat.Prime p) (M : ℕ) (s : ℂ) :
    finiteCanonicalCpLogJetCommutatorWedgeTrace p M s =
      -(Real.log (p : ℝ) : ℂ) *
        finiteOrientedCpGreenFlux p (3 * M) s := by
  rw [finiteCanonicalCpLogJetCommutatorWedgeTrace_eq_range]
  simp_rw [canonicalReflectedCpLogJetCommutatorWedge_eq_neg_log_mul_green
    p hp]
  rw [← Finset.mul_sum,
    sum_range_canonicalOrientedCpGreenEdge_eq_finiteOrientedCpGreenFlux]

/-- Soma por blocos completos do defeito log-jet--Green. -/
def finiteCanonicalLogJetGreenDefectTrace
    (p M : ℕ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.range M,
    TfvdWedgeTriple.total
      (canonicalLogJetGreenDefectTriple p m s)

/-- Reagrupamento consecutivo do defeito. -/
theorem finiteCanonicalLogJetGreenDefectTrace_eq_range
    (p M : ℕ) (s : ℂ) :
    finiteCanonicalLogJetGreenDefectTrace p M s =
      ∑ n ∈ Finset.range (3 * M),
        logJetGreenEdgeDefect p n s := by
  unfold finiteCanonicalLogJetGreenDefectTrace
    TfvdWedgeTriple.total canonicalLogJetGreenDefectTriple
  exact sum_range_threeBlocks_eq_range
    (fun n ↦ logJetGreenEdgeDefect p n s) M

/-- O defeito completo e fluxo de vertices menos Green diagonal. -/
theorem finiteCanonicalLogJetGreenDefectTrace_eq_vertex_sub_green
    (p M : ℕ) (s : ℂ) :
    finiteCanonicalLogJetGreenDefectTrace p M s =
      finiteReflectedLogJetVertexFlux (3 * M) s -
        finiteOrientedCpGreenFlux p (3 * M) s := by
  rw [finiteCanonicalLogJetGreenDefectTrace_eq_range]
  simp only [logJetGreenEdgeDefect]
  rw [Finset.sum_sub_distrib,
    sum_range_canonicalOrientedCpGreenEdge_eq_finiteOrientedCpGreenFlux]
  rfl

/-!
Formula final do cutoff completo: o defeito se separa em endpoint movel,
bulk cruzado e menos o Green diagonal.
-/
theorem finiteCanonicalLogJetGreenDefectTrace_eq_cutoff_add_bulk_sub_green
    (p M : ℕ) (s : ℂ) :
    finiteCanonicalLogJetGreenDefectTrace p M s =
      reflectedLogJetMovingCutoff (3 * M) s +
        finiteReflectedLogJetCrossBulk (3 * M) s -
          finiteOrientedCpGreenFlux p (3 * M) s := by
  rw [finiteCanonicalLogJetGreenDefectTrace_eq_vertex_sub_green,
    finiteReflectedLogJetVertexFlux_eq_cutoff_add_crossBulk]

/-- A decomposicao do 0.32 permanece exata depois da soma por blocos. -/
theorem finiteCanonicalLogJetGreenDefectTrace_eq_commutator_add_residual
    (p : ℕ) (hp : Nat.Prime p) (M : ℕ) (s : ℂ) :
    finiteCanonicalLogJetGreenDefectTrace p M s =
      finiteCanonicalCpLogJetCommutatorWedgeTrace p M s +
        finiteCanonicalLogJetCommutatorResidualTrace p M s := by
  rw [finiteCanonicalLogJetGreenDefectTrace_eq_vertex_sub_green,
    finiteCanonicalCpLogJetCommutatorWedgeTrace_eq_neg_log_mul_green
      p hp M s,
    finiteCanonicalLogJetCommutatorResidualTrace_eq_vertex_add_green]
  ring

/-!
## Witness de bulk cruzado em um bloco completo
-/

/-- Primeira corrente cruzada em `s=0`. -/
theorem reflectedDirichletVertexCrossFlux_zero_zero :
    reflectedDirichletVertexCrossFlux 0 0 = -(1 : ℂ) / 2 := by
  norm_num [reflectedDirichletVertexCrossFlux,
    positiveDirichletValue, reflectedParameter, Complex.cpow_neg_one]

/-- Segunda corrente cruzada em `s=0`. -/
theorem reflectedDirichletVertexCrossFlux_one_zero :
    reflectedDirichletVertexCrossFlux 1 0 = -(1 : ℂ) / 6 := by
  norm_num [reflectedDirichletVertexCrossFlux,
    positiveDirichletValue, reflectedParameter, Complex.cpow_neg_one]

/-- Terceira corrente cruzada em `s=0`. -/
theorem reflectedDirichletVertexCrossFlux_two_zero :
    reflectedDirichletVertexCrossFlux 2 0 = -(1 : ℂ) / 12 := by
  norm_num [reflectedDirichletVertexCrossFlux,
    positiveDirichletValue, reflectedParameter, Complex.cpow_neg_one]

/-- Valor fechado do bulk cruzado no primeiro bloco completo. -/
theorem finiteReflectedLogJetCrossBulk_three_zero :
    finiteReflectedLogJetCrossBulk 3 0 =
      (((-(Real.log 2) / 3 - Real.log 3 / 12 : ℝ)) : ℂ) := by
  norm_num [finiteReflectedLogJetCrossBulk, Finset.sum_range_succ,
    positiveLogVertexWeight,
    reflectedDirichletVertexCrossFlux_zero_zero,
    reflectedDirichletVertexCrossFlux_one_zero,
    reflectedDirichletVertexCrossFlux_two_zero]
  push_cast
  ring

/-!
O bulk cruzado nao pode ser apagado por uma identidade universal: ele ja e
estritamente negativo, portanto nao nulo, no cutoff completo `N=3,s=0`.
-/
theorem finiteReflectedLogJetCrossBulk_three_zero_ne_zero :
    finiteReflectedLogJetCrossBulk 3 0 ≠ 0 := by
  rw [finiteReflectedLogJetCrossBulk_three_zero]
  have hlogTwo : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hlogThree : 0 < Real.log (3 : ℝ) :=
    Real.log_pos (by norm_num)
  have hreal :
      -(Real.log 2) / 3 - Real.log 3 / 12 < 0 := by
    nlinarith
  have hneReal :
      -(Real.log 2) / 3 - Real.log 3 / 12 ≠ 0 :=
    ne_of_lt hreal
  exact_mod_cast hneReal

end

end CPFormal.Analytic.Cp
