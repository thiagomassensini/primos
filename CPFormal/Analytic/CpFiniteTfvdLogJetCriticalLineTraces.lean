import CPFormal.Analytic.CpFiniteTfvdLogJetResidualReflection

/-!
# Colapso dos tracos log-jet na linha critica

O checkpoint 0.35 provou que o limite residual `B(s)` e anti-Hermitiano e,
portanto, puramente imaginario na linha critica. Este arquivo recombina essa
informacao com o canal Green radial ja formalizado.

O coeficiente do fluxo Green orientado e

`p^delta - p^(-delta)`, com `delta = Re(s)-1/2`.

Logo ele se anula literalmente quando `Re(s)=1/2`, em todo corte finito.
Inserindo essa identidade nas formulas do 0.33, o traco do comutador zera e
os tracos residual e de defeito colapsam para o mesmo fluxo de vertices.
Ambos convergem para `B(s)` e possuem parte real zero; nenhuma anulacao da
parte imaginaria e postulada.
-/

open scoped BigOperators Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-!
## Anulacao exata do canal Green
-/

/-- Na linha critica, o deslocamento radial e literalmente zero. -/
theorem criticalDisplacement_eq_zero_of_re_eq_half
    {s : ℂ} (hs : s.re = 1 / 2) :
    criticalDisplacement s.re = 0 := by
  norm_num [criticalDisplacement, hs]

/-- O fluxo Green orientado se anula em todo corte da linha critica. -/
theorem finiteOrientedCpGreenFlux_eq_zero_of_re_eq_half
    (p M : ℕ) (hp : Nat.Prime p) {s : ℂ} (hs : s.re = 1 / 2) :
    finiteOrientedCpGreenFlux p M s = 0 := by
  rw [finiteOrientedCpGreenFlux_eq_radialDifference_mul_pairing p M hp s,
    criticalDisplacement_eq_zero_of_re_eq_half hs]
  simp [cpRadialDifference]

/-!
## Estrutura puramente imaginaria dos termos de Abel
-/

/-- A soma finita de vertices possui parte real zero na linha critica. -/
theorem finiteReflectedLogJetVertexFlux_re_eq_zero_of_re_eq_half
    (N : ℕ) {s : ℂ} (hs : s.re = 1 / 2) :
    (finiteReflectedLogJetVertexFlux N s).re = 0 := by
  have hanti := finiteReflectedLogJetVertexFlux_reflectedParameter N s
  rw [reflectedParameter_eq_self_of_re_eq_half hs] at hanti
  exact re_eq_zero_of_eq_neg_conj hanti

/-- O cutoff movel tambem possui parte real zero na linha critica. -/
theorem reflectedLogJetMovingCutoff_re_eq_zero_of_re_eq_half
    (N : ℕ) {s : ℂ} (hs : s.re = 1 / 2) :
    (reflectedLogJetMovingCutoff N s).re = 0 := by
  have hanti := reflectedLogJetMovingCutoff_reflectedParameter N s
  rw [reflectedParameter_eq_self_of_re_eq_half hs] at hanti
  exact re_eq_zero_of_eq_neg_conj hanti

/-!
## Colapso dos tres tracos completos
-/

/-- Na linha critica, o traco residual perde exatamente o termo Green. -/
theorem finiteCanonicalLogJetCommutatorResidualTrace_eq_vertex_of_re_eq_half
    (p : ℕ) (hp : Nat.Prime p) (M : ℕ)
    {s : ℂ} (hs : s.re = 1 / 2) :
    finiteCanonicalLogJetCommutatorResidualTrace p M s =
      finiteReflectedLogJetVertexFlux (3 * M) s := by
  rw [finiteCanonicalLogJetCommutatorResidualTrace_eq_vertex_add_green,
    finiteOrientedCpGreenFlux_eq_zero_of_re_eq_half p (3 * M) hp hs]
  simp

/-- Forma de Abel do mesmo colapso residual. -/
theorem finiteCanonicalLogJetCommutatorResidualTrace_eq_cutoff_add_bulk_of_re_eq_half
    (p : ℕ) (hp : Nat.Prime p) (M : ℕ)
    {s : ℂ} (hs : s.re = 1 / 2) :
    finiteCanonicalLogJetCommutatorResidualTrace p M s =
      reflectedLogJetMovingCutoff (3 * M) s +
        finiteReflectedLogJetCrossBulk (3 * M) s := by
  rw [finiteCanonicalLogJetCommutatorResidualTrace_eq_cutoff_add_bulk_add_green,
    finiteOrientedCpGreenFlux_eq_zero_of_re_eq_half p (3 * M) hp hs]
  simp

/-- O traco completo do comutador e zero em cada corte da linha critica. -/
theorem finiteCanonicalCpLogJetCommutatorWedgeTrace_eq_zero_of_re_eq_half
    (p : ℕ) (hp : Nat.Prime p) (M : ℕ)
    {s : ℂ} (hs : s.re = 1 / 2) :
    finiteCanonicalCpLogJetCommutatorWedgeTrace p M s = 0 := by
  rw [finiteCanonicalCpLogJetCommutatorWedgeTrace_eq_neg_log_mul_green
      p hp M s,
    finiteOrientedCpGreenFlux_eq_zero_of_re_eq_half p (3 * M) hp hs]
  simp

/-- Na linha critica, o traco do defeito perde exatamente o termo Green. -/
theorem finiteCanonicalLogJetGreenDefectTrace_eq_vertex_of_re_eq_half
    (p : ℕ) (hp : Nat.Prime p) (M : ℕ)
    {s : ℂ} (hs : s.re = 1 / 2) :
    finiteCanonicalLogJetGreenDefectTrace p M s =
      finiteReflectedLogJetVertexFlux (3 * M) s := by
  rw [finiteCanonicalLogJetGreenDefectTrace_eq_vertex_sub_green,
    finiteOrientedCpGreenFlux_eq_zero_of_re_eq_half p (3 * M) hp hs]
  simp

/-- Forma de Abel do mesmo colapso do defeito. -/
theorem finiteCanonicalLogJetGreenDefectTrace_eq_cutoff_add_bulk_of_re_eq_half
    (p : ℕ) (hp : Nat.Prime p) (M : ℕ)
    {s : ℂ} (hs : s.re = 1 / 2) :
    finiteCanonicalLogJetGreenDefectTrace p M s =
      reflectedLogJetMovingCutoff (3 * M) s +
        finiteReflectedLogJetCrossBulk (3 * M) s := by
  rw [finiteCanonicalLogJetGreenDefectTrace_eq_cutoff_add_bulk_sub_green,
    finiteOrientedCpGreenFlux_eq_zero_of_re_eq_half p (3 * M) hp hs]
  simp

/-- Residual e defeito tornam-se o mesmo traco na linha critica. -/
theorem finiteCanonicalLogJetGreenDefectTrace_eq_residual_of_re_eq_half
    (p : ℕ) (hp : Nat.Prime p) (M : ℕ)
    {s : ℂ} (hs : s.re = 1 / 2) :
    finiteCanonicalLogJetGreenDefectTrace p M s =
      finiteCanonicalLogJetCommutatorResidualTrace p M s := by
  rw [finiteCanonicalLogJetGreenDefectTrace_eq_vertex_of_re_eq_half
      p hp M hs,
    finiteCanonicalLogJetCommutatorResidualTrace_eq_vertex_of_re_eq_half
      p hp M hs]

/-!
## Partes reais dos tracos finitos
-/

/-- O traco residual completo possui parte real zero na linha critica. -/
theorem finiteCanonicalLogJetCommutatorResidualTrace_re_eq_zero_of_re_eq_half
    (p : ℕ) (hp : Nat.Prime p) (M : ℕ)
    {s : ℂ} (hs : s.re = 1 / 2) :
    (finiteCanonicalLogJetCommutatorResidualTrace p M s).re = 0 := by
  rw [finiteCanonicalLogJetCommutatorResidualTrace_eq_vertex_of_re_eq_half
    p hp M hs]
  exact finiteReflectedLogJetVertexFlux_re_eq_zero_of_re_eq_half
    (3 * M) hs

/-- O traco do defeito completo possui parte real zero na linha critica. -/
theorem finiteCanonicalLogJetGreenDefectTrace_re_eq_zero_of_re_eq_half
    (p : ℕ) (hp : Nat.Prime p) (M : ℕ)
    {s : ℂ} (hs : s.re = 1 / 2) :
    (finiteCanonicalLogJetGreenDefectTrace p M s).re = 0 := by
  rw [finiteCanonicalLogJetGreenDefectTrace_eq_vertex_of_re_eq_half
    p hp M hs]
  exact finiteReflectedLogJetVertexFlux_re_eq_zero_of_re_eq_half
    (3 * M) hs

/-!
## Limites dos tracos completos
-/

/-- Os cutoffs de vertices por trios convergem para a serie residual. -/
theorem finiteReflectedLogJetVertexFlux_three_mul_tendsto_series
    {s : ℂ} (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    Tendsto (fun M : ℕ ↦ finiteReflectedLogJetVertexFlux (3 * M) s)
      atTop (nhds (reflectedLogJetVertexFluxSeries s)) := by
  have hthree : Tendsto (fun M : ℕ ↦ 3 * M) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with M hM
    omega
  exact (finiteReflectedLogJetVertexFlux_tendsto_series hs0 hs1).comp hthree

/-- O traco residual converge para `B(s)` na linha critica. -/
theorem finiteCanonicalLogJetCommutatorResidualTrace_tendsto_series_of_re_eq_half
    (p : ℕ) (hp : Nat.Prime p) {s : ℂ} (hs : s.re = 1 / 2) :
    Tendsto (fun M : ℕ ↦
        finiteCanonicalLogJetCommutatorResidualTrace p M s)
      atTop (nhds (reflectedLogJetVertexFluxSeries s)) := by
  have hs0 : 0 ≤ s.re := by rw [hs]; norm_num
  have hs1 : s.re ≤ 1 := by rw [hs]; norm_num
  have hfun :
      (fun M : ℕ ↦ finiteCanonicalLogJetCommutatorResidualTrace p M s) =
        (fun M : ℕ ↦ finiteReflectedLogJetVertexFlux (3 * M) s) := by
    funext M
    exact finiteCanonicalLogJetCommutatorResidualTrace_eq_vertex_of_re_eq_half
      p hp M hs
  rw [hfun]
  exact finiteReflectedLogJetVertexFlux_three_mul_tendsto_series hs0 hs1

/-- O traco do comutador converge trivialmente para zero porque ja e zero
em todo corte da linha critica. -/
theorem finiteCanonicalCpLogJetCommutatorWedgeTrace_tendsto_zero_of_re_eq_half
    (p : ℕ) (hp : Nat.Prime p) {s : ℂ} (hs : s.re = 1 / 2) :
    Tendsto (fun M : ℕ ↦
        finiteCanonicalCpLogJetCommutatorWedgeTrace p M s)
      atTop (nhds 0) := by
  have hfun :
      (fun M : ℕ ↦ finiteCanonicalCpLogJetCommutatorWedgeTrace p M s) =
        (fun _ : ℕ ↦ (0 : ℂ)) := by
    funext M
    exact finiteCanonicalCpLogJetCommutatorWedgeTrace_eq_zero_of_re_eq_half
      p hp M hs
  rw [hfun]
  exact tendsto_const_nhds

/-- O traco do defeito converge para o mesmo `B(s)` na linha critica. -/
theorem finiteCanonicalLogJetGreenDefectTrace_tendsto_series_of_re_eq_half
    (p : ℕ) (hp : Nat.Prime p) {s : ℂ} (hs : s.re = 1 / 2) :
    Tendsto (fun M : ℕ ↦ finiteCanonicalLogJetGreenDefectTrace p M s)
      atTop (nhds (reflectedLogJetVertexFluxSeries s)) := by
  have hs0 : 0 ≤ s.re := by rw [hs]; norm_num
  have hs1 : s.re ≤ 1 := by rw [hs]; norm_num
  have hfun :
      (fun M : ℕ ↦ finiteCanonicalLogJetGreenDefectTrace p M s) =
        (fun M : ℕ ↦ finiteReflectedLogJetVertexFlux (3 * M) s) := by
    funext M
    exact finiteCanonicalLogJetGreenDefectTrace_eq_vertex_of_re_eq_half
      p hp M hs
  rw [hfun]
  exact finiteReflectedLogJetVertexFlux_three_mul_tendsto_series hs0 hs1

/-- Coracao do 0.36: na linha critica, residual e defeito convergem para o
mesmo limite puramente imaginario, enquanto o comutador converge para zero. -/
theorem criticalLine_completeTraces_tendsto
    (p : ℕ) (hp : Nat.Prime p) {s : ℂ} (hs : s.re = 1 / 2) :
    Tendsto (fun M : ℕ ↦
        finiteCanonicalLogJetCommutatorResidualTrace p M s)
        atTop (nhds (reflectedLogJetVertexFluxSeries s)) ∧
      Tendsto (fun M : ℕ ↦
        finiteCanonicalCpLogJetCommutatorWedgeTrace p M s)
        atTop (nhds 0) ∧
      Tendsto (fun M : ℕ ↦
        finiteCanonicalLogJetGreenDefectTrace p M s)
        atTop (nhds (reflectedLogJetVertexFluxSeries s)) ∧
      (reflectedLogJetVertexFluxSeries s).re = 0 := by
  exact ⟨
    finiteCanonicalLogJetCommutatorResidualTrace_tendsto_series_of_re_eq_half
      p hp hs,
    finiteCanonicalCpLogJetCommutatorWedgeTrace_tendsto_zero_of_re_eq_half
      p hp hs,
    finiteCanonicalLogJetGreenDefectTrace_tendsto_series_of_re_eq_half
      p hp hs,
    reflectedLogJetVertexFluxSeries_re_eq_zero_of_re_eq_half hs⟩

/-!
## Ponto central
-/

/-- A soma finita de vertices se anula termo a termo em `s=1/2`. -/
@[simp] theorem finiteReflectedLogJetVertexFlux_one_half_eq_zero (N : ℕ) :
    finiteReflectedLogJetVertexFlux N ((1 / 2 : ℝ) : ℂ) = 0 := by
  unfold finiteReflectedLogJetVertexFlux
  apply Finset.sum_eq_zero
  intro n hn
  exact reflectedLogJetVertexFlux_one_half_eq_zero n

/-- No ponto central, o traco residual inteiro e zero em todo corte. -/
@[simp] theorem finiteCanonicalLogJetCommutatorResidualTrace_one_half_eq_zero
    (p : ℕ) (hp : Nat.Prime p) (M : ℕ) :
    finiteCanonicalLogJetCommutatorResidualTrace p M
        ((1 / 2 : ℝ) : ℂ) = 0 := by
  rw [finiteCanonicalLogJetCommutatorResidualTrace_eq_vertex_of_re_eq_half
    p hp M (by norm_num)]
  exact finiteReflectedLogJetVertexFlux_one_half_eq_zero (3 * M)

/-- No ponto central, o traco do comutador inteiro e zero em todo corte. -/
@[simp] theorem finiteCanonicalCpLogJetCommutatorWedgeTrace_one_half_eq_zero
    (p : ℕ) (hp : Nat.Prime p) (M : ℕ) :
    finiteCanonicalCpLogJetCommutatorWedgeTrace p M
        ((1 / 2 : ℝ) : ℂ) = 0 := by
  exact finiteCanonicalCpLogJetCommutatorWedgeTrace_eq_zero_of_re_eq_half
    p hp M (by norm_num)

/-- No ponto central, o traco do defeito inteiro e zero em todo corte. -/
@[simp] theorem finiteCanonicalLogJetGreenDefectTrace_one_half_eq_zero
    (p : ℕ) (hp : Nat.Prime p) (M : ℕ) :
    finiteCanonicalLogJetGreenDefectTrace p M
        ((1 / 2 : ℝ) : ℂ) = 0 := by
  rw [finiteCanonicalLogJetGreenDefectTrace_eq_vertex_of_re_eq_half
    p hp M (by norm_num)]
  exact finiteReflectedLogJetVertexFlux_one_half_eq_zero (3 * M)

end

end CPFormal.Analytic.Cp
