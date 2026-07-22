import CPFormal.Analytic.CpFiniteTfvdLogJetResidualAsymptotics

/-!
# Simetria refletida do limite residual log-jet

O checkpoint 0.34 construiu a serie absolutamente convergente do fluxo
residual no strip fechado e identificou nela o limite do bulk cruzado. Este
arquivo determina sua geometria sob a involucao espectral

`s# = 1 - conj(s)`.

A corrente cruzada troca de sinal e e conjugada quando `s` e substituido por
`s#`. O mesmo vale para o fluxo de cada aresta, para todos os cutoffs finitos,
para o bulk cruzado e para a serie. Na linha critica, onde `s# = s`, o limite
e portanto puramente imaginario. No ponto central real `s = 1/2`, os dois
produtos cruzados coincidem e o residual inteiro se anula.

Nenhuma dessas identidades transforma anti-Hermiticidade em anulacao fora do
ponto central: a unidade imaginaria fornece um witness abstrato nao nulo com
a mesma simetria.
-/

open scoped BigOperators Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-!
## Involucao espectral e corrente local
-/

/-- A reflexao espectral `s# = 1-conj(s)` e uma involucao literal. -/
@[simp] theorem reflectedParameter_reflectedParameter (s : ℂ) :
    reflectedParameter (reflectedParameter s) = s := by
  simp [reflectedParameter]

/-- Na linha critica, a reflexao fixa o parametro. -/
theorem reflectedParameter_eq_self_of_re_eq_half
    {s : ℂ} (hs : s.re = 1 / 2) :
    reflectedParameter s = s := by
  apply Complex.ext
  · norm_num [reflectedParameter, hs]
  · simp [reflectedParameter]

/-- O salto de logaritmo e real e, portanto, fixo por conjugacao. -/
@[simp] theorem conj_positiveLogGap (n : ℕ) :
    (starRingEnd ℂ) (positiveLogGap n) = positiveLogGap n := by
  simp [positiveLogGap]

/-- A corrente cruzada e anti-Hermitiana sob a reflexao espectral. -/
theorem reflectedDirichletVertexCrossFlux_reflectedParameter
    (n : ℕ) (s : ℂ) :
    reflectedDirichletVertexCrossFlux n (reflectedParameter s) =
      -(starRingEnd ℂ) (reflectedDirichletVertexCrossFlux n s) := by
  unfold reflectedDirichletVertexCrossFlux
  rw [reflectedParameter_reflectedParameter]
  simp only [map_sub, map_mul]
  simp
  ring

/-- O fluxo log-jet de cada aresta herda a mesma anti-Hermiticidade. -/
theorem reflectedLogJetVertexFlux_reflectedParameter
    (n : ℕ) (s : ℂ) :
    reflectedLogJetVertexFlux n (reflectedParameter s) =
      -(starRingEnd ℂ) (reflectedLogJetVertexFlux n s) := by
  rw [reflectedLogJetVertexFlux_eq_gap_mul_crossFlux,
    reflectedLogJetVertexFlux_eq_gap_mul_crossFlux,
    reflectedDirichletVertexCrossFlux_reflectedParameter]
  simp only [map_mul, conj_positiveLogGap]
  ring

/-!
## Simetria em todo corte finito
-/

/-- A soma finita dos fluxos de vertices e anti-Hermitiana. -/
theorem finiteReflectedLogJetVertexFlux_reflectedParameter
    (N : ℕ) (s : ℂ) :
    finiteReflectedLogJetVertexFlux N (reflectedParameter s) =
      -(starRingEnd ℂ) (finiteReflectedLogJetVertexFlux N s) := by
  unfold finiteReflectedLogJetVertexFlux
  simp_rw [reflectedLogJetVertexFlux_reflectedParameter]
  rw [Finset.sum_neg_distrib, map_sum]

/-- O peso do cutoff movel tambem e real. -/
@[simp] theorem conj_positiveLogVertexWeight (N : ℕ) :
    (starRingEnd ℂ) (positiveLogVertexWeight N) =
      positiveLogVertexWeight N := by
  simp [positiveLogVertexWeight]

/-- O cutoff movel preserva a anti-Hermiticidade exata. -/
theorem reflectedLogJetMovingCutoff_reflectedParameter
    (N : ℕ) (s : ℂ) :
    reflectedLogJetMovingCutoff N (reflectedParameter s) =
      -(starRingEnd ℂ) (reflectedLogJetMovingCutoff N s) := by
  unfold reflectedLogJetMovingCutoff
  rw [reflectedDirichletVertexCrossFlux_reflectedParameter]
  simp only [map_mul, conj_positiveLogVertexWeight]
  ring

/-- O bulk cruzado finito e anti-Hermitiano em cada cutoff. -/
theorem finiteReflectedLogJetCrossBulk_reflectedParameter
    (N : ℕ) (s : ℂ) :
    finiteReflectedLogJetCrossBulk N (reflectedParameter s) =
      -(starRingEnd ℂ) (finiteReflectedLogJetCrossBulk N s) := by
  calc
    finiteReflectedLogJetCrossBulk N (reflectedParameter s) =
        finiteReflectedLogJetVertexFlux N (reflectedParameter s) -
          reflectedLogJetMovingCutoff N (reflectedParameter s) := by
      rw [finiteReflectedLogJetVertexFlux_eq_cutoff_add_crossBulk]
      ring
    _ = -(starRingEnd ℂ) (finiteReflectedLogJetVertexFlux N s) -
          (-(starRingEnd ℂ) (reflectedLogJetMovingCutoff N s)) := by
      rw [finiteReflectedLogJetVertexFlux_reflectedParameter,
        reflectedLogJetMovingCutoff_reflectedParameter]
    _ = -(starRingEnd ℂ) (finiteReflectedLogJetCrossBulk N s) := by
      rw [show finiteReflectedLogJetCrossBulk N s =
          finiteReflectedLogJetVertexFlux N s -
            reflectedLogJetMovingCutoff N s by
        rw [finiteReflectedLogJetVertexFlux_eq_cutoff_add_crossBulk]
        ring]
      simp only [map_sub]
      ring

/-!
## Passagem exata a serie e estrutura da linha critica
-/

/-- A serie residual satisfaz `B(s#) = -conj(B(s))`.

A identidade do `tsum` e algebrica e nao precisa de hipotese de strip. As
hipoteses do strip sao necessarias apenas quando queremos identificar esse
`tsum` com o limite dos cutoffs do bulk. -/
theorem reflectedLogJetVertexFluxSeries_reflectedParameter (s : ℂ) :
    reflectedLogJetVertexFluxSeries (reflectedParameter s) =
      -(starRingEnd ℂ) (reflectedLogJetVertexFluxSeries s) := by
  unfold reflectedLogJetVertexFluxSeries
  calc
    (∑' n : ℕ, reflectedLogJetVertexFlux n (reflectedParameter s)) =
        ∑' n : ℕ, -(starRingEnd ℂ) (reflectedLogJetVertexFlux n s) := by
      congr 1
      funext n
      exact reflectedLogJetVertexFlux_reflectedParameter n s
    _ = -(∑' n : ℕ, (starRingEnd ℂ) (reflectedLogJetVertexFlux n s)) := by
      rw [tsum_neg]
    _ = -(starRingEnd ℂ)
          (∑' n : ℕ, reflectedLogJetVertexFlux n s) := by
      rw [Complex.conj_tsum]

/-- Uma quantidade anti-Hermitiana possui parte real nula. -/
theorem re_eq_zero_of_eq_neg_conj
    {z : ℂ} (hz : z = -(starRingEnd ℂ) z) :
    z.re = 0 := by
  have hreal := congrArg Complex.re hz
  simp only [Complex.neg_re, Complex.conj_re] at hreal
  linarith

/-- Cada cutoff do bulk e puramente imaginario na linha critica. -/
theorem finiteReflectedLogJetCrossBulk_re_eq_zero_of_re_eq_half
    (N : ℕ) {s : ℂ} (hs : s.re = 1 / 2) :
    (finiteReflectedLogJetCrossBulk N s).re = 0 := by
  have hanti := finiteReflectedLogJetCrossBulk_reflectedParameter N s
  rw [reflectedParameter_eq_self_of_re_eq_half hs] at hanti
  exact re_eq_zero_of_eq_neg_conj hanti

/-- O limite residual e puramente imaginario na linha critica. -/
theorem reflectedLogJetVertexFluxSeries_re_eq_zero_of_re_eq_half
    {s : ℂ} (hs : s.re = 1 / 2) :
    (reflectedLogJetVertexFluxSeries s).re = 0 := by
  have hanti := reflectedLogJetVertexFluxSeries_reflectedParameter s
  rw [reflectedParameter_eq_self_of_re_eq_half hs] at hanti
  exact re_eq_zero_of_eq_neg_conj hanti

/-- Nos cutoffs TFVD completos da linha critica, o bulk converge para um
limite cuja parte real e zero. -/
theorem finiteReflectedLogJetCrossBulk_three_mul_tendsto_criticalLine
    {s : ℂ} (hs : s.re = 1 / 2) :
    Tendsto (fun M : ℕ ↦ finiteReflectedLogJetCrossBulk (3 * M) s)
        atTop (nhds (reflectedLogJetVertexFluxSeries s)) ∧
      (reflectedLogJetVertexFluxSeries s).re = 0 := by
  have hs0 : 0 ≤ s.re := by rw [hs]; norm_num
  have hs1 : s.re ≤ 1 := by rw [hs]; norm_num
  exact ⟨finiteReflectedLogJetCrossBulk_three_mul_tendsto_series hs0 hs1,
    reflectedLogJetVertexFluxSeries_re_eq_zero_of_re_eq_half hs⟩

/-!
## Ponto central e limite da conclusao
-/

/-- No ponto central real, os dois produtos cruzados coincidem. -/
@[simp] theorem reflectedDirichletVertexCrossFlux_one_half_eq_zero
    (n : ℕ) :
    reflectedDirichletVertexCrossFlux n ((1 / 2 : ℝ) : ℂ) = 0 := by
  rw [reflectedDirichletVertexCrossFlux_eq_cpow_cross]
  simp only [Complex.conj_ofReal]
  norm_num
  ring

/-- Cada aresta residual se anula no ponto central. -/
@[simp] theorem reflectedLogJetVertexFlux_one_half_eq_zero (n : ℕ) :
    reflectedLogJetVertexFlux n ((1 / 2 : ℝ) : ℂ) = 0 := by
  rw [reflectedLogJetVertexFlux_eq_gap_mul_crossFlux,
    reflectedDirichletVertexCrossFlux_one_half_eq_zero]
  simp

/-- O bulk finito inteiro se anula no ponto central. -/
@[simp] theorem finiteReflectedLogJetCrossBulk_one_half_eq_zero (N : ℕ) :
    finiteReflectedLogJetCrossBulk N ((1 / 2 : ℝ) : ℂ) = 0 := by
  unfold finiteReflectedLogJetCrossBulk
  apply Finset.sum_eq_zero
  intro n hn
  rw [reflectedDirichletVertexCrossFlux_one_half_eq_zero,
    reflectedDirichletVertexCrossFlux_one_half_eq_zero]
  ring

/-- O limite residual se anula exatamente no ponto central real. -/
@[simp] theorem reflectedLogJetVertexFluxSeries_one_half_eq_zero :
    reflectedLogJetVertexFluxSeries ((1 / 2 : ℝ) : ℂ) = 0 := by
  unfold reflectedLogJetVertexFluxSeries
  simp_rw [reflectedLogJetVertexFlux_one_half_eq_zero]
  exact tsum_zero

/-- Anti-Hermiticidade isolada nao implica anulacao: `I` e um witness nao
nulo que satisfaz a mesma equacao. -/
theorem nonzero_antiHermitian_witness :
    Complex.I = -(starRingEnd ℂ) Complex.I ∧ Complex.I ≠ 0 := by
  constructor <;> norm_num

end

end CPFormal.Analytic.Cp
