import CPFormal.Analytic.CpFiniteTfvdLogJetResidualCutoff
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Assintotica do cutoff e do bulk residual log-jet

O checkpoint 0.33 separou exatamente o fluxo residual de vertices em um
cutoff movel e um bulk cruzado. Este arquivo controla os dois termos sem
postular cancelamento.

Primeiro abrimos a corrente cruzada em potencias complexas positivas. No
strip fechado `0 <= Re(s) <= 1`, cada produto cruzado e dominado por
`1/(n+1)`, logo a corrente inteira e dominada por `2/(n+1)`. O salto de
logaritmo fornece mais uma potencia. Consequentemente o fluxo de vertices e
absolutamente somavel, o cutoff movel tende a zero e o bulk cruzado converge
ao mesmo limite da serie de fluxos.
-/

open scoped BigOperators Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-!
## Forma fechada da corrente cruzada
-/

/-- Conjugacao de um valor de Dirichlet em base natural positiva. -/
theorem conj_positiveDirichletValue_eq_cpow
    (s : ℂ) (n : ℕ) :
    (starRingEnd ℂ) (positiveDirichletValue s n) =
      (((n + 1 : ℕ) : ℂ)) ^ (-(starRingEnd ℂ) s) := by
  let x : ℂ := ((n + 1 : ℕ) : ℂ)
  have hargzero : x.arg = 0 := by
    simpa [x] using (Complex.natCast_arg (n := n + 1))
  have harg : x.arg ≠ Real.pi := by
    rw [hargzero]
    exact Real.pi_ne_zero.symm
  have hxconj : (starRingEnd ℂ) x = x := by
    simp [x]
  have h := (Complex.cpow_conj x (-s) harg).symm
  rw [hxconj] at h
  simpa [positiveDirichletValue, x] using h

/--
Forma fechada sem gradientes: duas potencias cruzadas nos vertices positivos
`n+1` e `n+2`, com expoentes refletidos complementares.
-/
theorem reflectedDirichletVertexCrossFlux_eq_cpow_cross
    (n : ℕ) (s : ℂ) :
    reflectedDirichletVertexCrossFlux n s =
      (((n + 1 : ℕ) : ℂ)) ^ (-(starRingEnd ℂ) s) *
          (((n + 2 : ℕ) : ℂ)) ^
            (-(1 - (starRingEnd ℂ) s)) -
        (((n + 2 : ℕ) : ℂ)) ^ (-(starRingEnd ℂ) s) *
          (((n + 1 : ℕ) : ℂ)) ^
            (-(1 - (starRingEnd ℂ) s)) := by
  unfold reflectedDirichletVertexCrossFlux
  rw [conj_positiveDirichletValue_eq_cpow,
    conj_positiveDirichletValue_eq_cpow]
  simp [positiveDirichletValue, reflectedParameter, Nat.add_assoc]

/-!
## Cota uniforme da corrente no strip fechado
-/

/-- Cada um dos dois produtos radiais cruzados e dominado pelo endpoint
interno quando `0 <= sigma <= 1`. -/
theorem reflected_rpow_cross_each_le_inv
    {x y sigma : ℝ}
    (hx : 0 < x) (hxy : x ≤ y)
    (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    y ^ (-sigma) * x ^ (sigma - 1) ≤ x⁻¹ ∧
      x ^ (-sigma) * y ^ (sigma - 1) ≤ x⁻¹ := by
  have hnegSigma : -sigma ≤ 0 := by linarith
  have hsigmaSub : sigma - 1 ≤ 0 := by linarith
  have hpowNeg : y ^ (-sigma) ≤ x ^ (-sigma) :=
    Real.rpow_le_rpow_of_nonpos hx hxy hnegSigma
  have hpowSub : y ^ (sigma - 1) ≤ x ^ (sigma - 1) :=
    Real.rpow_le_rpow_of_nonpos hx hxy hsigmaSub
  have hcombine :
      x ^ (-sigma) * x ^ (sigma - 1) = x⁻¹ := by
    rw [← Real.rpow_add hx, ← Real.rpow_neg_one x]
    congr 1
    ring
  constructor
  · calc
      y ^ (-sigma) * x ^ (sigma - 1) ≤
          x ^ (-sigma) * x ^ (sigma - 1) :=
        mul_le_mul_of_nonneg_right hpowNeg (Real.rpow_nonneg hx.le _)
      _ = x⁻¹ := hcombine
  · calc
      x ^ (-sigma) * y ^ (sigma - 1) ≤
          x ^ (-sigma) * x ^ (sigma - 1) :=
        mul_le_mul_of_nonneg_left hpowSub (Real.rpow_nonneg hx.le _)
      _ = x⁻¹ := hcombine

/-- A corrente cruzada decai ao menos como `2/(n+1)` no strip fechado. -/
theorem norm_reflectedDirichletVertexCrossFlux_le_two_mul_inv
    {s : ℂ} (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) (n : ℕ) :
    ‖reflectedDirichletVertexCrossFlux n s‖ ≤
      2 * (((n + 1 : ℕ) : ℝ))⁻¹ := by
  have hxy :
      (((n + 1 : ℕ) : ℝ)) ≤ (((n + 2 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.le_succ (n + 1)
  have hbounds := reflected_rpow_cross_each_le_inv
    (show 0 < (((n + 1 : ℕ) : ℝ)) by positivity)
    hxy hs0 hs1
  unfold reflectedDirichletVertexCrossFlux
  calc
    ‖(starRingEnd ℂ) (positiveDirichletValue s n) *
          positiveDirichletValue (reflectedParameter s) (n + 1) -
        (starRingEnd ℂ) (positiveDirichletValue s (n + 1)) *
          positiveDirichletValue (reflectedParameter s) n‖ ≤
      ‖(starRingEnd ℂ) (positiveDirichletValue s n) *
          positiveDirichletValue (reflectedParameter s) (n + 1)‖ +
        ‖(starRingEnd ℂ) (positiveDirichletValue s (n + 1)) *
          positiveDirichletValue (reflectedParameter s) n‖ :=
      norm_sub_le _ _
    _ = (((n + 1 : ℕ) : ℝ)) ^ (-s.re) *
          (((n + 2 : ℕ) : ℝ)) ^ (s.re - 1) +
        (((n + 2 : ℕ) : ℝ)) ^ (-s.re) *
          (((n + 1 : ℕ) : ℝ)) ^ (s.re - 1) := by
      rw [norm_reflectedGradientCross_backward,
        norm_reflectedGradientCross_forward]
    _ ≤ (((n + 1 : ℕ) : ℝ))⁻¹ +
        (((n + 1 : ℕ) : ℝ))⁻¹ :=
      add_le_add hbounds.2 hbounds.1
    _ = 2 * (((n + 1 : ℕ) : ℝ))⁻¹ := by ring

/-!
## Salto logaritmico e somabilidade absoluta
-/

/-- O salto `log(n+2)-log(n+1)` e positivo e no maximo `1/(n+1)`. -/
theorem norm_positiveLogGap_le_inv (n : ℕ) :
    ‖positiveLogGap n‖ ≤ (((n + 1 : ℕ) : ℝ))⁻¹ := by
  let x : ℝ := ((n + 1 : ℕ) : ℝ)
  let y : ℝ := ((n + 2 : ℕ) : ℝ)
  have hx : 0 < x := by positivity
  have hy : 0 < y := by positivity
  have hxy : x ≤ y := by
    dsimp [x, y]
    exact_mod_cast Nat.le_succ (n + 1)
  have hratioOne : 1 ≤ y / x :=
    (le_div_iff₀ hx).2 (by simpa using hxy)
  have hlogNonneg : 0 ≤ Real.log (y / x) :=
    Real.log_nonneg hratioOne
  have hlogUpper : Real.log (y / x) ≤ y / x - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hy hx)
  have hdiff : y / x - 1 = x⁻¹ := by
    dsimp [x, y]
    field_simp
    push_cast
    ring
  have hlogDiv : Real.log y - Real.log x = Real.log (y / x) := by
    rw [Real.log_div hy.ne' hx.ne']
  have hgap :
      positiveLogGap n = ((Real.log (y / x) : ℝ) : ℂ) := by
    apply Complex.ext
    · simpa [positiveLogGap, x, y] using hlogDiv
    · simp [positiveLogGap]
  rw [hgap, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hlogNonneg]
  exact hlogUpper.trans_eq hdiff

/-- Cada fluxo log-jet de vertices e dominado por uma p-serie quadratica. -/
theorem norm_reflectedLogJetVertexFlux_le_two_mul_rpow_neg_two
    {s : ℂ} (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) (n : ℕ) :
    ‖reflectedLogJetVertexFlux n s‖ ≤
      2 * (((n + 1 : ℕ) : ℝ)) ^ (-2 : ℝ) := by
  rw [reflectedLogJetVertexFlux_eq_gap_mul_crossFlux, norm_mul]
  have hgap := norm_positiveLogGap_le_inv n
  have hcross :=
    norm_reflectedDirichletVertexCrossFlux_le_two_mul_inv hs0 hs1 n
  have hx : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  calc
    ‖positiveLogGap n‖ * ‖reflectedDirichletVertexCrossFlux n s‖ ≤
        (((n + 1 : ℕ) : ℝ))⁻¹ *
          ‖reflectedDirichletVertexCrossFlux n s‖ :=
      mul_le_mul_of_nonneg_right hgap (norm_nonneg _)
    _ ≤ (((n + 1 : ℕ) : ℝ))⁻¹ *
          (2 * (((n + 1 : ℕ) : ℝ))⁻¹) :=
      mul_le_mul_of_nonneg_left hcross (inv_nonneg.mpr hx.le)
    _ = 2 *
          ((((n + 1 : ℕ) : ℝ))⁻¹ *
            (((n + 1 : ℕ) : ℝ))⁻¹) := by ring
    _ = 2 * (((n + 1 : ℕ) : ℝ)) ^ ((-1 : ℝ) + (-1 : ℝ)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hx]
    _ = 2 * (((n + 1 : ℕ) : ℝ)) ^ (-2 : ℝ) := by norm_num

/-- A serie real majorante quadratica, ja com o fator `2`, e somavel. -/
theorem summable_two_mul_nat_add_one_rpow_neg_two :
    Summable (fun n : ℕ ↦
      2 * (((n + 1 : ℕ) : ℝ)) ^ (-2 : ℝ)) := by
  have hpower :
      Summable (fun n : ℕ ↦
        (((n + 1 : ℕ) : ℝ)) ^ (-2 : ℝ)) := by
    simpa using
      (summable_nat_add_one_rpow_neg_re_sub_two
        (s := (0 : ℂ)) (by norm_num))
  exact hpower.mul_left 2

/-- As normas do fluxo residual formam uma serie somavel no strip fechado. -/
theorem summable_norm_reflectedLogJetVertexFlux
    {s : ℂ} (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    Summable (fun n : ℕ ↦ ‖reflectedLogJetVertexFlux n s‖) := by
  exact summable_two_mul_nat_add_one_rpow_neg_two.of_norm_bounded
    (fun n ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact norm_reflectedLogJetVertexFlux_le_two_mul_rpow_neg_two
        hs0 hs1 n)

/-- A serie complexa do fluxo residual converge absolutamente. -/
theorem summable_reflectedLogJetVertexFlux
    {s : ℂ} (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    Summable (fun n : ℕ ↦ reflectedLogJetVertexFlux n s) :=
  (summable_norm_reflectedLogJetVertexFlux hs0 hs1).of_norm

/-- Limite canonico do canal residual de vertices. -/
def reflectedLogJetVertexFluxSeries (s : ℂ) : ℂ :=
  ∑' n : ℕ, reflectedLogJetVertexFlux n s

/-- Os cutoffs finitos do fluxo de vertices convergem para sua serie. -/
theorem finiteReflectedLogJetVertexFlux_tendsto_series
    {s : ℂ} (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    Tendsto (fun N : ℕ ↦ finiteReflectedLogJetVertexFlux N s)
      atTop (nhds (reflectedLogJetVertexFluxSeries s)) := by
  simpa [finiteReflectedLogJetVertexFlux,
    reflectedLogJetVertexFluxSeries] using
      (summable_reflectedLogJetVertexFlux hs0 hs1).tendsto_sum_tsum_nat

/-!
## Desaparecimento do cutoff movel
-/

/-- Cota explicita do cutoff deslocado, com o mesmo denominador do log. -/
theorem norm_reflectedLogJetMovingCutoff_succ_le
    {s : ℂ} (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) (N : ℕ) :
    ‖reflectedLogJetMovingCutoff (N + 1) s‖ ≤
      4 * Real.log (((N + 2 : ℕ) : ℝ)) /
        (((N + 2 : ℕ) : ℝ)) := by
  have hone : (1 : ℝ) ≤ (((N + 2 : ℕ) : ℝ)) := by
    exact_mod_cast (show 1 ≤ N + 2 by omega)
  have hlog : 0 ≤ Real.log (((N + 2 : ℕ) : ℝ)) :=
    Real.log_nonneg hone
  have hcross :=
    norm_reflectedDirichletVertexCrossFlux_le_two_mul_inv hs0 hs1 N
  have hratio :
      2 * (((N + 1 : ℕ) : ℝ))⁻¹ ≤
        4 * (((N + 2 : ℕ) : ℝ))⁻¹ := by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    norm_num
    nlinarith [show (0 : ℝ) ≤ (N : ℝ) by positivity]
  have hweight :
      ‖positiveLogVertexWeight (N + 1)‖ =
        Real.log (((N + 2 : ℕ) : ℝ)) := by
    unfold positiveLogVertexWeight
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  unfold reflectedLogJetMovingCutoff
  simp only [Nat.add_sub_cancel]
  rw [norm_mul, hweight]
  calc
    Real.log (((N + 2 : ℕ) : ℝ)) *
        ‖reflectedDirichletVertexCrossFlux N s‖ ≤
      Real.log (((N + 2 : ℕ) : ℝ)) *
        (2 * (((N + 1 : ℕ) : ℝ))⁻¹) :=
      mul_le_mul_of_nonneg_left hcross hlog
    _ ≤ Real.log (((N + 2 : ℕ) : ℝ)) *
        (4 * (((N + 2 : ℕ) : ℝ))⁻¹) :=
      mul_le_mul_of_nonneg_left hratio hlog
    _ = 4 * Real.log (((N + 2 : ℕ) : ℝ)) /
        (((N + 2 : ℕ) : ℝ)) := by
      rw [div_eq_mul_inv]
      ring

/-- O cutoff movel desaparece em todo o strip fechado. -/
theorem reflectedLogJetMovingCutoff_tendsto_zero
    {s : ℂ} (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    Tendsto (fun N : ℕ ↦ reflectedLogJetMovingCutoff N s)
      atTop (nhds 0) := by
  have hnat : Tendsto (fun N : ℕ ↦ N + 2) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with N hN
    omega
  have hreal :
      Tendsto (fun N : ℕ ↦ (((N + 2 : ℕ) : ℝ))) atTop atTop :=
    (tendsto_natCast_atTop_atTop :
      Tendsto ((↑) : ℕ → ℝ) atTop atTop).comp hnat
  have hratio :
      Tendsto
        (fun N : ℕ ↦
          Real.log (((N + 2 : ℕ) : ℝ)) /
            (((N + 2 : ℕ) : ℝ)) ^ (1 : ℝ))
        atTop (nhds 0) :=
    ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero).comp
      hreal
  have hmajorant :
      Tendsto
        (fun N : ℕ ↦
          4 * Real.log (((N + 2 : ℕ) : ℝ)) /
            (((N + 2 : ℕ) : ℝ)))
        atTop (nhds 0) := by
    have hfour :
        Tendsto (fun _ : ℕ ↦ (4 : ℝ)) atTop (nhds 4) :=
      tendsto_const_nhds
    have hmul := hfour.mul hratio
    simpa [Real.rpow_one] using hmul
  have hshift :
      Tendsto
        (fun N : ℕ ↦ reflectedLogJetMovingCutoff (N + 1) s)
        atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero
      (fun N ↦ norm_nonneg _)
      (fun N ↦ norm_reflectedLogJetMovingCutoff_succ_le hs0 hs1 N)
      hmajorant
  exact (tendsto_add_atTop_iff_nat 1).1 hshift

/-!
## Limite do bulk cruzado
-/

/-- O bulk converge para a mesma serie: o unico termo que os separava era o
cutoff movel, agora provado nulo no limite. -/
theorem finiteReflectedLogJetCrossBulk_tendsto_series
    {s : ℂ} (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    Tendsto (fun N : ℕ ↦ finiteReflectedLogJetCrossBulk N s)
      atTop (nhds (reflectedLogJetVertexFluxSeries s)) := by
  have hvertex := finiteReflectedLogJetVertexFlux_tendsto_series hs0 hs1
  have hcutoff := reflectedLogJetMovingCutoff_tendsto_zero hs0 hs1
  have hfun :
      (fun N : ℕ ↦ finiteReflectedLogJetCrossBulk N s) =
        (fun N : ℕ ↦ finiteReflectedLogJetVertexFlux N s -
          reflectedLogJetMovingCutoff N s) := by
    funext N
    rw [finiteReflectedLogJetVertexFlux_eq_cutoff_add_crossBulk]
    ring
  rw [hfun]
  simpa using hvertex.sub hcutoff

/-- A mesma convergencia nos cutoffs TFVD completos `N=3M`. -/
theorem finiteReflectedLogJetCrossBulk_three_mul_tendsto_series
    {s : ℂ} (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    Tendsto (fun M : ℕ ↦ finiteReflectedLogJetCrossBulk (3 * M) s)
      atTop (nhds (reflectedLogJetVertexFluxSeries s)) := by
  have hthree : Tendsto (fun M : ℕ ↦ 3 * M) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with M hM
    omega
  exact (finiteReflectedLogJetCrossBulk_tendsto_series hs0 hs1).comp hthree

end

end CPFormal.Analytic.Cp
