import CPFormal.Analytic.CpFiniteTfvdLogJetCriticalLineTraces

/-!
# Leque triangular de fases na linha critica

O checkpoint 0.36 reduziu os tracos residual e de defeito, na linha
critica, a mesma serie absolutamente convergente `B(s)`. Este arquivo abre
a parte imaginaria que ainda podia sobreviver.

Para `s(t)=1/2+it`, o vertice positivo `n+1` e visto como um ponto complexo
`u_n(t)`. Os pontos `0,u_n(t),u_{n+1}(t)` formam uma face orientada. Sua area
e metade da parte imaginaria de `conj(u_n)u_{n+1}`. O cross-flux e exatamente
quatro vezes essa area na direcao `I`.

A mesma identidade e aberta em coordenadas reais: cada termo e um peso
positivo multiplicado por `-sin(t * (log(n+2)-log(n+1)))`. Isso produz uma
serie real de senos para `B(1/2+it)` e prova, sem qualquer entrada Genuine,
que ela e estritamente negativa na parte imaginaria quando `0<t<=1`.
-/

open scoped BigOperators Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-!
## Parametro critico e vertices do leque
-/

/-- Parametrizacao real da linha critica. -/
def criticalLineParameter (t : ℝ) : ℂ :=
  ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I

@[simp] theorem criticalLineParameter_re (t : ℝ) :
    (criticalLineParameter t).re = 1 / 2 := by
  simp [criticalLineParameter]

@[simp] theorem criticalLineParameter_im (t : ℝ) :
    (criticalLineParameter t).im = t := by
  simp [criticalLineParameter]

/-- Vertice de fase associado ao inteiro positivo `n+1`. -/
def criticalPhaseVertex (n : ℕ) (t : ℝ) : ℂ :=
  positiveDirichletValue (criticalLineParameter t) n

/-- Area orientada da face `[0,u_n(t),u_{n+1}(t)]`. -/
def criticalPhaseTriangleArea (n : ℕ) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ((starRingEnd ℂ) (criticalPhaseVertex n t) *
      criticalPhaseVertex (n + 1) t).im

/-- O cross-flux critico e quatro vezes a area orientada, na direcao `I`. -/
theorem reflectedDirichletVertexCrossFlux_criticalLine_eq_four_area_mul_I
    (n : ℕ) (t : ℝ) :
    reflectedDirichletVertexCrossFlux n (criticalLineParameter t) =
      ((4 * criticalPhaseTriangleArea n t : ℝ) : ℂ) * Complex.I := by
  unfold reflectedDirichletVertexCrossFlux criticalPhaseTriangleArea
    criticalPhaseVertex
  rw [reflectedParameter_eq_self_of_re_eq_half
    (criticalLineParameter_re t)]
  apply Complex.ext <;> simp <;> ring

/-!
## Coordenadas reais: gap, amplitude e seno
-/

/-- Salto real de logaritmo entre os dois vertices da face. -/
def positiveRealLogGap (n : ℕ) : ℝ :=
  Real.log (((n + 2 : ℕ) : ℝ)) -
    Real.log (((n + 1 : ℕ) : ℝ))

/-- O salto complexo anterior e a inclusao do salto real. -/
theorem positiveLogGap_eq_ofReal_positiveRealLogGap (n : ℕ) :
    positiveLogGap n = (positiveRealLogGap n : ℂ) := by
  apply Complex.ext <;> simp [positiveLogGap, positiveRealLogGap]

/-- Todo salto logaritmico consecutivo e estritamente positivo. -/
theorem positiveRealLogGap_pos (n : ℕ) :
    0 < positiveRealLogGap n := by
  let x : ℝ := ((n + 1 : ℕ) : ℝ)
  let y : ℝ := ((n + 2 : ℕ) : ℝ)
  have hx : 0 < x := by positivity
  have hy : 0 < y := by positivity
  have hxy : x < y := by
    dsimp [x, y]
    exact_mod_cast Nat.lt_succ_self (n + 1)
  have hratio : 1 < y / x :=
    (lt_div_iff₀ hx).2 (by simpa using hxy)
  have hlogEq : Real.log y - Real.log x = Real.log (y / x) := by
    rw [Real.log_div hy.ne' hx.ne']
  change 0 < Real.log y - Real.log x
  rw [hlogEq]
  exact Real.log_pos hratio

/-- A cota do 0.34, agora na coordenada real do salto. -/
theorem positiveRealLogGap_le_inv (n : ℕ) :
    positiveRealLogGap n ≤ (((n + 1 : ℕ) : ℝ))⁻¹ := by
  have h := norm_positiveLogGap_le_inv n
  rw [positiveLogGap_eq_ofReal_positiveRealLogGap,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (positiveRealLogGap_pos n)] at h
  exact h

/-- Em particular, todo salto consecutivo e no maximo `1`. -/
theorem positiveRealLogGap_le_one (n : ℕ) :
    positiveRealLogGap n ≤ 1 := by
  have hgap := positiveRealLogGap_le_inv n
  have hone : (1 : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hinv : (((n + 1 : ℕ) : ℝ))⁻¹ ≤ 1 := by
    rw [inv_le_one₀]
    · exact hone
    · positivity
  exact hgap.trans hinv

/-- Modulo radial comum aos dois transportes orientados da face. -/
def criticalPhaseAmplitude (n : ℕ) : ℝ :=
  Real.exp
    (-((Real.log (((n + 1 : ℕ) : ℝ)) +
      Real.log (((n + 2 : ℕ) : ℝ))) / 2))

theorem criticalPhaseAmplitude_pos (n : ℕ) :
    0 < criticalPhaseAmplitude n := by
  exact Real.exp_pos _

/-- Coeficiente real do fluxo log-jet critico. -/
def criticalPhaseSineFlux (n : ℕ) (t : ℝ) : ℝ :=
  -2 * positiveRealLogGap n * criticalPhaseAmplitude n *
    Real.sin (t * positiveRealLogGap n)

/-!
O lema auxiliar abaixo e apenas a expansao de duas potencias complexas de
bases reais positivas. Ele mantem a escolha de ramo completamente explicita.
-/
theorem positiveReal_criticalCpowCross_eq_sine
    (x y t : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (x : ℂ) ^ (-(starRingEnd ℂ) (criticalLineParameter t)) *
          (y : ℂ) ^ (-(criticalLineParameter t)) -
        (y : ℂ) ^ (-(starRingEnd ℂ) (criticalLineParameter t)) *
          (x : ℂ) ^ (-(criticalLineParameter t)) =
      ((-2 * Real.exp (-((Real.log x + Real.log y) / 2)) *
          Real.sin (t * (Real.log y - Real.log x)) : ℝ) : ℂ) *
        Complex.I := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  simp_rw [Complex.cpow_def_of_ne_zero hxC,
    Complex.cpow_def_of_ne_zero hyC]
  rw [← Complex.exp_add, ← Complex.exp_add]
  rw [← Complex.ofReal_log hx.le, ← Complex.ofReal_log hy.le]
  let z₁ : ℂ :=
    (Real.log x : ℂ) * (-(starRingEnd ℂ) (criticalLineParameter t)) +
      (Real.log y : ℂ) * (-(criticalLineParameter t))
  let z₂ : ℂ :=
    (Real.log y : ℂ) * (-(starRingEnd ℂ) (criticalLineParameter t)) +
      (Real.log x : ℂ) * (-(criticalLineParameter t))
  change Complex.exp z₁ - Complex.exp z₂ = _
  have hz₁re : z₁.re = -((Real.log x + Real.log y) / 2) := by
    simp [z₁, criticalLineParameter]
    ring
  have hz₁im : z₁.im = -(t * (Real.log y - Real.log x)) := by
    simp [z₁, criticalLineParameter]
    ring
  have hz₂re : z₂.re = -((Real.log x + Real.log y) / 2) := by
    simp [z₂, criticalLineParameter]
    ring
  have hz₂im : z₂.im = t * (Real.log y - Real.log x) := by
    simp [z₂, criticalLineParameter]
    ring
  apply Complex.ext
  · simp [Complex.exp_re, hz₁re, hz₁im, hz₂re, hz₂im,
      Real.cos_neg] <;> ring
  · simp [Complex.exp_im, hz₁re, hz₁im, hz₂re, hz₂im,
      Real.sin_neg] <;> ring

/-- Forma local exata do cross-flux como seno real orientado. -/
theorem reflectedDirichletVertexCrossFlux_criticalLine_eq_sine
    (n : ℕ) (t : ℝ) :
    reflectedDirichletVertexCrossFlux n (criticalLineParameter t) =
      ((-2 * criticalPhaseAmplitude n *
          Real.sin (t * positiveRealLogGap n) : ℝ) : ℂ) * Complex.I := by
  rw [reflectedDirichletVertexCrossFlux_eq_cpow_cross]
  rw [show 1 - (starRingEnd ℂ) (criticalLineParameter t) =
      criticalLineParameter t by
    exact reflectedParameter_eq_self_of_re_eq_half
      (criticalLineParameter_re t)]
  simpa [criticalPhaseAmplitude, positiveRealLogGap, Nat.add_assoc] using
    positiveReal_criticalCpowCross_eq_sine
      (((n + 1 : ℕ) : ℝ)) (((n + 2 : ℕ) : ℝ)) t
      (by positivity) (by positivity)

/-- A area orientada de cada face possui a formula senoidal esperada. -/
theorem criticalPhaseTriangleArea_eq_sine
    (n : ℕ) (t : ℝ) :
    criticalPhaseTriangleArea n t =
      -(1 / 2 : ℝ) * criticalPhaseAmplitude n *
        Real.sin (t * positiveRealLogGap n) := by
  have harea :=
    reflectedDirichletVertexCrossFlux_criticalLine_eq_four_area_mul_I n t
  rw [reflectedDirichletVertexCrossFlux_criticalLine_eq_sine] at harea
  have him := congrArg Complex.im harea
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im,
    Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero] at him
  linarith

/-- O fluxo log-jet de uma face critica e um numero real vezes `I`. -/
theorem reflectedLogJetVertexFlux_criticalLine_eq_sine
    (n : ℕ) (t : ℝ) :
    reflectedLogJetVertexFlux n (criticalLineParameter t) =
      (criticalPhaseSineFlux n t : ℂ) * Complex.I := by
  rw [reflectedLogJetVertexFlux_eq_gap_mul_crossFlux,
    positiveLogGap_eq_ofReal_positiveRealLogGap,
    reflectedDirichletVertexCrossFlux_criticalLine_eq_sine]
  unfold criticalPhaseSineFlux
  push_cast
  ring

/-!
## Serie real de senos e simetria em `t`
-/

/-- Os coeficientes reais do perfil senoidal formam uma serie somavel. -/
theorem summable_criticalPhaseSineFlux (t : ℝ) :
    Summable (fun n : ℕ ↦ criticalPhaseSineFlux n t) := by
  have hsum : Summable (fun n : ℕ ↦
      reflectedLogJetVertexFlux n (criticalLineParameter t)) :=
    summable_reflectedLogJetVertexFlux
      (s := criticalLineParameter t) (by norm_num) (by norm_num)
  have him := (Complex.hasSum_im hsum.hasSum).summable
  simpa only [reflectedLogJetVertexFlux_criticalLine_eq_sine,
    Complex.mul_im, Complex.ofReal_re, Complex.I_im,
    Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero] using him

/-- Coracao espectral do 0.37: `B(1/2+it)` e literalmente uma serie real de
senos colocada no eixo imaginario. -/
theorem reflectedLogJetVertexFluxSeries_criticalLine_eq_sineSeries
    (t : ℝ) :
    reflectedLogJetVertexFluxSeries (criticalLineParameter t) =
      ((∑' n : ℕ, criticalPhaseSineFlux n t : ℝ) : ℂ) * Complex.I := by
  have hsum : Summable (fun n : ℕ ↦
      reflectedLogJetVertexFlux n (criticalLineParameter t)) :=
    summable_reflectedLogJetVertexFlux
      (s := criticalLineParameter t) (by norm_num) (by norm_num)
  unfold reflectedLogJetVertexFluxSeries
  apply Complex.ext
  · rw [Complex.re_tsum hsum]
    simp [reflectedLogJetVertexFlux_criticalLine_eq_sine]
  · rw [Complex.im_tsum hsum]
    simp [reflectedLogJetVertexFlux_criticalLine_eq_sine]

@[simp] theorem criticalPhaseSineFlux_neg (n : ℕ) (t : ℝ) :
    criticalPhaseSineFlux n (-t) = -criticalPhaseSineFlux n t := by
  simp [criticalPhaseSineFlux]

/-- O perfil critico e impar no parametro vertical. -/
theorem reflectedLogJetVertexFluxSeries_criticalLine_neg
    (t : ℝ) :
    reflectedLogJetVertexFluxSeries (criticalLineParameter (-t)) =
      -reflectedLogJetVertexFluxSeries (criticalLineParameter t) := by
  rw [reflectedLogJetVertexFluxSeries_criticalLine_eq_sineSeries,
    reflectedLogJetVertexFluxSeries_criticalLine_eq_sineSeries]
  simp_rw [criticalPhaseSineFlux_neg]
  rw [tsum_neg]
  push_cast
  ring

/-!
## Primeira faixa formal de nao-anulamento
-/

/-- Para `0<t<=1`, toda face possui orientacao estritamente negativa. -/
theorem criticalPhaseSineFlux_neg_of_pos_of_le_one
    (n : ℕ) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    criticalPhaseSineFlux n t < 0 := by
  have hgap0 := positiveRealLogGap_pos n
  have hgap1 := positiveRealLogGap_le_one n
  have harg0 : 0 < t * positiveRealLogGap n :=
    mul_pos ht0 hgap0
  have harg1 : t * positiveRealLogGap n ≤ 1 := by
    nlinarith
  have hargPi : t * positiveRealLogGap n < Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hsin : 0 < Real.sin (t * positiveRealLogGap n) :=
    Real.sin_pos_of_pos_of_lt_pi harg0 hargPi
  unfold criticalPhaseSineFlux
  have hamp := criticalPhaseAmplitude_pos n
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by norm_num) hgap0) hamp) hsin

/-- A serie residual possui parte imaginaria estritamente negativa em toda a
faixa `0<t<=1`. -/
theorem reflectedLogJetVertexFluxSeries_criticalLine_im_neg
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (reflectedLogJetVertexFluxSeries (criticalLineParameter t)).im < 0 := by
  have hsumComplex : Summable (fun n : ℕ ↦
      reflectedLogJetVertexFlux n (criticalLineParameter t)) :=
    summable_reflectedLogJetVertexFlux
      (s := criticalLineParameter t) (by norm_num) (by norm_num)
  have hsumReal : Summable (fun n : ℕ ↦ criticalPhaseSineFlux n t) :=
    summable_criticalPhaseSineFlux t
  have hsumNeg : Summable (fun n : ℕ ↦ -criticalPhaseSineFlux n t) :=
    hsumReal.neg
  have hpositive : 0 < ∑' n : ℕ, -criticalPhaseSineFlux n t :=
    hsumNeg.tsum_pos
      (fun n ↦ neg_nonneg.mpr
        (le_of_lt (criticalPhaseSineFlux_neg_of_pos_of_le_one n ht0 ht1)))
      0
      (neg_pos.mpr
        (criticalPhaseSineFlux_neg_of_pos_of_le_one 0 ht0 ht1))
  have hnegative : (∑' n : ℕ, criticalPhaseSineFlux n t) < 0 := by
    rw [tsum_neg] at hpositive
    linarith
  unfold reflectedLogJetVertexFluxSeries
  rw [Complex.im_tsum hsumComplex]
  simpa only [reflectedLogJetVertexFlux_criticalLine_eq_sine,
    Complex.mul_im, Complex.ofReal_re, Complex.I_im,
    Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero] using hnegative

/-- Em particular, o residual critico nao se anula nessa faixa. -/
theorem reflectedLogJetVertexFluxSeries_criticalLine_ne_zero
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    reflectedLogJetVertexFluxSeries (criticalLineParameter t) ≠ 0 := by
  intro hzero
  have him := congrArg Complex.im hzero
  simp only [Complex.zero_im] at him
  linarith [reflectedLogJetVertexFluxSeries_criticalLine_im_neg ht0 ht1]

/-- Witness canonico simples fora do centro: `t=1`. -/
theorem reflectedLogJetVertexFluxSeries_one_half_add_I_ne_zero :
    reflectedLogJetVertexFluxSeries
      (((1 / 2 : ℝ) : ℂ) + Complex.I) ≠ 0 := by
  simpa [criticalLineParameter] using
    (reflectedLogJetVertexFluxSeries_criticalLine_ne_zero
      (t := (1 : ℝ)) (by norm_num) (by norm_num))

/-!
## Retorno aos tracos completos
-/

/-- Na faixa `0<t<=1`, os tracos residual e de defeito convergem para o
mesmo limite agora provadamente nao nulo; o comutador continua convergindo
para zero. -/
theorem criticalLine_completeTraces_tendsto_nonzero
    (p : ℕ) (hp : Nat.Prime p) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) :
    Tendsto (fun M : ℕ ↦
        finiteCanonicalLogJetCommutatorResidualTrace p M
          (criticalLineParameter t))
        Filter.atTop
        (nhds (reflectedLogJetVertexFluxSeries (criticalLineParameter t))) ∧
      Tendsto (fun M : ℕ ↦
        finiteCanonicalCpLogJetCommutatorWedgeTrace p M
          (criticalLineParameter t))
        Filter.atTop (nhds 0) ∧
      Tendsto (fun M : ℕ ↦
        finiteCanonicalLogJetGreenDefectTrace p M
          (criticalLineParameter t))
        Filter.atTop
        (nhds (reflectedLogJetVertexFluxSeries (criticalLineParameter t))) ∧
      reflectedLogJetVertexFluxSeries (criticalLineParameter t) ≠ 0 := by
  have htraces := criticalLine_completeTraces_tendsto
    p hp (criticalLineParameter_re t)
  exact ⟨htraces.1, htraces.2.1, htraces.2.2.1,
    reflectedLogJetVertexFluxSeries_criticalLine_ne_zero ht0 ht1⟩

end

end CPFormal.Analytic.Cp
