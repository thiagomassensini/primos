import CPFormal.Analytic.CpNativeGpreTfvdVisiblePencil
import CPFormal.Analytic.CpRealSpectralGenerator
import CPFormal.Analytic.CpAngularPort

/-!
# Camera Genuine como limite de compressoes visiveis nativas

Este modulo especializa o pencil visivel ao estado real-espectral finito. Para
`q != 0`, a coordenada vertical armazena o valor de Dirichlet vestido por
`q^n`; um observador finito remove exatamente esse dressing e le os blocos
angulares da camera canonica `p = 3`, incluindo o vertice externo.

O readout obtido e literalmente `finiteRealSpectralCamera 3 M t`. Portanto o
pencil comprimido nao recebe a carta como definicao: ele a recupera de um
estado finitamente suportado que passou pela analise
`bracket + traco + proveniencia`.

Quando `M -> infinity`, os coeficientes caracteristicos dessas compressoes
convergem para `realSpectralGenuine t`. O pencil escalar Genuine ja existente e
assim identificado como o pencil limite da familia nativa finita. Zero e valor
caracteristico desse limite exatamente nas ressonancias reais.
-/

open scoped BigOperators lp ENNReal NNReal

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-- Avaliacao que remove o dressing geometrico `q^n` de uma coordenada
vertical. -/
def carryWeightedUndressedEval (q : ℝ) (n : ℕ) :
    CarryVerticalL2 →L[ℂ] ℂ :=
  (((q : ℂ) ^ n)⁻¹) • carryVerticalL2Eval n

@[simp] theorem carryWeightedUndressedEval_apply
    (q : ℝ) (n : ℕ) (x : CarryVerticalL2) :
    carryWeightedUndressedEval q n x =
      ((q : ℂ) ^ n)⁻¹ * x n := rfl

/-- Leitura de um bloco angular `1,1,-2` depois de remover o dressing. -/
def carryWeightedCanonicalAngularBlockObserver
    (q : ℝ) (m : ℕ) : CarryVerticalL2 →L[ℂ] ℂ :=
  carryWeightedUndressedEval q (3 * m) +
    carryWeightedUndressedEval q (3 * m + 1) -
      (2 : ℂ) • carryWeightedUndressedEval q (3 * m + 2)

@[simp] theorem carryWeightedCanonicalAngularBlockObserver_apply
    (q : ℝ) (m : ℕ) (x : CarryVerticalL2) :
    carryWeightedCanonicalAngularBlockObserver q m x =
      ((q : ℂ) ^ (3 * m))⁻¹ * x (3 * m) +
        ((q : ℂ) ^ (3 * m + 1))⁻¹ * x (3 * m + 1) -
          2 * (((q : ℂ) ^ (3 * m + 2))⁻¹ * x (3 * m + 2)) := by
  rfl

/-- Observador da carta finita: soma dos blocos angulares mais o vertice
externo `3M+1`. -/
def carryWeightedFiniteChartObserver (q : ℝ) (M : ℕ) :
    CarryVerticalL2 →L[ℂ] ℂ :=
  (∑ m ∈ Finset.range M,
      carryWeightedCanonicalAngularBlockObserver q m) +
    carryWeightedUndressedEval q (3 * M)

@[simp] theorem carryWeightedFiniteChartObserver_apply
    (q : ℝ) (M : ℕ) (x : CarryVerticalL2) :
    carryWeightedFiniteChartObserver q M x =
      (∑ m ∈ Finset.range M,
        carryWeightedCanonicalAngularBlockObserver q m x) +
      carryWeightedUndressedEval q (3 * M) x := by
  rfl

/-- Estado real-espectral finito, vestido por `q^n`, antes da inclusao em
`ell^2`. -/
noncomputable def nativeGpreFiniteWeightedRealSpectralCore
    (q : ℝ) (N : ℕ) (t : ℝ) : NativeGpreComplexEdgeCore :=
  ∑ n ∈ Finset.range N,
    Finsupp.single n ((q : ℂ) ^ n * realSpectralState t n)

@[simp] theorem nativeGpreFiniteWeightedRealSpectralCore_apply_of_lt
    (q : ℝ) (N : ℕ) (t : ℝ) (n : ℕ) (hn : n < N) :
    nativeGpreFiniteWeightedRealSpectralCore q N t n =
      (q : ℂ) ^ n * realSpectralState t n := by
  classical
  simp [nativeGpreFiniteWeightedRealSpectralCore, hn]

/-- O mesmo estado visto no Hilbert vertical. O cutoff `3M+1` contem todos os
vertices usados pelos primeiros `M` blocos e pelo endpoint externo. -/
noncomputable def nativeGpreFiniteWeightedRealSpectralState
    (q : ℝ) (M : ℕ) (t : ℝ) : CarryVerticalL2 :=
  nativeGpreCanonicalVerticalRealization
    (nativeGpreFiniteWeightedRealSpectralCore q (3 * M + 1) t)

@[simp] theorem nativeGpreFiniteWeightedRealSpectralState_apply_of_lt
    (q : ℝ) (M : ℕ) (t : ℝ) (n : ℕ) (hn : n < 3 * M + 1) :
    nativeGpreFiniteWeightedRealSpectralState q M t n =
      (q : ℂ) ^ n * realSpectralState t n := by
  rw [nativeGpreFiniteWeightedRealSpectralState,
    nativeGpreCanonicalVerticalRealization_apply,
    nativeGpreFiniteWeightedRealSpectralCore_apply_of_lt q (3 * M + 1) t n hn]

/-- Remover o dressing de uma coordenada ativa recupera o estado
real-espectral literal. -/
@[simp] theorem carryWeightedUndressedEval_finiteRealSpectralState
    (q : ℝ) (hq : q ≠ 0) (M : ℕ) (t : ℝ)
    (n : ℕ) (hn : n < 3 * M + 1) :
    carryWeightedUndressedEval q n
        (nativeGpreFiniteWeightedRealSpectralState q M t) =
      realSpectralState t n := by
  rw [carryWeightedUndressedEval_apply,
    nativeGpreFiniteWeightedRealSpectralState_apply_of_lt q M t n hn]
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq
  simp [hqC]

/-- Cada bloco do observador recupera exatamente o bloco angular Dirichlet. -/
theorem carryWeightedCanonicalAngularBlockObserver_finiteRealSpectralState
    (q : ℝ) (hq : q ≠ 0) (M : ℕ) (t : ℝ)
    (m : ℕ) (hm : m < M) :
    carryWeightedCanonicalAngularBlockObserver q m
        (nativeGpreFiniteWeightedRealSpectralState q M t) =
      canonicalAngularGradientBlock m (criticalLineParameter t) := by
  have h0 : 3 * m < 3 * M + 1 := by omega
  have h1 : 3 * m + 1 < 3 * M + 1 := by omega
  have h2 : 3 * m + 2 < 3 * M + 1 := by omega
  rw [carryWeightedCanonicalAngularBlockObserver_apply,
    carryWeightedUndressedEval_finiteRealSpectralState q hq M t (3 * m) h0,
    carryWeightedUndressedEval_finiteRealSpectralState q hq M t (3 * m + 1) h1,
    carryWeightedUndressedEval_finiteRealSpectralState q hq M t (3 * m + 2) h2]
  simpa [realSpectralState] using
    (canonicalAngularGradientBlock_eq_values
      m (criticalLineParameter t)).symm

/-- O endpoint do observador recupera o vertice exterior da porta angular. -/
theorem carryWeightedFiniteChartObserver_outer_finiteRealSpectralState
    (q : ℝ) (hq : q ≠ 0) (M : ℕ) (t : ℝ) :
    carryWeightedUndressedEval q (3 * M)
        (nativeGpreFiniteWeightedRealSpectralState q M t) =
      positiveDirichletValue (criticalLineParameter t) (3 * M) := by
  have h : 3 * M < 3 * M + 1 := by omega
  simpa [realSpectralState] using
    carryWeightedUndressedEval_finiteRealSpectralState
      q hq M t (3 * M) h

/-- A leitura finita do estado nativo e literalmente a carta bracketada
real-espectral da camera `3`. -/
theorem carryWeightedFiniteChartObserver_finiteRealSpectralState
    (q : ℝ) (hq : q ≠ 0) (M : ℕ) (t : ℝ) :
    carryWeightedFiniteChartObserver q M
        (nativeGpreFiniteWeightedRealSpectralState q M t) =
      finiteRealSpectralChart 3 M t := by
  rw [carryWeightedFiniteChartObserver_apply]
  calc
    (∑ m ∈ Finset.range M,
        carryWeightedCanonicalAngularBlockObserver q m
          (nativeGpreFiniteWeightedRealSpectralState q M t)) +
        carryWeightedUndressedEval q (3 * M)
          (nativeGpreFiniteWeightedRealSpectralState q M t) =
      finiteCanonicalAngularTrace M (criticalLineParameter t) +
        positiveDirichletValue (criticalLineParameter t) (3 * M) := by
          congr 1
          · unfold finiteCanonicalAngularTrace
            apply Finset.sum_congr rfl
            intro m hm
            exact carryWeightedCanonicalAngularBlockObserver_finiteRealSpectralState
              q hq M t m (Finset.mem_range.mp hm)
          · exact
              carryWeightedFiniteChartObserver_outer_finiteRealSpectralState
                q hq M t
    _ = finiteBracketedDirichletChart 3 M (criticalLineParameter t) :=
      (finiteBracketedDirichletChart_three_eq_angularTrace_add_outer
        M (criticalLineParameter t)).symm
    _ = finiteRealSpectralChart 3 M t := rfl

/-- Observador normalizado pela camera `3`; o fator e nao nulo em toda a
orbita real critica. -/
def nativeGpreFiniteGenuineObserver
    (q : ℝ) (M : ℕ) (t : ℝ) : CarryVerticalL2 →L[ℂ] ℂ :=
  (realSpectralChartFactor 3 t)⁻¹ • carryWeightedFiniteChartObserver q M

/-- O observador normalizado recupera exatamente a camera finita. -/
@[simp] theorem nativeGpreFiniteGenuineObserver_finiteRealSpectralState
    (q : ℝ) (hq : q ≠ 0) (M : ℕ) (t : ℝ) :
    nativeGpreFiniteGenuineObserver q M t
        (nativeGpreFiniteWeightedRealSpectralState q M t) =
      finiteRealSpectralCamera 3 M t := by
  change
    (realSpectralChartFactor 3 t)⁻¹ *
        carryWeightedFiniteChartObserver q M
          (nativeGpreFiniteWeightedRealSpectralState q M t) =
      finiteRealSpectralCamera 3 M t
  rw [carryWeightedFiniteChartObserver_finiteRealSpectralState q hq M t]
  simp [finiteRealSpectralCamera, div_eq_mul_inv, mul_comm]

/-- Pencil nativo comprimido no corte `M`, com coeficiente igual a camera
Genuine finita. -/
def nativeGpreFiniteGenuineBoundaryPencil
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (M : ℕ) (t : ℝ) :
    RegularLinearBoundaryPencil ℂ ℂ :=
  nativeGpreFiniteTfvdVisibleBoundaryPencil q hq0 hq1 S
    (nativeGpreFiniteGenuineObserver q M t)
    (nativeGpreFiniteWeightedRealSpectralState q M t)

/-- Os valores caracteristicos do corte sao exatamente a camera finita. -/
theorem nativeGpreFiniteGenuine_isCharacteristicValue_iff
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (M : ℕ) (t : ℝ)
    (lambda : ℂ) :
    (nativeGpreFiniteGenuineBoundaryPencil
        q hqpos.le hq1 S M t).toLinearBoundaryPencil.IsCharacteristicValue
          lambda ↔
      lambda = finiteRealSpectralCamera 3 M t := by
  rw [nativeGpreFiniteTfvdVisible_isCharacteristicValue_iff
    q hqpos hq1 S
      (nativeGpreFiniteGenuineObserver q M t)
      (nativeGpreFiniteWeightedRealSpectralState q M t) lambda]
  rw [nativeGpreFiniteGenuineObserver_finiteRealSpectralState
    q hqpos.ne' M t]

/-- No corte, zero e caracteristico exatamente quando a camera finita fecha. -/
theorem nativeGpreFiniteGenuine_zeroCharacteristic_iff
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (M : ℕ) (t : ℝ) :
    (nativeGpreFiniteGenuineBoundaryPencil
        q hqpos.le hq1 S M t).toLinearBoundaryPencil.IsCharacteristicValue
          0 ↔
      finiteRealSpectralCamera 3 M t = 0 := by
  simpa [eq_comm] using
    (nativeGpreFiniteGenuine_isCharacteristicValue_iff
      q hqpos hq1 S M t 0)

/-- As cameras finitas canonicas convergem para o Genuine real-espectral. -/
theorem finiteRealSpectralCamera_three_tendsto_realSpectralGenuine
    (t : ℝ) :
    Tendsto (fun M : ℕ => finiteRealSpectralCamera 3 M t)
      atTop (nhds (realSpectralGenuine t)) := by
  have hchart := finiteBracketedDirichletChart_tendsto
    3 (by norm_num : Nat.Prime 3)
    (s := criticalLineParameter t) (by norm_num)
  have hscaled := hchart.mul_const ((realSpectralChartFactor 3 t)⁻¹)
  have hfactor : realSpectralChartFactor 3 t ≠ 0 :=
    realSpectralChartFactor_ne_zero 3 (by norm_num) t
  have hlimit :
      bracketedDirichletChart 3 (criticalLineParameter t) *
          (realSpectralChartFactor 3 t)⁻¹ =
        realSpectralGenuine t := by
    rw [bracketedDirichletChart_criticalLine_eq_factor_mul_realSpectralGenuine
      3 (by norm_num) (by norm_num) t]
    field_simp [hfactor]
  convert hscaled using 1 <;>
    simp [finiteRealSpectralCamera, finiteRealSpectralChart,
      div_eq_mul_inv, hlimit]

/-- Os coeficientes caracteristicos da familia de pencils nativos convergem ao
coeficiente do pencil Genuine escalar. -/
theorem nativeGpreFiniteGenuineBoundaryLinearization_tendsto
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (t : ℝ) :
    Tendsto
      (fun M : ℕ =>
        (nativeGpreFiniteGenuineBoundaryPencil
          q hqpos.le hq1 S M t).linearization 1)
      atTop
      (nhds ((realSpectralGenuineBoundaryPencil t).linearization 1)) := by
  have h := finiteRealSpectralCamera_three_tendsto_realSpectralGenuine t
  simpa [nativeGpreFiniteGenuineBoundaryPencil] using h

/-- Num zero Genuine, os coeficientes das compressoes finitas tendem a zero. -/
theorem nativeGpreFiniteGenuineBoundaryLinearization_tendsto_zero_of_resonance
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) {t : ℝ}
    (hres : IsRealSpectralResonance t) :
    Tendsto
      (fun M : ℕ =>
        (nativeGpreFiniteGenuineBoundaryPencil
          q hqpos.le hq1 S M t).linearization 1)
      atTop (nhds 0) := by
  have h := nativeGpreFiniteGenuineBoundaryLinearization_tendsto
    q hqpos hq1 S t
  change realSpectralGenuine t = 0 at hres
  simpa [hres] using h

/-- O pencil limite da familia nativa e o pencil escalar Genuine. -/
def nativeGpreGenuineLimitBoundaryPencil (t : ℝ) :
    RegularLinearBoundaryPencil ℂ ℂ :=
  realSpectralGenuineBoundaryPencil t

/-- Fechamento final da cadeia: ressonancia real equivale a zero caracteristico
do pencil limite das compressoes nativas. -/
theorem isRealSpectralResonance_iff_nativeGpreGenuineLimit_zeroCharacteristic
    (t : ℝ) :
    IsRealSpectralResonance t ↔
      (nativeGpreGenuineLimitBoundaryPencil t).toLinearBoundaryPencil.
        IsCharacteristicValue 0 := by
  exact isRealSpectralResonance_iff_zero_characteristicValue t

end

end CPFormal.Analytic.Cp
