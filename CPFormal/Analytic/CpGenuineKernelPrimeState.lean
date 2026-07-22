import CPFormal.Analytic.CpGenuinePrimeGreenBessel
import CPFormal.Analytic.CpGenuineCarrySaturationTransport
import CPFormal.Analytic.CpNativeGprePrimeTowerBessel
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Estado multiprima do bulk Green e o kernel Genuine

Este modulo constroi primeiro os estados canonicos em todo atlas finito de
cameras primas. A norma quadrada desses estados e exatamente a soma parcial
do perfil Green centrado

`primeCarryGreenBulkCutoffProfile M s p`.

Em seguida registramos o criterio exato de completacao: para qualquer cutoff
nao vazio, os estados finitos possuem norma uniformemente limitada quando o
atlas primo cresce se, e somente se, o deslocamento critico e zero. Isto
permite construir um unico vetor em `ell^2(Nat.Primes)` exatamente nesse
locus.

O ultimo bloco deixa explicita a obrigacao do kernel Genuine. A afirmacao de
que todo zero Genuine produz esse estado multiprima e equivalente a
`GenuineZeroSaturatesCarry 3`; portanto ela nao e introduzida como uma
definicao nem deduzida da mera compatibilidade projetiva dos atlas finitos.
-/

open scoped BigOperators ENNReal

namespace CPFormal.Analytic.Cp

open CPFormal.Carry.Cp

noncomputable section

/-! ## Forma Dirichlet refletida do perfil radial -/

/-- Vestir a diferenca radial pela amplitude critica `p^(-1/2)` produz
literalmente a diferenca entre os dois expoentes Dirichlet refletidos. Esta
identidade e a parte util da antiga leitura C2--zeta para a rota multiprima. -/
theorem primeCarryGreenRadialProfile_eq_reflectedDirichletGap
    (sigma : ℝ) (p : Nat.Primes) :
    primeCarryGreenRadialProfile (criticalDisplacement sigma) p =
      (p : ℝ) ^ (sigma - 1) - (p : ℝ) ^ (-sigma) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  rw [primeCarryGreenRadialProfile,
    primeCarryAmplitudeRatio_eq_criticalAmplitude_one]
  unfold criticalAmplitude cpRadialDifference criticalDisplacement
  norm_num
  rw [mul_sub, ← Real.rpow_add hp, ← Real.rpow_add hp]
  congr 2 <;> ring

/-- A coordenada de cutoff e o mesmo gap Dirichlet refletido multiplicado
pela energia Green positiva comum a todas as cameras. -/
theorem primeCarryGreenBulkCutoffProfile_eq_reflectedDirichletGap_mul
    (M : ℕ) (s : ℂ) (p : Nat.Primes) :
    primeCarryGreenBulkCutoffProfile M s p =
      ((p : ℝ) ^ (s.re - 1) - (p : ℝ) ^ (-s.re)) *
        (finiteReflectedGradientPairing M s).re := by
  rw [primeCarryGreenBulkCutoffProfile_eq,
    primeCarryGreenRadialProfile_eq_reflectedDirichletGap]

/-! ## Hilbert global das cameras primas -/

/-- Soma Hilbert real das cameras indexadas pelos primos. -/
abbrev PrimeGreenCameraHilbert := lp (fun _ : Nat.Primes => ℝ) 2

/-- Eixo canonico de uma camera prima no Hilbert global. -/
def primeGreenCameraAxis (p : Nat.Primes) : PrimeGreenCameraHilbert :=
  lp.single 2 p 1

/-- Os eixos canonicos das cameras primas sao ortonormais. -/
theorem primeGreenCameraAxis_orthonormal :
    Orthonormal ℝ primeGreenCameraAxis := by
  classical
  rw [orthonormal_iff_ite]
  intro p q
  rw [primeGreenCameraAxis, primeGreenCameraAxis,
    lp.inner_single_left]
  simp [lp.single_apply, Pi.single_apply]

/-- A coordenada contra o eixo primo e literalmente a avaliacao do vetor. -/
@[simp] theorem inner_primeGreenCameraAxis
    (p : Nat.Primes) (v : PrimeGreenCameraHilbert) :
    inner ℝ (primeGreenCameraAxis p) v = v p := by
  classical
  rw [primeGreenCameraAxis, lp.inner_single_left]
  simp

/-! ## Estados canonicos em atlas finito -/

/-- Estado Green centrado quando somente um atlas finito de primos e
mantido. Este objeto existe para todo `s`; a questao global e a uniformidade
de sua norma quando o atlas cresce. -/
def primeGreenBulkFiniteState
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) : PrimeGreenCameraHilbert :=
  ∑ p ∈ S,
    lp.single 2 p (primeCarryGreenBulkCutoffProfile M s p)

/-- Coordenadas exatas do estado de atlas finito. -/
@[simp] theorem primeGreenBulkFiniteState_apply
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) (p : Nat.Primes) :
    primeGreenBulkFiniteState M s S p =
      if p ∈ S then primeCarryGreenBulkCutoffProfile M s p else 0 := by
  classical
  simp only [primeGreenBulkFiniteState, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_single, Finset.sum_pi_single]

/-- A norma quadrada do estado finito e exatamente o ledger de Bessel do
atlas, sem perda por desigualdade. -/
theorem primeGreenBulkFiniteState_norm_sq
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) :
    ‖primeGreenBulkFiniteState M s S‖ ^ 2 =
      ∑ p ∈ S, (primeCarryGreenBulkCutoffProfile M s p) ^ 2 := by
  simpa [primeGreenBulkFiniteState, Real.norm_eq_abs, sq_abs] using
    (lp.norm_sum_single
      (E := fun _ : Nat.Primes => ℝ)
      (p := (2 : ℝ≥0∞)) (by norm_num)
      (fun p : Nat.Primes => primeCarryGreenBulkCutoffProfile M s p) S)

/-- Todo atlas finito admite uma realizacao exata, para qualquer parametro
espectral. Portanto existencia e compatibilidade em cada atlas finito nao
podem, sozinhas, selecionar a meia-abscissa. -/
theorem exists_primeGreenBulkFiniteState_realization
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) :
    ∃ v : PrimeGreenCameraHilbert,
      ∀ p ∈ S, v p = primeCarryGreenBulkCutoffProfile M s p := by
  exact ⟨primeGreenBulkFiniteState M s S, by
    intro p hp
    simp [hp]⟩

/-- Uniformidade dos estados finitos no unico indice relevante: o atlas de
primos. Nao se pede uniformidade no cutoff Green `M`. -/
def PrimeGreenBulkFiniteStatesBounded (M : ℕ) (s : ℂ) : Prop :=
  ∃ C : ℝ, ∀ S : Finset Nat.Primes,
    ‖primeGreenBulkFiniteState M s S‖ ^ 2 ≤ C

/-- Em qualquer cutoff nao vazio, a uniformidade dos atlas finitos seleciona
exatamente a meia-abscissa. -/
theorem primeGreenBulkFiniteStatesBounded_iff
    (M : ℕ) (hM : 0 < M)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    PrimeGreenBulkFiniteStatesBounded M s ↔
      criticalDisplacement s.re = 0 := by
  constructor
  · rintro ⟨C, hC⟩
    apply criticalDisplacement_eq_zero_of_primeGreen_bulk_bessel_at_cutoff
      M hM hs C
    intro S
    rw [← primeGreenBulkFiniteState_norm_sq]
    exact hC S
  · intro hcritical
    refine ⟨0, ?_⟩
    intro S
    have hprofile : ∀ p : Nat.Primes,
        primeCarryGreenBulkCutoffProfile M s p = 0 := by
      intro p
      rw [primeCarryGreenBulkCutoffProfile_eq]
      simp [hcritical, primeCarryGreenRadialProfile,
        cpRadialDifference]
    rw [primeGreenBulkFiniteState_norm_sq]
    simp [hprofile]

/-! ## Estado global e criterio exato de existencia -/

/-- Um vetor global realiza o bulk centrado quando todas as suas coordenadas
primas sao exatamente as leituras Green vestidas. -/
def IsPrimeGreenBulkStateAt
    (M : ℕ) (s : ℂ) (v : PrimeGreenCameraHilbert) : Prop :=
  ∀ p : Nat.Primes, v p = primeCarryGreenBulkCutoffProfile M s p

/-- Existir um estado global e equivalente a quadrado-somabilidade do perfil.
Esta e a passagem precisa de atlas finitos para o Hilbert completo. -/
theorem exists_isPrimeGreenBulkStateAt_iff_summable
    (M : ℕ) (s : ℂ) :
    (∃ v : PrimeGreenCameraHilbert, IsPrimeGreenBulkStateAt M s v) ↔
      Summable (fun p : Nat.Primes =>
        (primeCarryGreenBulkCutoffProfile M s p) ^ 2) := by
  constructor
  · rintro ⟨v, hv⟩
    have hsum := (lp.memℓp v).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    have hsum' : Summable (fun p : Nat.Primes => (v p) ^ 2) := by
      simpa [Real.norm_eq_abs, sq_abs] using hsum
    exact hsum'.congr fun p => by rw [hv p]
  · intro hsum
    let f : PreLp (fun _ : Nat.Primes => ℝ) :=
      fun p => primeCarryGreenBulkCutoffProfile M s p
    have hf : Memℓp f 2 := by
      rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
      simpa [f, Real.norm_eq_abs, sq_abs] using hsum
    refine ⟨⟨f, hf⟩, ?_⟩
    intro p
    rfl

/-- Um unico estado global, em um unico cutoff nao vazio, ja detecta
exatamente o deslocamento critico. -/
theorem exists_isPrimeGreenBulkStateAt_iff_criticalDisplacement_eq_zero
    (M : ℕ) (hM : 0 < M)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    (∃ v : PrimeGreenCameraHilbert, IsPrimeGreenBulkStateAt M s v) ↔
      criticalDisplacement s.re = 0 := by
  rw [exists_isPrimeGreenBulkStateAt_iff_summable,
    summable_primeCarryGreenBulkCutoffProfile_sq_iff M hM hs]

/-- A completude Hilbert dos atlas finitos e exatamente a uniformidade de
suas normas. A mera colagem projetiva, que existe para todo `s`, nao aparece
como substituta dessa condicao. -/
theorem primeGreenBulkFiniteStatesBounded_iff_exists_global_state
    (M : ℕ) (hM : 0 < M)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    PrimeGreenBulkFiniteStatesBounded M s ↔
      ∃ v : PrimeGreenCameraHilbert, IsPrimeGreenBulkStateAt M s v := by
  rw [primeGreenBulkFiniteStatesBounded_iff M hM hs,
    exists_isPrimeGreenBulkStateAt_iff_criticalDisplacement_eq_zero M hM hs]

/-- A realizacao global e a realizacao ortogonal pedida pelo argumento de
Bessel: suas coordenadas sao inner products contra os eixos primos. -/
theorem isPrimeGreenBulkStateAt_iff_inner_coordinates
    (M : ℕ) (s : ℂ) (v : PrimeGreenCameraHilbert) :
    IsPrimeGreenBulkStateAt M s v ↔
      ∀ p : Nat.Primes,
        inner ℝ (primeGreenCameraAxis p) v =
          primeCarryGreenBulkCutoffProfile M s p := by
  simp only [IsPrimeGreenBulkStateAt, inner_primeGreenCameraAxis]

/-! ## Analise multiprima concreta da torre nativa `G_pre` -/

/-- Cauchy--Schwarz para um momento primo individual da torre nativa. -/
private theorem nativeGpreTowerPrimeMoment_sq_le
    (tau : ℕ) (x : NativeGpreTowerHilbert) (p : Nat.Primes) :
    (inner ℝ (nativeGpreTowerProfileVector (p : ℕ) tau) x) ^ 2 ≤
      ‖x‖ ^ 2 * ‖nativeGpreTowerProfileVector (p : ℕ) tau‖ ^ 2 := by
  have hinner :=
    abs_real_inner_le_norm
      (nativeGpreTowerProfileVector (p : ℕ) tau) x
  have hnonneg :
      0 ≤ ‖nativeGpreTowerProfileVector (p : ℕ) tau‖ * ‖x‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have habsnonneg :
      0 ≤ |inner ℝ (nativeGpreTowerProfileVector (p : ℕ) tau) x| :=
    abs_nonneg _
  have hsq :
      |inner ℝ (nativeGpreTowerProfileVector (p : ℕ) tau) x| ^ 2 ≤
        (‖nativeGpreTowerProfileVector (p : ℕ) tau‖ * ‖x‖) ^ 2 := by
    nlinarith
  simpa [sq_abs, mul_pow, mul_comm] using hsq

/-- Todo vetor da torre nativa possui momentos quadrado-somaveis contra os
perfis primos em tempo aritmetico positivo. Nao se usa ortogonalidade: a
somabilidade das normas dos perfis e Cauchy--Schwarz bastam. -/
theorem summable_nativeGpreTowerPrimeMoment_sq_over_primes
    (tau : ℕ) (htau : 1 ≤ tau) (x : NativeGpreTowerHilbert) :
    Summable (fun p : Nat.Primes =>
      (inner ℝ (nativeGpreTowerProfileVector (p : ℕ) tau) x) ^ 2) := by
  have hnorm :=
    summable_nativeGpreTowerProfileVector_norm_sq_over_primes tau htau
  have hmajor : Summable (fun p : Nat.Primes =>
      ‖x‖ ^ 2 * ‖nativeGpreTowerProfileVector (p : ℕ) tau‖ ^ 2) :=
    hnorm.mul_left (‖x‖ ^ 2)
  exact Summable.of_nonneg_of_le
    (fun p => sq_nonneg _)
    (fun p => nativeGpreTowerPrimeMoment_sq_le tau x p)
    hmajor

/-- Vetor multiprima produzido canonicamente por um estado da torre nativa.
Sua coordenada `p` e o momento contra o perfil material da camera `p`. -/
def nativeGprePrimeMomentState
    (tau : ℕ) (htau : 1 ≤ tau)
    (x : NativeGpreTowerHilbert) : PrimeGreenCameraHilbert :=
  let f : PreLp (fun _ : Nat.Primes => ℝ) :=
    fun p => inner ℝ (nativeGpreTowerProfileVector (p : ℕ) tau) x
  ⟨f, by
    change Memℓp f 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    simpa [f, Real.norm_eq_abs, sq_abs] using
      summable_nativeGpreTowerPrimeMoment_sq_over_primes tau htau x⟩

@[simp] theorem nativeGprePrimeMomentState_apply
    (tau : ℕ) (htau : 1 ≤ tau)
    (x : NativeGpreTowerHilbert) (p : Nat.Primes) :
    nativeGprePrimeMomentState tau htau x p =
      inner ℝ (nativeGpreTowerProfileVector (p : ℕ) tau) x := rfl

/-- Forma de atlas finito da cota de momentos `G_pre`. -/
theorem sum_nativeGpreTowerPrimeMoment_sq_le
    (tau : ℕ) (x : NativeGpreTowerHilbert) (S : Finset Nat.Primes) :
    (∑ p ∈ S,
      (inner ℝ (nativeGpreTowerProfileVector (p : ℕ) tau) x) ^ 2) ≤
      ‖x‖ ^ 2 *
        ∑ p ∈ S, ‖nativeGpreTowerProfileVector (p : ℕ) tau‖ ^ 2 := by
  calc
    (∑ p ∈ S,
        (inner ℝ (nativeGpreTowerProfileVector (p : ℕ) tau) x) ^ 2) ≤
        ∑ p ∈ S,
          ‖x‖ ^ 2 * ‖nativeGpreTowerProfileVector (p : ℕ) tau‖ ^ 2 := by
      gcongr with p hp
      exact nativeGpreTowerPrimeMoment_sq_le tau x p
    _ = ‖x‖ ^ 2 *
        ∑ p ∈ S, ‖nativeGpreTowerProfileVector (p : ℕ) tau‖ ^ 2 := by
      rw [Finset.mul_sum]

/-- Um estado da torre `G_pre` realiza o bulk Green quando seus momentos
primos sao exatamente as leituras centradas. Esta e a identidade de
coordenadas que ainda deve nascer do kernel Genuine. -/
def IsNativeGprePrimeMomentRealizationAt
    (tau M : ℕ) (s : ℂ) (x : NativeGpreTowerHilbert) : Prop :=
  ∀ p : Nat.Primes,
    inner ℝ (nativeGpreTowerProfileVector (p : ℕ) tau) x =
      primeCarryGreenBulkCutoffProfile M s p

/-- A identidade de momentos diz literalmente que o vetor multiprima
produzido por `G_pre` realiza o perfil Green centrado. -/
theorem isNativeGprePrimeMomentRealizationAt_iff_state
    (tau : ℕ) (htau : 1 ≤ tau)
    (M : ℕ) (s : ℂ) (x : NativeGpreTowerHilbert) :
    IsNativeGprePrimeMomentRealizationAt tau M s x ↔
      IsPrimeGreenBulkStateAt M s
        (nativeGprePrimeMomentState tau htau x) := by
  rfl

/-- Em tempo aritmetico positivo e cutoff Green nao vazio, existir uma
realizacao por momentos da torre nativa equivale exatamente a estar na
meia-abscissa. A volta usa o estado zero; a ida usa a cota `G_pre`. -/
theorem exists_isNativeGprePrimeMomentRealizationAt_iff
    (tau : ℕ) (htau : 1 ≤ tau)
    (M : ℕ) (hM : 0 < M)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    (∃ x : NativeGpreTowerHilbert,
      IsNativeGprePrimeMomentRealizationAt tau M s x) ↔
        criticalDisplacement s.re = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    apply (summable_primeCarryGreenBulkCutoffProfile_sq_iff M hM hs).1
    exact
      (summable_nativeGpreTowerPrimeMoment_sq_over_primes tau htau x).congr
        fun p => by rw [hx p]
  · intro hcritical
    refine ⟨0, ?_⟩
    intro p
    rw [primeCarryGreenBulkCutoffProfile_eq]
    simp [hcritical, primeCarryGreenRadialProfile, cpRadialDifference]

/-! ## Obrigacao exata do kernel Genuine -/

/-- Todo zero Genuine produz um estado multiprima no primeiro cutoff Green.
O cutoff `1` e suficiente e evita uma hipotese artificial de uniformidade em
`M`. -/
def GenuineKernelHasPrimeGreenState : Prop :=
  ∀ {s : ℂ}, genuineContinuation s = 0 →
    s ∈ genuineCriticalStrip →
      ∃ v : PrimeGreenCameraHilbert, IsPrimeGreenBulkStateAt 1 s v

/-- Versao nativa da mesma obrigacao: todo zero Genuine deveria produzir um
estado da torre cujo perfil de momentos em `tau = 1` fosse o bulk Green no
primeiro cutoff. -/
def GenuineKernelHasNativeGprePrimeMomentState : Prop :=
  ∀ {s : ℂ}, genuineContinuation s = 0 →
    s ∈ genuineCriticalStrip →
      ∃ x : NativeGpreTowerHilbert,
        IsNativeGprePrimeMomentRealizationAt 1 1 s x

/-- O estado multiprima do kernel e exatamente a localizacao dos zeros na
meia-abscissa. Este teorema impede que a existencia do vetor seja usada como
uma hipotese aparentemente mais fraca que ja contenha a conclusao. -/
theorem genuineKernelHasPrimeGreenState_iff :
    GenuineKernelHasPrimeGreenState ↔
      ∀ {s : ℂ}, genuineContinuation s = 0 →
        s ∈ genuineCriticalStrip →
          criticalDisplacement s.re = 0 := by
  constructor
  · intro hstate s hzero hs
    exact
      (exists_isPrimeGreenBulkStateAt_iff_criticalDisplacement_eq_zero
        1 (by norm_num) hs).1 (hstate hzero hs)
  · intro hcritical s hzero hs
    exact
      (exists_isPrimeGreenBulkStateAt_iff_criticalDisplacement_eq_zero
        1 (by norm_num) hs).2 (hcritical hzero hs)

/-- A formulacao por momentos `G_pre` e a formulacao pelo estado canonico em
`ell^2` sao logicamente equivalentes. Assim, a somabilidade material de
`G_pre` resolve a analise de Bessel, mas nao fabrica por si mesma a identidade
de momentos a partir do zero Genuine. -/
theorem genuineKernelHasNativeGprePrimeMomentState_iff_primeGreenState :
    GenuineKernelHasNativeGprePrimeMomentState ↔
      GenuineKernelHasPrimeGreenState := by
  constructor
  · intro hmoment s hzero hs
    have hcritical :=
      (exists_isNativeGprePrimeMomentRealizationAt_iff
        1 (by norm_num) 1 (by norm_num) hs).1 (hmoment hzero hs)
    exact
      (exists_isPrimeGreenBulkStateAt_iff_criticalDisplacement_eq_zero
        1 (by norm_num) hs).2 hcritical
  · intro hstate s hzero hs
    have hcritical :=
      (exists_isPrimeGreenBulkStateAt_iff_criticalDisplacement_eq_zero
        1 (by norm_num) hs).1 (hstate hzero hs)
    exact
      (exists_isNativeGprePrimeMomentRealizationAt_iff
        1 (by norm_num) 1 (by norm_num) hs).2 hcritical

/-- A obrigacao do estado multiprima coincide com a obrigacao de saturacao
do carry ja registrada para a camera canonica `3`. -/
theorem genuineKernelHasPrimeGreenState_iff_genuineZeroSaturatesCarry_three :
    GenuineKernelHasPrimeGreenState ↔ GenuineZeroSaturatesCarry 3 := by
  rw [genuineKernelHasPrimeGreenState_iff]
  constructor
  · intro hcritical s hzero hs
    apply (branchNormSq_eq_one_iff 3 (by norm_num) hs.1).2
    have hdelta := hcritical hzero hs
    unfold criticalDisplacement at hdelta
    linarith
  · intro hsaturates s hzero hs
    have hre : s.re = (1 : ℝ) / 2 :=
      (branchNormSq_eq_one_iff 3 (by norm_num) hs.1).1
        (hsaturates hzero hs)
    unfold criticalDisplacement
    linarith

/-- Se a construcao do estado do kernel for fornecida, o `ne 0` forte do
Genuine escalar fora da meia-abscissa segue por contradicao. -/
theorem genuineContinuation_ne_zero_of_re_ne_half_of_kernelPrimeGreenState
    (hstate : GenuineKernelHasPrimeGreenState)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    genuineContinuation s ≠ 0 := by
  intro hzero
  have hdelta := (genuineKernelHasPrimeGreenState_iff.1 hstate) hzero hs
  apply hoff
  unfold criticalDisplacement at hdelta
  linarith

end

end CPFormal.Analytic.Cp
