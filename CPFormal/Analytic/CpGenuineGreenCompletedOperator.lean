import CPFormal.Analytic.CpGenuineFirstOrthogonalGreenLimit
import CPFormal.Analytic.CpCarryAmplitudeIdentification
import CPFormal.Analytic.CpRealSpectralOperator
import Mathlib.LinearAlgebra.Prod

/-!
# Operador Genuine completado pelo canal Green do carry

A sintese escalar Genuine e o fluxo Green vivem em canais diferentes. Num
zero Genuine, o primeiro canal fecha, enquanto o segundo converge para o bulk
radial

`cpRadialDifference p (criticalDisplacement s.re) * infiniteReflectedGreenEnergy s`.

Este modulo preserva os dois canais numa soma direta. O primeiro bloco e o
operador Genuine ortogonal ja construido. O segundo bloco e a complexificacao
diagonal do vetor Green alinhado. O operador completado nao postula uma ponte
entre os dois kernels: ele conserva simultaneamente as duas informacoes que a
sintese escalar mantinha separadas.

O resultado principal identifica seu kernel sem hipoteses adicionais:

`completedOperator p q s = 0` se, e somente se,

`genuineContinuation s = 0` e `criticalDisplacement s.re = 0`.

Consequentemente, o operador completado e nao nulo fora da meia abscissa.
Esta conclusao e sobre o operador em soma direta; ela nao rebatiza como prova
uma inclusao entre o kernel do Genuine escalar e o kernel Green.
-/

open scoped Topology

namespace CPFormal.Analytic.Cp

open CPFormal.Carry.Cp
open Filter

noncomputable section

/-! ## Complexificacao do canal Green -/

/-- O vetor Green real, usado como os dois coeficientes de um operador
diagonal complexo. -/
def complexifiedAlignedGreenLimitOperator
    (p q : ℕ) (s : ℂ) : Module.End ℂ TwoPrimeGenuineHilbert :=
  twoPrimeGenuineDiagonalOperator
    ((crossPrimeAlignedGreenLimitVector p q s (0 : Fin 2) : ℝ) : ℂ)
    ((crossPrimeAlignedGreenLimitVector p q s (1 : Fin 2) : ℝ) : ℂ)

/-- Versao finita do mesmo canal: as duas coordenadas sao os fluxos Green nos
cutoffs cruzados alinhados. -/
def finiteComplexifiedAlignedGreenFluxOperator
    (p q L : ℕ) (s : ℂ) : Module.End ℂ TwoPrimeGenuineHilbert :=
  twoPrimeGenuineDiagonalOperator
    ((crossPrimeAlignedGreenFluxVector p q L s (0 : Fin 2) : ℝ) : ℂ)
    ((crossPrimeAlignedGreenFluxVector p q L s (1 : Fin 2) : ℝ) : ℂ)

/-! ## Rigidez da concordancia entre cameras Green -/

/-- Para duas bases primas distintas, os fatores radiais coincidem somente
no equilibrio transversal. -/
theorem cpRadialDifference_eq_cpRadialDifference_iff
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (delta : ℝ) :
    cpRadialDifference p delta = cpRadialDifference q delta ↔
      delta = 0 := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq.pos
  constructor
  · intro heq
    by_contra hdelta
    rcases lt_or_gt_of_ne hpq with hpqlt | hqplt
    · have hpqR : (p : ℝ) < (q : ℝ) := by exact_mod_cast hpqlt
      rcases lt_or_gt_of_ne hdelta with hdneg | hdpos
      · have h₁ : (q : ℝ) ^ delta < (p : ℝ) ^ delta :=
          Real.rpow_lt_rpow_of_neg hpR hpqR hdneg
        have h₂ : (p : ℝ) ^ (-delta) < (q : ℝ) ^ (-delta) :=
          Real.rpow_lt_rpow hpR.le hpqR (neg_pos.mpr hdneg)
        unfold cpRadialDifference at heq
        linarith
      · have h₁ : (p : ℝ) ^ delta < (q : ℝ) ^ delta :=
          Real.rpow_lt_rpow hpR.le hpqR hdpos
        have h₂ : (q : ℝ) ^ (-delta) < (p : ℝ) ^ (-delta) :=
          Real.rpow_lt_rpow_of_neg hpR hpqR (neg_neg_of_pos hdpos)
        unfold cpRadialDifference at heq
        linarith
    · have hqpR : (q : ℝ) < (p : ℝ) := by exact_mod_cast hqplt
      rcases lt_or_gt_of_ne hdelta with hdneg | hdpos
      · have h₁ : (p : ℝ) ^ delta < (q : ℝ) ^ delta :=
          Real.rpow_lt_rpow_of_neg hqR hqpR hdneg
        have h₂ : (q : ℝ) ^ (-delta) < (p : ℝ) ^ (-delta) :=
          Real.rpow_lt_rpow hqR.le hqpR (neg_pos.mpr hdneg)
        unfold cpRadialDifference at heq
        linarith
      · have h₁ : (q : ℝ) ^ delta < (p : ℝ) ^ delta :=
          Real.rpow_lt_rpow hqR.le hqpR hdpos
        have h₂ : (p : ℝ) ^ (-delta) < (q : ℝ) ^ (-delta) :=
          Real.rpow_lt_rpow_of_neg hqR hqpR (neg_neg_of_pos hdpos)
        unfold cpRadialDifference at heq
        linarith
  · rintro rfl
    simp [cpRadialDifference]

/-- Em duas cameras primas distintas, a concordancia das coordenadas do
vetor Green limite detecta exatamente o equilibrio transversal. Esta rota e
mais fraca do que exigir que as duas coordenadas sejam zero. -/
theorem crossPrimeAlignedGreenLimitVector_coordinates_eq_iff
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    crossPrimeAlignedGreenLimitVector p q s (0 : Fin 2) =
        crossPrimeAlignedGreenLimitVector p q s (1 : Fin 2) ↔
      criticalDisplacement s.re = 0 := by
  let delta := criticalDisplacement s.re
  let E := infiniteReflectedGreenEnergy s
  have hE : E ≠ 0 := ne_of_gt (infiniteReflectedGreenEnergy_pos hs)
  constructor
  · intro hcoord
    have hmul :
        cpRadialDifference p delta * E =
          cpRadialDifference q delta * E := by
      simpa [crossPrimeAlignedGreenLimitVector, delta, E] using hcoord
    exact (cpRadialDifference_eq_cpRadialDifference_iff
      p q hp hq hpq delta).1 (mul_right_cancel₀ hE hmul)
  · intro hdelta
    have hcoeff := (cpRadialDifference_eq_cpRadialDifference_iff
      p q hp hq hpq delta).2 hdelta
    simpa [crossPrimeAlignedGreenLimitVector, delta, E] using
      congrArg (fun x : ℝ => x * E) hcoeff

/-- Complexificar o vetor Green e coloca-lo na diagonal nao altera seu locus
de anulacao. -/
theorem complexifiedAlignedGreenLimitOperator_eq_zero_iff_limitVector_eq_zero
    (p q : ℕ) (s : ℂ) :
    complexifiedAlignedGreenLimitOperator p q s = 0 ↔
      crossPrimeAlignedGreenLimitVector p q s = 0 := by
  constructor
  · intro hop
    have hzero := congrArg
      (fun T : Module.End ℂ TwoPrimeGenuineHilbert =>
        T (firstPrimeGenuineAxis 1) (0 : Fin 2)) hop
    have hone := congrArg
      (fun T : Module.End ℂ TwoPrimeGenuineHilbert =>
        T (secondPrimeGenuineAxis 1) (1 : Fin 2)) hop
    ext i
    fin_cases i
    · simpa [complexifiedAlignedGreenLimitOperator,
        firstPrimeGenuineAxis, twoPrimeGenuineVector] using
          hzero
    · simpa [complexifiedAlignedGreenLimitOperator,
        secondPrimeGenuineAxis, twoPrimeGenuineVector] using
          hone
  · intro hvector
    have hzero := congrArg
      (fun v : TwoPrimeGreenHilbert => v (0 : Fin 2)) hvector
    have hone := congrArg
      (fun v : TwoPrimeGreenHilbert => v (1 : Fin 2)) hvector
    ext v i
    fin_cases i <;>
      simp [complexifiedAlignedGreenLimitOperator, hzero, hone]

/-- O canal Green complexificado zera exatamente quando o deslocamento
critico zera. -/
theorem complexifiedAlignedGreenLimitOperator_eq_zero_iff_criticalDisplacement_eq_zero
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    complexifiedAlignedGreenLimitOperator p q s = 0 ↔
      criticalDisplacement s.re = 0 := by
  rw [complexifiedAlignedGreenLimitOperator_eq_zero_iff_limitVector_eq_zero,
    crossPrimeAlignedGreenLimitVector_eq_zero_iff_criticalDisplacement_eq_zero
      p q hp hq hs]

/-!
## Soma direta dos canais Genuine e Green
-/

/-- Espaco complexo completado: um bloco para as cameras Genuine e outro para
a complexificacao das cameras Green. -/
abbrev GenuineGreenCompletedSpace :=
  TwoPrimeGenuineHilbert × TwoPrimeGenuineHilbert

/-- Operador finito que preserva separadamente o readout Genuine e o fluxo
Green alinhado. -/
def finiteGenuineGreenCompletedOperator
    (p q L : ℕ) (s : ℂ) : Module.End ℂ GenuineGreenCompletedSpace :=
  (finiteAlignedOrthogonalGenuineOperator p q L s).prodMap
    (finiteComplexifiedAlignedGreenFluxOperator p q L s)

/-- Operador-limite em soma direta dos canais Genuine e Green. -/
def genuineGreenCompletedLimitOperator
    (p q : ℕ) (s : ℂ) : Module.End ℂ GenuineGreenCompletedSpace :=
  (orthogonalGenuineLimitOperator s).prodMap
    (complexifiedAlignedGreenLimitOperator p q s)

/-- Um bloco diagonal sobre uma soma direta e zero exatamente quando cada
bloco e zero. -/
theorem linearMap_prodMap_eq_zero_iff
    {M N : Type*}
    [AddCommMonoid M] [Module ℂ M]
    [AddCommMonoid N] [Module ℂ N]
    (A : Module.End ℂ M) (B : Module.End ℂ N) :
    A.prodMap B = 0 ↔ A = 0 ∧ B = 0 := by
  constructor
  · intro hprod
    constructor
    · apply LinearMap.ext
      intro v
      have h := congrArg (fun T : Module.End ℂ (M × N) => (T (v, 0)).1) hprod
      simpa using h
    · apply LinearMap.ext
      intro v
      have h := congrArg (fun T : Module.End ℂ (M × N) => (T (0, v)).2) hprod
      simpa using h
  · rintro ⟨rfl, rfl⟩
    exact LinearMap.prodMap_zero

/-- O operador completado e zero exatamente quando seus dois canais sao
zero. -/
theorem genuineGreenCompletedLimitOperator_eq_zero_iff_components
    (p q : ℕ) (s : ℂ) :
    genuineGreenCompletedLimitOperator p q s = 0 ↔
      orthogonalGenuineLimitOperator s = 0 ∧
        complexifiedAlignedGreenLimitOperator p q s = 0 := by
  exact linearMap_prodMap_eq_zero_iff _ _

/-- Caracterizacao intrinseca do kernel do operador completado. -/
theorem genuineGreenCompletedLimitOperator_eq_zero_iff
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    genuineGreenCompletedLimitOperator p q s = 0 ↔
      genuineContinuation s = 0 ∧ criticalDisplacement s.re = 0 := by
  rw [genuineGreenCompletedLimitOperator_eq_zero_iff_components,
    orthogonalGenuineLimitOperator_eq_zero_iff,
    complexifiedAlignedGreenLimitOperator_eq_zero_iff_criticalDisplacement_eq_zero
      p q hp hq hs]

/-- A condicao transversal pode ser escrita sem coordenada escolhida: a
amplitude da primeira camada coincide com a razao vertical do carry. -/
theorem genuineGreenCompletedLimitOperator_eq_zero_iff_carryAmplitude
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    genuineGreenCompletedLimitOperator p q s = 0 ↔
      genuineContinuation s = 0 ∧
        branchAmplitude p s.re 1 = primeCarryAmplitudeRatio p := by
  rw [genuineGreenCompletedLimitOperator_eq_zero_iff p q hp hq hs]
  constructor
  · rintro ⟨hzero, hcritical⟩
    refine ⟨hzero, ?_⟩
    apply (branchAmplitude_one_eq_primeCarryAmplitudeRatio_iff p hp s.re).2
    unfold criticalDisplacement at hcritical
    linarith
  · rintro ⟨hzero, hamplitude⟩
    refine ⟨hzero, ?_⟩
    have hre :=
      (branchAmplitude_one_eq_primeCarryAmplitudeRatio_iff p hp s.re).1
        hamplitude
    unfold criticalDisplacement
    linarith

/-- Forma coordenada da mesma caracterizacao. -/
theorem genuineGreenCompletedLimitOperator_eq_zero_iff_re_eq_half
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    genuineGreenCompletedLimitOperator p q s = 0 ↔
      genuineContinuation s = 0 ∧ s.re = (1 : ℝ) / 2 := by
  rw [genuineGreenCompletedLimitOperator_eq_zero_iff p q hp hq hs]
  constructor <;> rintro ⟨hzero, hcritical⟩
  · refine ⟨hzero, ?_⟩
    unfold criticalDisplacement at hcritical
    linarith
  · refine ⟨hzero, ?_⟩
    unfold criticalDisplacement
    linarith

/-- Fora da meia abscissa, o operador completado nao pode ser zero. -/
theorem genuineGreenCompletedLimitOperator_ne_zero_of_re_ne_half
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    genuineGreenCompletedLimitOperator p q s ≠ 0 := by
  intro hzero
  exact hoff
    ((genuineGreenCompletedLimitOperator_eq_zero_iff_re_eq_half
      p q hp hq hs).1 hzero).2

/-- Em particular, mesmo se o canal Genuine escalar zerar fora da meia
abscissa, o operador completado permanece nao nulo pelo canal Green. -/
theorem genuine_zero_has_nonzero_completed_limitOperator_of_re_ne_half
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (_hzero : genuineContinuation s = 0)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    genuineGreenCompletedLimitOperator p q s ≠ 0 :=
  genuineGreenCompletedLimitOperator_ne_zero_of_re_ne_half
    p q hp hq hs hoff

/-!
## Proveniencia finita e restricao real-espectral
-/

/-- Num zero Genuine, o operador Green finito complexificado converge
fortemente para o bloco Green explicito. -/
theorem finiteComplexifiedAlignedGreenFluxOperator_tendsto_apply_of_genuine_zero
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (v : TwoPrimeGenuineHilbert) :
    Tendsto
      (fun L : ℕ => finiteComplexifiedAlignedGreenFluxOperator p q L s v)
      atTop
      (nhds (complexifiedAlignedGreenLimitOperator p q s v)) := by
  have hvector :=
    crossPrimeAlignedGreenFluxVector_tendsto_limit_of_genuine_zero
      p q hp hq hs hzero
  have hzeroCoordinate :
      Tendsto
        (fun L : ℕ =>
          crossPrimeAlignedGreenFluxVector p q L s (0 : Fin 2))
        atTop
        (nhds (crossPrimeAlignedGreenLimitVector p q s (0 : Fin 2))) :=
    (PiLp.continuous_apply (p := 2)
      (β := fun _ : Fin 2 => ℝ) (0 : Fin 2)).continuousAt.tendsto.comp hvector
  have honeCoordinate :
      Tendsto
        (fun L : ℕ =>
          crossPrimeAlignedGreenFluxVector p q L s (1 : Fin 2))
        atTop
        (nhds (crossPrimeAlignedGreenLimitVector p q s (1 : Fin 2))) :=
    (PiLp.continuous_apply (p := 2)
      (β := fun _ : Fin 2 => ℝ) (1 : Fin 2)).continuousAt.tendsto.comp hvector
  have hzeroAction := hzeroCoordinate.ofReal.mul_const (v (0 : Fin 2))
  have honeAction := honeCoordinate.ofReal.mul_const (v (1 : Fin 2))
  simpa [finiteComplexifiedAlignedGreenFluxOperator,
    complexifiedAlignedGreenLimitOperator,
    twoPrimeGenuineDiagonalOperator] using
      (twoPrimeGenuineVector_tendsto hzeroAction honeAction)

/-- No locus de zero Genuine, o operador finito completado converge
fortemente para o operador em soma direta definido acima. -/
theorem finiteGenuineGreenCompletedOperator_tendsto_apply_of_genuine_zero
    (p q : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (v : GenuineGreenCompletedSpace) :
    Tendsto
      (fun L : ℕ => finiteGenuineGreenCompletedOperator p q L s v)
      atTop
      (nhds (genuineGreenCompletedLimitOperator p q s v)) := by
  have hgenuine :=
    finiteAlignedOrthogonalGenuineOperator_tendsto_apply
      p q hp hpodd hq hqodd hs v.1
  have hgreen :=
    finiteComplexifiedAlignedGreenFluxOperator_tendsto_apply_of_genuine_zero
      p q hp hq hs hzero v.2
  simpa [finiteGenuineGreenCompletedOperator,
    genuineGreenCompletedLimitOperator] using
      hgenuine.prodMk_nhds hgreen

/-- Na orbita real-espectral, o canal Green ja esta equilibrado por
construcao; o kernel completado reduz exatamente ao Genuine real-espectral. -/
theorem genuineGreenCompletedLimitOperator_criticalLine_eq_zero_iff
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (t : ℝ) :
    genuineGreenCompletedLimitOperator p q (criticalLineParameter t) = 0 ↔
      realSpectralGenuine t = 0 := by
  rw [genuineGreenCompletedLimitOperator_eq_zero_iff
    p q hp hq (criticalLineParameter_mem_genuineCriticalStrip t)]
  simp [realSpectralGenuine, criticalDisplacement]

end

end CPFormal.Analytic.Cp
