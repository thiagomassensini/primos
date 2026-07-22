import CPFormal.Analytic.CpBranchNorm

/-!
# Tilt transversal `Cₚ` e seu locus critico

Para os offsets balanceados `Aₚ`, definimos o tilt local

`Theta_delta(c) = sum_{a in Aₚ} (c+a)^(-delta) - (p-1)c^(-delta)`.

O parametro transversal e `delta = sigma - 1/2`. Este arquivo prova, para
todo primo impar, que o tilt se anula quando `delta = 0` e que a saturacao da
norma do operador de ramo implica essa anulacao.

A reciproca exige a rigidez de sinal do tilt no dominio considerado. Ela e
isolada na proposicao `TiltRigidityAt`; nao e assumida por definicao e nenhuma
instancia global e declarada aqui.
-/

open scoped BigOperators

namespace CPFormal.Analytic.Cp

open CPFormal.Carry.Cp
open CPFormal.Genuine.Cp

noncomputable section

/-- Tilt bracketado local da camera `Cₚ` no centro real `center`. -/
def cpTilt (p : ℕ) (delta center : ℝ) : ℝ :=
  (∑ a ∈ balancedOffsets p,
      (center + (a : ℝ)) ^ (-delta)) -
    ((p - 1 : ℕ) : ℝ) * center ^ (-delta)

/-- Tilt parametrizado diretamente pela abscissa `sigma`. -/
def cpTiltAtSigma (p : ℕ) (sigma center : ℝ) : ℝ :=
  cpTilt p (criticalDisplacement sigma) center

/-- Com `delta = 0`, todas as pernas e o centro valem um e se cancelam. -/
@[simp] theorem cpTilt_zero
    (p : ℕ) (hpodd : Odd p) (center : ℝ) :
    cpTilt p 0 center = 0 := by
  classical
  simp [cpTilt, card_balancedOffsets hpodd]

/-- Toda carta prima impar aniquila o tilt na meia abscissa. -/
@[simp] theorem cpTiltAtSigma_half
    (p : ℕ) (hpodd : Odd p) (center : ℝ) :
    cpTiltAtSigma p ((1 : ℝ) / 2) center = 0 := by
  have hdelta : criticalDisplacement ((1 : ℝ) / 2) = 0 := by
    unfold criticalDisplacement
    ring
  rw [cpTiltAtSigma, hdelta]
  exact cpTilt_zero p hpodd center

/--
Ligacao direta norma--tilt: saturacao quadratica força a anulacao local do
tilt em qualquer centro.
-/
theorem branchDefect_zero_implies_cpTiltAtSigma_zero
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {sigma : ℝ} (hsigma : 0 < sigma) (center : ℝ)
    (hdefect : branchDefect p sigma = 0) :
    cpTiltAtSigma p sigma center = 0 := by
  have hdelta : criticalDisplacement sigma = 0 :=
    (branchDefect_eq_zero_iff_criticalDisplacement_eq_zero
      p hp hsigma).mp hdefect
  rw [cpTiltAtSigma, hdelta]
  exact cpTilt_zero p hpodd center

/--
Rigidez local necessaria para a volta tilt--norma: no semiplano `sigma > 0`,
o unico zero do tilt naquele centro deve ser `delta = 0`.
-/
structure TiltRigidityAt (p : ℕ) (center : ℝ) : Prop where
  zero_only :
    ∀ {sigma : ℝ}, 0 < sigma → cpTiltAtSigma p sigma center = 0 →
      criticalDisplacement sigma = 0

/-- Sob rigidez do tilt, tilt e defeito da norma possuem exatamente o mesmo zero. -/
theorem branchDefect_eq_zero_iff_cpTiltAtSigma_eq_zero
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (center : ℝ) (rigidity : TiltRigidityAt p center)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    branchDefect p sigma = 0 ↔ cpTiltAtSigma p sigma center = 0 := by
  constructor
  · exact branchDefect_zero_implies_cpTiltAtSigma_zero
      p hp hpodd hsigma center
  · intro htilt
    apply (branchDefect_eq_zero_iff_criticalDisplacement_eq_zero
      p hp hsigma).2
    exact rigidity.zero_only hsigma htilt

/-- Uma ponte Genuine--ramo tambem transporta zeros Genuine para zeros do tilt. -/
theorem cpTiltAtSigma_eq_zero_of_genuine_zero
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (genuine : ℂ → ℂ) (bridge : GenuineBranchBridge p genuine)
    {s : ℂ} (hzero : genuine s = 0) (hre : 0 < s.re)
    (center : ℝ) :
    cpTiltAtSigma p s.re center = 0 := by
  apply branchDefect_zero_implies_cpTiltAtSigma_zero
    p hp hpodd hre center
  unfold branchDefect
  exact sub_eq_zero.mpr (bridge.saturation_of_zero hzero hre)

end

end CPFormal.Analytic.Cp
