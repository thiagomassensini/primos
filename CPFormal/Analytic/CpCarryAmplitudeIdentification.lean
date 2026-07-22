import CPFormal.Analytic.CpCarryWeightedVerticalGreen
import CPFormal.Carry.CpBranchWeight

/-!
# Identificacao da razao vertical com a amplitude critica do carry

A valvula vertical ponderada usa a razao

`q_p = (sqrt p)⁻¹`.

Este modulo prova que essa razao nao e uma calibracao externa: ela e
literalmente a amplitude critica da primeira camada do carry,
`criticalAmplitude p 1 = p^(-1/2)`. Para uma base prima, uma amplitude de
ramo coincide com essa razao exatamente em `sigma = 1/2`.

As tres identidades abaixo pertenciam a um antigo modulo de gate global.
Elas sao restauradas aqui separadamente porque sao fatos fundacionais e nao
dependem de qualquer afirmacao sobre zeros Genuine.
-/

namespace CPFormal.Analytic.Cp

open CPFormal.Carry.Cp

noncomputable section

/-- A razao usada pela valvula vertical e exatamente a amplitude critica da
primeira camada do carry. -/
theorem primeCarryAmplitudeRatio_eq_criticalAmplitude_one
    (p : ℕ) :
    primeCarryAmplitudeRatio p = criticalAmplitude p 1 := by
  have hpnonneg : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have hratioSq :
      (primeCarryAmplitudeRatio p) ^ 2 = (p : ℝ)⁻¹ := by
    unfold primeCarryAmplitudeRatio
    rw [inv_pow, Real.sq_sqrt hpnonneg]
  have hcriticalSq :
      (criticalAmplitude p 1) ^ 2 = (p : ℝ)⁻¹ := by
    rw [criticalAmplitude_sq_eq_mass]
    simp [criticalMass, Real.rpow_neg_one]
  have hratioNonneg : 0 ≤ primeCarryAmplitudeRatio p :=
    primeCarryAmplitudeRatio_nonneg p
  have hcriticalNonneg : 0 ≤ criticalAmplitude p 1 :=
    criticalAmplitude_nonneg p 1
  nlinarith

/-- Numa base prima, coincidir com a amplitude critica ja na primeira camada
equivale a `sigma = 1/2`. -/
theorem branchAmplitude_one_eq_criticalAmplitude_one_iff
    (p : ℕ) (hp : Nat.Prime p) (sigma : ℝ) :
    branchAmplitude p sigma 1 = criticalAmplitude p 1 ↔
      sigma = (1 : ℝ) / 2 := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast hp.ne_one
  constructor
  · intro hamplitude
    unfold branchAmplitude criticalAmplitude at hamplitude
    have hexponent := (Real.rpow_right_inj hp0 hp1).mp hamplitude
    norm_num at hexponent
    linarith
  · intro hsigma
    subst sigma
    exact branchAmplitude_half p 1

/-- A mesma rigidez escrita diretamente com a razao `q_p` usada no Green,
no bracket, no traco e no retorno verticais. -/
theorem branchAmplitude_one_eq_primeCarryAmplitudeRatio_iff
    (p : ℕ) (hp : Nat.Prime p) (sigma : ℝ) :
    branchAmplitude p sigma 1 = primeCarryAmplitudeRatio p ↔
      sigma = (1 : ℝ) / 2 := by
  rw [primeCarryAmplitudeRatio_eq_criticalAmplitude_one]
  exact branchAmplitude_one_eq_criticalAmplitude_one_iff p hp sigma

end

end CPFormal.Analytic.Cp
