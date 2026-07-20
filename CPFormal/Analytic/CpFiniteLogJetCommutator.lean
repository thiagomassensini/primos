import CPFormal.Analytic.CpFiniteGreenRadial
import CPFormal.Analytic.CpAngularPort

/-!
# Comutador log-jet finito do bloco Cp

Este arquivo compara duas operacoes construidas independentemente:

* aplicar o bloco Cp ao campo de Dirichlet log-pesado;
* aplicar o autovalor Cp ao gradiente log-jet horizontal.

A regra do produto para `log (p * n)` deixa um unico canal adicional,

`log(p) * p^(-s) * G_s`.

Em particular, o comutador e colinear com o gradiente ordinario em cada
aresta. Sua soma em um cutoff finito telescopa a um bordo literal. Nenhum
defeito do checkpoint anterior e identificado com esse bordo neste modulo.
-/

open scoped BigOperators

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Monomio natural vestido pelo gerador logaritmico. -/
def natLogDirichletTerm (s : ℂ) (n : ℕ) : ℂ :=
  (Real.log (n : ℝ) : ℂ) * natDirichletTerm s n

/-- O campo positivo log-pesado e o mesmo monomio no indice deslocado. -/
theorem positiveLogDirichletValue_eq_natLogDirichletTerm
    (s : ℂ) (n : ℕ) :
    positiveLogDirichletValue s n =
      natLogDirichletTerm s (n + 1) := by
  unfold positiveLogDirichletValue natLogDirichletTerm
  rw [positiveDirichletValue_eq_natDirichletTerm]

/-!
Regra de Leibniz multiplicativa finita. As hipoteses de nao nulidade sao
somente as exigidas pela identidade real `log (a*b) = log a + log b`.
-/
theorem natLogDirichletTerm_mul
    (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (s : ℂ) :
    natLogDirichletTerm s (a * b) =
      natDirichletTerm s a * natLogDirichletTerm s b +
        (Real.log (a : ℝ) : ℂ) *
          natDirichletTerm s a * natDirichletTerm s b := by
  have haReal : (a : ℝ) ≠ 0 := by
    exact_mod_cast ha
  have hbReal : (b : ℝ) ≠ 0 := by
    exact_mod_cast hb
  unfold natLogDirichletTerm
  rw [Nat.cast_mul, Real.log_mul haReal hbReal,
    natDirichletTerm_mul]
  push_cast
  ring

/--
Soma dos `p` gradientes log-pesados no bloco que comeca em `p(n+1)`.
A definicao e independente do comutador que sera formado abaixo.
-/
def cpLogBlockGradient (p : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  ∑ r ∈ Finset.range p,
    (natLogDirichletTerm s (p * (n + 1) + r + 1) -
      natLogDirichletTerm s (p * (n + 1) + r))

/-- Coeficiente primo-local produzido pelo gerador de escala. -/
def cpLogScaleCoefficient (p : ℕ) (s : ℂ) : ℂ :=
  (Real.log (p : ℝ) : ℂ) * natDirichletTerm s p

/-!
Forma fechada do bloco log-jet. O primeiro termo e o autovalor Cp aplicado
ao log-jet horizontal; o segundo e o novo canal radial aplicado ao gradiente
ordinario.
-/
theorem cpLogBlockGradient_eq_eigenvalue_mul_logJet_add_logScale
    (p : ℕ) (hp : p ≠ 0) (s : ℂ) (n : ℕ) :
    cpLogBlockGradient p s n =
      natDirichletTerm s p * positiveLogDirichletGradient s n +
        cpLogScaleCoefficient p s * positiveDirichletGradient s n := by
  unfold cpLogBlockGradient
  rw [sum_range_forwardDifference]
  have hend : p * (n + 1) + p = p * (n + 2) := by
    ring
  rw [hend,
    natLogDirichletTerm_mul p (n + 2) hp (by omega) s,
    natLogDirichletTerm_mul p (n + 1) hp (by omega) s]
  rw [← positiveLogDirichletValue_eq_natLogDirichletTerm s (n + 1),
    ← positiveLogDirichletValue_eq_natLogDirichletTerm s n,
    ← positiveDirichletValue_eq_natDirichletTerm s (n + 1),
    ← positiveDirichletValue_eq_natDirichletTerm s n]
  unfold positiveLogDirichletGradient positiveDirichletGradient
    cpLogScaleCoefficient
  ring

/-- Diferenca entre transportar o log-jet pelo bloco e pelo autovalor Cp. -/
def cpLogJetCommutator (p : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  cpLogBlockGradient p s n -
    natDirichletTerm s p * positiveLogDirichletGradient s n

/-- O comutador inteiro e exatamente o canal radial vezes o gradiente. -/
theorem cpLogJetCommutator_eq_logScale_mul_gradient
    (p : ℕ) (hp : p ≠ 0) (s : ℂ) (n : ℕ) :
    cpLogJetCommutator p s n =
      cpLogScaleCoefficient p s * positiveDirichletGradient s n := by
  unfold cpLogJetCommutator
  rw [cpLogBlockGradient_eq_eigenvalue_mul_logJet_add_logScale p hp]
  ring

/-!
Identidade anunciada no checkpoint 0.30. A primalidade nao participa da
algebra local alem de garantir `p != 0`; ela tipa o coeficiente como o canal
de uma camera prima.
-/
theorem cpPrimeLogJetCommutator_identity
    (p : ℕ) (hp : Nat.Prime p) (s : ℂ) (n : ℕ) :
    cpLogBlockGradient p s n -
        natDirichletTerm s p * positiveLogDirichletGradient s n =
      (Real.log (p : ℝ) : ℂ) * natDirichletTerm s p *
        positiveDirichletGradient s n := by
  simpa [cpLogJetCommutator, cpLogScaleCoefficient] using
    (cpLogJetCommutator_eq_logScale_mul_gradient p hp.ne_zero s n)

/-- O mesmo comutador depois de retirar a fase da camera prima. -/
def phaseNormalizedCpLogJetCommutator
    (p : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  cpPhaseNormalizer p s * cpLogJetCommutator p s n

/-!
Depois da normalizacao radial, o coeficiente e real salvo pelo fator real
`log p`: `log(p) * p^(-delta)`, onde `delta = Re(s)-1/2`.
-/
theorem phaseNormalizedCpLogJetCommutator_eq_radial_logScale
    (p : ℕ) (hp : Nat.Prime p) (s : ℂ) (n : ℕ) :
    phaseNormalizedCpLogJetCommutator p s n =
      (Real.log (p : ℝ) : ℂ) *
        (((p : ℝ) ^ (-criticalDisplacement s.re) : ℝ) : ℂ) *
          positiveDirichletGradient s n := by
  unfold phaseNormalizedCpLogJetCommutator
  rw [cpLogJetCommutator_eq_logScale_mul_gradient p hp.ne_zero]
  unfold cpLogScaleCoefficient
  calc
    cpPhaseNormalizer p s *
          ((Real.log (p : ℝ) : ℂ) * natDirichletTerm s p *
            positiveDirichletGradient s n) =
        (Real.log (p : ℝ) : ℂ) *
          (cpPhaseNormalizer p s * natDirichletTerm s p) *
            positiveDirichletGradient s n := by ring
    _ = (Real.log (p : ℝ) : ℂ) *
          (((p : ℝ) ^ (-criticalDisplacement s.re) : ℝ) : ℂ) *
            positiveDirichletGradient s n := by
      rw [cpPhaseNormalizer_mul_eigenvalue p hp s]

/-- Soma do comutador nas primeiras `M` arestas horizontais. -/
def finiteCpLogJetCommutator (p M : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range M, cpLogJetCommutator p s n

/-!
O canal do comutador e um cobordo genuino em cutoff finito: sua soma e o
coeficiente primo-local vezes endpoint externo menos endpoint interno.
-/
theorem finiteCpLogJetCommutator_eq_boundary
    (p M : ℕ) (hp : p ≠ 0) (s : ℂ) :
    finiteCpLogJetCommutator p M s =
      cpLogScaleCoefficient p s *
        (positiveDirichletValue s M - positiveDirichletValue s 0) := by
  unfold finiteCpLogJetCommutator
  simp_rw [cpLogJetCommutator_eq_logScale_mul_gradient p hp s]
  rw [← Finset.mul_sum]
  have htelescoping :
      (∑ n ∈ Finset.range M, positiveDirichletGradient s n) =
        positiveDirichletValue s M - positiveDirichletValue s 0 := by
    rw [positiveDirichletValue_eq_natDirichletTerm,
      positiveDirichletValue_eq_natDirichletTerm]
    simpa [positiveDirichletGradient, Nat.add_assoc] using
      (sum_range_forwardDifference
        (fun k : ℕ ↦ natDirichletTerm s (k + 1)) 0 M)
  rw [htelescoping]

end

end CPFormal.Analytic.Cp
