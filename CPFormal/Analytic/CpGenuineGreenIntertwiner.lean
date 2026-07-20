import CPFormal.Analytic.CpFinitePortWronskian
import CPFormal.Genuine.CpFiniteChart

/-!
# Intertwiner exato entre o bracket Genuine e o Green Cp

O `cpBlockGradient` nao e um segundo operador aritmetico. Ele e a realizacao
no espaco de gradientes da identidade local ja certificada

`bracket = centerBlock - p * center`.

Este modulo diferencia essa identidade entre dois centros Cp consecutivos.
O resultado e universal: vale para qualquer funcao com valores num anel
comutativo, antes de escolher monomios de Dirichlet, zeros, limites ou uma
normalizacao espectral. Depois especializamos ao campo `dirichletTerm` e
provamos que o Wronskiano usado pelo Green atual e exatamente a forma de
Green do residual Genuine, salvo o fator escalar nao nulo `p`.
-/

open scoped BigOperators

namespace CPFormal.Analytic.Cp

noncomputable section

open CPFormal.Genuine.Cp

variable {R : Type*} [CommRing R]

/-- Diferenca de uma funcao entre dois centros Cp consecutivos. -/
def cpAlignedCenterGradient
    (p : ℕ) (f : ℤ → R) (n : ℕ) : R :=
  f (alignedCenter p (n + 1)) - f (alignedCenter p n)

/-- Diferenca dos blocos completos entre dois centros Cp consecutivos. -/
def cpCenterBlockGradient
    (p : ℕ) (f : ℤ → R) (n : ℕ) : R :=
  centerBlock p f (alignedCenter p (n + 1)) -
    centerBlock p f (alignedCenter p n)

/-- Diferenca dos brackets Genuine entre dois centros Cp consecutivos. -/
def cpGenuineBracketGradient
    (p : ℕ) (f : ℤ → R) (n : ℕ) : R :=
  bracket p f (alignedCenter p (n + 1)) -
    bracket p f (alignedCenter p n)

/--
Residual Genuine diferenciado. Esta e a expressao CP--Green antes de dividir
pelo tamanho do bloco.
-/
def cpGenuineResolvedGradient
    (p : ℕ) (f : ℤ → R) (n : ℕ) : R :=
  cpCenterBlockGradient p f n - cpGenuineBracketGradient p f n

/--
Intertwiner universal CP--Genuine--Green. Diferenciar a identidade local do
bracket deixa exatamente `p` copias do gradiente da coluna central.
-/
theorem cpGenuineResolvedGradient_eq_p_mul_alignedCenterGradient
    (p : ℕ) (hp : Nat.Prime p) (f : ℤ → R) (n : ℕ) :
    cpGenuineResolvedGradient p f n =
      (p : R) * cpAlignedCenterGradient p f n := by
  unfold cpGenuineResolvedGradient cpCenterBlockGradient
    cpGenuineBracketGradient cpAlignedCenterGradient
  rw [bracket_eq_centerBlock_sub_p_mul_center p hp,
    bracket_eq_centerBlock_sub_p_mul_center p hp]
  ring

/--
A soma telescopica chamada `cpBlockGradient` e literalmente o gradiente dos
centros alinhados da mesma funcao de Dirichlet.
-/
theorem cpBlockGradient_eq_alignedCenterGradient
    (p : ℕ) (s : ℂ) (n : ℕ) :
    cpBlockGradient p s n =
      cpAlignedCenterGradient p (dirichletTerm s) n := by
  unfold cpBlockGradient
  rw [sum_range_forwardDifference]
  unfold cpAlignedCenterGradient alignedCenter natDirichletTerm
  congr 1

/--
Especializacao central: o gradiente resolvido do bracket Genuine e exatamente
`p * cpBlockGradient`. Logo o bloco usado pelo Green nao introduz um novo
operador; ele e a representacao diferenciada do operador Genuine.
-/
theorem cpGenuineResolvedGradient_dirichlet_eq_p_mul_cpBlockGradient
    (p : ℕ) (hp : Nat.Prime p) (s : ℂ) (n : ℕ) :
    cpGenuineResolvedGradient p (dirichletTerm s) n =
      (p : ℂ) * cpBlockGradient p s n := by
  rw [cpGenuineResolvedGradient_eq_p_mul_alignedCenterGradient p hp]
  rw [← cpBlockGradient_eq_alignedCenterGradient]

/--
Gradiente Green na normalizacao natural da camera: resolver o residual
Genuine e dividir pelo numero `p` de valores do bloco.
-/
def cpGenuineGreenGradient
    (p : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  (p : ℂ)⁻¹ * cpGenuineResolvedGradient p (dirichletTerm s) n

/--
Identificacao coordenada a coordenada, sem fator restante: o gradiente que
entra no Green e o residual Genuine diferenciado e normalizado.
-/
theorem cpGenuineGreenGradient_eq_cpBlockGradient
    (p : ℕ) (hp : Nat.Prime p) (s : ℂ) (n : ℕ) :
    cpGenuineGreenGradient p s n = cpBlockGradient p s n := by
  unfold cpGenuineGreenGradient
  rw [cpGenuineResolvedGradient_dirichlet_eq_p_mul_cpBlockGradient p hp]
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  simp [hp0]

/-!
## Forma de Green resolvida pelo Genuine
-/

/--
Wronskiano finito escrito diretamente com o residual Genuine diferenciado.
Ele e definido independentemente de `finiteCpGreenFlux`.
-/
def finiteGenuineResolvedCpGreenFlux
    (p M : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range M,
    ((starRingEnd ℂ)
          (cpGenuineResolvedGradient p (dirichletTerm s) n) *
        positiveDirichletGradient (reflectedParameter s) n -
      (starRingEnd ℂ) (positiveDirichletGradient s n) *
        cpGenuineResolvedGradient p
          (dirichletTerm (reflectedParameter s)) n)

/--
Identidade finita do Green correto: a forma resolvida Genuine e `p` vezes o
fluxo Cp anterior. O fator e real, positivo e nao cria nem remove zeros.
-/
theorem finiteGenuineResolvedCpGreenFlux_eq_p_mul_finiteCpGreenFlux
    (p M : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    finiteGenuineResolvedCpGreenFlux p M s =
      (p : ℂ) * finiteCpGreenFlux p M s := by
  unfold finiteGenuineResolvedCpGreenFlux finiteCpGreenFlux
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [cpGenuineResolvedGradient_dirichlet_eq_p_mul_cpBlockGradient p hp,
    cpGenuineResolvedGradient_dirichlet_eq_p_mul_cpBlockGradient p hp]
  simp only [map_mul, Complex.conj_natCast]
  ring

/-- O Green anterior e nulo exatamente quando a forma Green Genuine e nula. -/
theorem finiteGenuineResolvedCpGreenFlux_eq_zero_iff
    (p M : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    finiteGenuineResolvedCpGreenFlux p M s = 0 ↔
      finiteCpGreenFlux p M s = 0 := by
  rw [finiteGenuineResolvedCpGreenFlux_eq_p_mul_finiteCpGreenFlux p M hp]
  exact mul_eq_zero_iff_left (by exact_mod_cast hp.ne_zero)

/-- Forma Green construida diretamente com o gradiente Genuine normalizado. -/
def finiteGenuineCpGreenFlux
    (p M : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range M,
    ((starRingEnd ℂ) (cpGenuineGreenGradient p s n) *
        positiveDirichletGradient (reflectedParameter s) n -
      (starRingEnd ℂ) (positiveDirichletGradient s n) *
        cpGenuineGreenGradient p (reflectedParameter s) n)

/--
O `finiteCpGreenFlux` existente e literalmente a forma Green Genuine depois
da normalizacao canonica por `p`; nao ha um segundo operador.
-/
theorem finiteGenuineCpGreenFlux_eq_finiteCpGreenFlux
    (p M : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    finiteGenuineCpGreenFlux p M s = finiteCpGreenFlux p M s := by
  unfold finiteGenuineCpGreenFlux finiteCpGreenFlux
  apply Finset.sum_congr rfl
  intro n hn
  rw [cpGenuineGreenGradient_eq_cpBlockGradient p hp,
    cpGenuineGreenGradient_eq_cpBlockGradient p hp]

/-!
## Compatibilidade com a normalizacao radial usada pela TFVD
-/

/-- Residual Genuine diferenciado depois da mesma normalizacao de fase. -/
def phaseNormalizedCpGenuineResolvedGradient
    (p : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  cpPhaseNormalizer p s *
    cpGenuineResolvedGradient p (dirichletTerm s) n

/-- A normalizacao radial comuta exatamente com o intertwiner Genuine. -/
theorem phaseNormalizedCpGenuineResolvedGradient_eq_p_mul
    (p : ℕ) (hp : Nat.Prime p) (s : ℂ) (n : ℕ) :
    phaseNormalizedCpGenuineResolvedGradient p s n =
      (p : ℂ) * phaseNormalizedCpBlockGradient p s n := by
  unfold phaseNormalizedCpGenuineResolvedGradient
    phaseNormalizedCpBlockGradient
  rw [cpGenuineResolvedGradient_dirichlet_eq_p_mul_cpBlockGradient p hp]
  ring

/-- Wronskiano radial escrito com o residual Genuine diferenciado. -/
def finitePhaseNormalizedGenuineResolvedCpGreenFlux
    (p M : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range M,
    ((starRingEnd ℂ)
          (phaseNormalizedCpGenuineResolvedGradient p s n) *
        positiveDirichletGradient (reflectedParameter s) n -
      (starRingEnd ℂ) (positiveDirichletGradient s n) *
        phaseNormalizedCpGenuineResolvedGradient p
          (reflectedParameter s) n)

/-- A forma radial Genuine e `p` vezes a forma radial usada anteriormente. -/
theorem finitePhaseNormalizedGenuineResolvedCpGreenFlux_eq_p_mul
    (p M : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    finitePhaseNormalizedGenuineResolvedCpGreenFlux p M s =
      (p : ℂ) * finitePhaseNormalizedCpGreenFlux p M s := by
  unfold finitePhaseNormalizedGenuineResolvedCpGreenFlux
    finitePhaseNormalizedCpGreenFlux
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [phaseNormalizedCpGenuineResolvedGradient_eq_p_mul p hp,
    phaseNormalizedCpGenuineResolvedGradient_eq_p_mul p hp]
  simp only [map_mul, Complex.conj_natCast]
  ring

/-- Convencao orientada da forma Green Genuine. -/
def finiteOrientedGenuineResolvedCpGreenFlux
    (p M : ℕ) (s : ℂ) : ℂ :=
  -finitePhaseNormalizedGenuineResolvedCpGreenFlux p M s

/--
O fluxo orientado identificado pela TFVD e o fluxo Genuine resolvido, apenas
normalizado pelo tamanho nao nulo do bloco.
-/
theorem finiteOrientedGenuineResolvedCpGreenFlux_eq_p_mul
    (p M : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    finiteOrientedGenuineResolvedCpGreenFlux p M s =
      (p : ℂ) * finiteOrientedCpGreenFlux p M s := by
  unfold finiteOrientedGenuineResolvedCpGreenFlux finiteOrientedCpGreenFlux
  rw [finitePhaseNormalizedGenuineResolvedCpGreenFlux_eq_p_mul p M hp]
  ring

/-- Gradiente Genuine normalizado depois da normalizacao radial de fase. -/
def phaseNormalizedCpGenuineGreenGradient
    (p : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  cpPhaseNormalizer p s * cpGenuineGreenGradient p s n

/-- A identificacao Genuine--Green comuta com a normalizacao radial. -/
theorem phaseNormalizedCpGenuineGreenGradient_eq_phaseNormalizedCpBlockGradient
    (p : ℕ) (hp : Nat.Prime p) (s : ℂ) (n : ℕ) :
    phaseNormalizedCpGenuineGreenGradient p s n =
      phaseNormalizedCpBlockGradient p s n := by
  unfold phaseNormalizedCpGenuineGreenGradient
    phaseNormalizedCpBlockGradient
  rw [cpGenuineGreenGradient_eq_cpBlockGradient p hp]

/-- Forma radial construida com o gradiente Genuine normalizado. -/
def finitePhaseNormalizedGenuineCpGreenFlux
    (p M : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range M,
    ((starRingEnd ℂ)
          (phaseNormalizedCpGenuineGreenGradient p s n) *
        positiveDirichletGradient (reflectedParameter s) n -
      (starRingEnd ℂ) (positiveDirichletGradient s n) *
        phaseNormalizedCpGenuineGreenGradient p
          (reflectedParameter s) n)

/-- A forma radial Genuine e exatamente a forma radial anterior. -/
theorem finitePhaseNormalizedGenuineCpGreenFlux_eq_finitePhaseNormalizedCpGreenFlux
    (p M : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    finitePhaseNormalizedGenuineCpGreenFlux p M s =
      finitePhaseNormalizedCpGreenFlux p M s := by
  unfold finitePhaseNormalizedGenuineCpGreenFlux
    finitePhaseNormalizedCpGreenFlux
  apply Finset.sum_congr rfl
  intro n hn
  rw [phaseNormalizedCpGenuineGreenGradient_eq_phaseNormalizedCpBlockGradient
      p hp,
    phaseNormalizedCpGenuineGreenGradient_eq_phaseNormalizedCpBlockGradient
      p hp]

/-- Convencao orientada, agora escrita somente com o operador Genuine. -/
def finiteOrientedGenuineCpGreenFlux
    (p M : ℕ) (s : ℂ) : ℂ :=
  -finitePhaseNormalizedGenuineCpGreenFlux p M s

/-- O fluxo orientado existente e literalmente o fluxo orientado Genuine. -/
theorem finiteOrientedGenuineCpGreenFlux_eq_finiteOrientedCpGreenFlux
    (p M : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    finiteOrientedGenuineCpGreenFlux p M s =
      finiteOrientedCpGreenFlux p M s := by
  unfold finiteOrientedGenuineCpGreenFlux finiteOrientedCpGreenFlux
  rw [finitePhaseNormalizedGenuineCpGreenFlux_eq_finitePhaseNormalizedCpGreenFlux
    p M hp]

/--
A diagonal TFVD e exatamente o Green Genuine normalizado, bloco por bloco.
-/
theorem finiteOrientedGenuineCpGreenFlux_eq_tfvdDiagonal
    (p M : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    finiteOrientedGenuineCpGreenFlux p M s =
      finiteTfvdCpGreenDiagonal p M s := by
  rw [finiteOrientedGenuineCpGreenFlux_eq_finiteOrientedCpGreenFlux p M hp,
    finiteTfvdCpGreenDiagonal_eq_finiteOrientedCpGreenFlux]

/--
O fluxo Green acoplado ao bordo bracketado tambem usa essa mesma forma
Genuine; o unico termo adicional e o bordo independente ja certificado.
-/
theorem finiteBracketCoupledCpGreenFlux_eq_genuineOriented_add_boundary
    (p M : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    finiteBracketCoupledCpGreenFlux p M s =
      (finiteOrientedGenuineCpGreenFlux p M s).re +
        finiteBracketCoupledSignedBoundary M s := by
  rw [finiteOrientedGenuineCpGreenFlux_eq_finiteOrientedCpGreenFlux p M hp]
  exact finiteBracketCoupledCpGreenFlux_eq_oriented_add_boundary p M s

/--
Composicao final com a TFVD: a diagonal preservada bloco a bloco e a forma
Green Genuine resolvida diferem somente pelo fator de bloco `p`. Assim os
checkpoints TFVD anteriores vivem na mesma cadeia Genuine-first.
-/
theorem finiteOrientedGenuineResolvedCpGreenFlux_eq_p_mul_tfvdDiagonal
    (p M : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    finiteOrientedGenuineResolvedCpGreenFlux p M s =
      (p : ℂ) * finiteTfvdCpGreenDiagonal p M s := by
  rw [finiteOrientedGenuineResolvedCpGreenFlux_eq_p_mul p M hp,
    finiteTfvdCpGreenDiagonal_eq_finiteOrientedCpGreenFlux]

end

end CPFormal.Analytic.Cp
