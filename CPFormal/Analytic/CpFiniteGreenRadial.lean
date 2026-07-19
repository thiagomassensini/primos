import CPFormal.Analytic.CpFiniteGreenCertificate
import CPFormal.Analytic.CpBranchNorm

/-!
# Normalizacao radial do certificado Green finito

O bloco Cp possui autovalor complexo `p^(-s)`. Antes de formar o Wronskiano,
retiramos a fase e a escala critica por

`p^(1/2 + i Im(s))`.

Para `delta = Re(s) - 1/2`, os dois parametros refletidos passam entao a ter
autovalores reais `p^(-delta)` e `p^delta`. Este arquivo prova essa afirmacao
no nivel dos blocos finitos, orienta o fluxo pelo fator

`p^delta - p^(-delta)`,

e fatora essa diferenca como `2 * delta` vezes um cofator estritamente
positivo. A passagem a parte real produz a identidade Green assinada finita.

Ainda nao usamos aqui o bracket Genuine para cancelar o endpoint interno;
essa identificacao continua sendo uma obrigacao independente de bordo.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Fator que remove simultaneamente a fase vertical e a escala critica. -/
def cpPhaseNormalizer (p : ℕ) (s : ℂ) : ℂ :=
  (p : ℂ) ^ ((1 : ℂ) / 2 + Complex.I * s.im)

/-- Bloco Cp depois da normalizacao radial, aplicada antes do Wronskiano. -/
def phaseNormalizedCpBlockGradient
    (p : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  cpPhaseNormalizer p s * cpBlockGradient p s n

@[simp] theorem reflectedParameter_re (s : ℂ) :
    (reflectedParameter s).re = 1 - s.re := by
  simp [reflectedParameter]

@[simp] theorem reflectedParameter_im (s : ℂ) :
    (reflectedParameter s).im = s.im := by
  simp [reflectedParameter]

@[simp] theorem criticalDisplacement_reflectedParameter (s : ℂ) :
    criticalDisplacement (reflectedParameter s).re =
      -criticalDisplacement s.re := by
  simp [criticalDisplacement]
  ring

/-!
O normalizador deve ser combinado com o autovalor antes da conjugacao da
forma sesquilinear. O resultado e a potencia real positiva `p^(-delta)`.
-/
theorem cpPhaseNormalizer_mul_eigenvalue
    (p : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    cpPhaseNormalizer p s * natDirichletTerm s p =
      (((p : ℝ) ^ (-criticalDisplacement s.re) : ℝ) : ℂ) := by
  have hpComplex : (p : ℂ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  have hpReal : 0 ≤ (p : ℝ) := by
    positivity
  have hexponent :
      (1 : ℂ) / 2 + Complex.I * s.im + (-s) =
        ((-criticalDisplacement s.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [criticalDisplacement] <;> ring
  unfold cpPhaseNormalizer natDirichletTerm dirichletTerm
  change
    (p : ℂ) ^ ((1 : ℂ) / 2 + Complex.I * s.im) *
        (p : ℂ) ^ (-s) =
      (((p : ℝ) ^ (-criticalDisplacement s.re) : ℝ) : ℂ)
  calc
    (p : ℂ) ^ ((1 : ℂ) / 2 + Complex.I * s.im) *
          (p : ℂ) ^ (-s) =
        (p : ℂ) ^
          ((1 : ℂ) / 2 + Complex.I * s.im + (-s)) :=
      (Complex.cpow_add _ _ hpComplex).symm
    _ = (p : ℂ) ^ ((-criticalDisplacement s.re : ℝ) : ℂ) := by
      rw [hexponent]
    _ = (((p : ℝ) ^ (-criticalDisplacement s.re) : ℝ) : ℂ) :=
      (Complex.ofReal_cpow hpReal (-criticalDisplacement s.re)).symm

/-- O bloco normalizado tem autovalor radial real `p^(-delta)`. -/
theorem phaseNormalizedCpBlockGradient_eq_radial_mul
    (p : ℕ) (hp : Nat.Prime p) (s : ℂ) (n : ℕ) :
    phaseNormalizedCpBlockGradient p s n =
      (((p : ℝ) ^ (-criticalDisplacement s.re) : ℝ) : ℂ) *
        positiveDirichletGradient s n := by
  unfold phaseNormalizedCpBlockGradient
  rw [cpBlockGradient_eq_eigenvalue_mul]
  rw [← mul_assoc, cpPhaseNormalizer_mul_eigenvalue p hp s]

/-- No parametro refletido, o autovalor radial e `p^delta`. -/
theorem phaseNormalizedCpBlockGradient_reflected_eq_radial_mul
    (p : ℕ) (hp : Nat.Prime p) (s : ℂ) (n : ℕ) :
    phaseNormalizedCpBlockGradient p (reflectedParameter s) n =
      (((p : ℝ) ^ (criticalDisplacement s.re) : ℝ) : ℂ) *
        positiveDirichletGradient (reflectedParameter s) n := by
  rw [phaseNormalizedCpBlockGradient_eq_radial_mul p hp]
  rw [criticalDisplacement_reflectedParameter]
  simp only [neg_neg]

/-- Wronskiano finito formado somente depois de retirar a fase. -/
def finitePhaseNormalizedCpGreenFlux (p M : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range M,
    ((starRingEnd ℂ) (phaseNormalizedCpBlockGradient p s n) *
        positiveDirichletGradient (reflectedParameter s) n -
      (starRingEnd ℂ) (positiveDirichletGradient s n) *
        phaseNormalizedCpBlockGradient p (reflectedParameter s) n)

/-!
Depois da normalizacao, a conjugacao da forma sesquilinear nao altera mais o
autovalor: ele e real. Por isso o coeficiente e literalmente
`p^(-delta) - p^delta`.
-/
theorem finitePhaseNormalizedCpGreenFlux_eq_radialDifference_mul_pairing
    (p M : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    finitePhaseNormalizedCpGreenFlux p M s =
      ((((p : ℝ) ^ (-criticalDisplacement s.re) -
          (p : ℝ) ^ (criticalDisplacement s.re) : ℝ) : ℂ) *
        finiteReflectedGradientPairing M s) := by
  unfold finitePhaseNormalizedCpGreenFlux finiteReflectedGradientPairing
  calc
    (∑ n ∈ Finset.range M,
      ((starRingEnd ℂ) (phaseNormalizedCpBlockGradient p s n) *
          positiveDirichletGradient (reflectedParameter s) n -
        (starRingEnd ℂ) (positiveDirichletGradient s n) *
          phaseNormalizedCpBlockGradient p (reflectedParameter s) n)) =
        ∑ n ∈ Finset.range M,
          ((((p : ℝ) ^ (-criticalDisplacement s.re) -
              (p : ℝ) ^ (criticalDisplacement s.re) : ℝ) : ℂ) *
            ((starRingEnd ℂ) (positiveDirichletGradient s n) *
              positiveDirichletGradient (reflectedParameter s) n)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [phaseNormalizedCpBlockGradient_eq_radial_mul p hp,
        phaseNormalizedCpBlockGradient_reflected_eq_radial_mul p hp]
      simp only [map_mul, map_ofReal]
      push_cast
      ring
    _ = ((((p : ℝ) ^ (-criticalDisplacement s.re) -
            (p : ℝ) ^ (criticalDisplacement s.re) : ℝ) : ℂ) *
          ∑ n ∈ Finset.range M,
            ((starRingEnd ℂ) (positiveDirichletGradient s n) *
              positiveDirichletGradient (reflectedParameter s) n)) := by
      rw [Finset.mul_sum]

/-- Diferenca radial orientada no mesmo sentido de `delta`. -/
def cpRadialDifference (p : ℕ) (delta : ℝ) : ℝ :=
  (p : ℝ) ^ delta - (p : ℝ) ^ (-delta)

/-- Cofator que prolonga continuamente o quociente radial em `delta = 0`. -/
def cpRadialCofactor (p : ℕ) (delta : ℝ) : ℝ :=
  if delta = 0 then Real.log p
  else cpRadialDifference p delta / (2 * delta)

/-- Fatoracao algebrica exata do desequilibrio radial. -/
theorem cpRadialDifference_eq_two_mul_delta_mul_cofactor
    (p : ℕ) (delta : ℝ) :
    cpRadialDifference p delta =
      2 * delta * cpRadialCofactor p delta := by
  by_cases hdelta : delta = 0
  · simp [cpRadialDifference, cpRadialCofactor, hdelta]
  · have hden : (2 : ℝ) * delta ≠ 0 := mul_ne_zero (by norm_num) hdelta
    rw [cpRadialCofactor, if_neg hdelta]
    field_simp [hden]

/-- Para uma base prima, o cofator radial e estritamente positivo. -/
theorem cpRadialCofactor_pos
    (p : ℕ) (hp : Nat.Prime p) (delta : ℝ) :
    0 < cpRadialCofactor p delta := by
  have hpgt : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp.one_lt
  by_cases hdelta : delta = 0
  · simp [cpRadialCofactor, hdelta, Real.log_pos hpgt]
  · rcases lt_or_gt_of_ne hdelta with hneg | hpos
    · have hpow :
          (p : ℝ) ^ delta < (p : ℝ) ^ (-delta) :=
        (Real.strictMono_rpow_of_base_gt_one hpgt) (by linarith)
      have hdiff : cpRadialDifference p delta < 0 := by
        unfold cpRadialDifference
        linarith
      have hden : (2 : ℝ) * delta < 0 :=
        mul_neg_of_pos_of_neg (by norm_num) hneg
      rw [cpRadialCofactor, if_neg hdelta]
      exact div_pos_of_neg_of_neg hdiff hden
    · have hpow :
          (p : ℝ) ^ (-delta) < (p : ℝ) ^ delta :=
        (Real.strictMono_rpow_of_base_gt_one hpgt) (by linarith)
      have hdiff : 0 < cpRadialDifference p delta := by
        unfold cpRadialDifference
        linarith
      have hden : 0 < (2 : ℝ) * delta := by positivity
      rw [cpRadialCofactor, if_neg hdelta]
      exact div_pos hdiff hden

/-- Fluxo orientado: o negativo do Wronskiano na convencao anterior. -/
def finiteOrientedCpGreenFlux (p M : ℕ) (s : ℂ) : ℂ :=
  -finitePhaseNormalizedCpGreenFlux p M s

/-- O fluxo orientado possui coeficiente `p^delta - p^(-delta)`. -/
theorem finiteOrientedCpGreenFlux_eq_radialDifference_mul_pairing
    (p M : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    finiteOrientedCpGreenFlux p M s =
      ((cpRadialDifference p (criticalDisplacement s.re) : ℝ) : ℂ) *
        finiteReflectedGradientPairing M s := by
  rw [finiteOrientedCpGreenFlux,
    finitePhaseNormalizedCpGreenFlux_eq_radialDifference_mul_pairing p M hp s]
  unfold cpRadialDifference
  push_cast
  ring

/-- Energia real finita depois de absorver o cofator radial positivo. -/
def finiteRadialGreenEnergy (p M : ℕ) (s : ℂ) : ℝ :=
  cpRadialCofactor p (criticalDisplacement s.re) *
    (finiteReflectedGradientPairing M s).re

/-- Fluxo total real: bulk orientado mais a corrente de Stokes explicita. -/
def finiteSignedCpGreenFlux (p M : ℕ) (s : ℂ) : ℝ :=
  (finiteOrientedCpGreenFlux p M s).re +
    (finiteReflectedStokesFlux M s).re

/-- Bordo real literal, ainda contendo o endpoint interno. -/
def finiteSignedCpGreenBoundary (M : ℕ) (s : ℂ) : ℝ :=
  (finiteReflectedBoundary M s).re

/-!
Identidade Green assinada em corte finito. Ela ja exibe exatamente o fator
`2 * (Re(s)-1/2)` exigido pela ponte abstrata; o sinal restante fica na parte
real da energia refletida, cuja positividade e a proxima obrigacao analitica.
-/
theorem finiteSignedCpGreen_identity
    (p M : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    finiteSignedCpGreenFlux p M s =
      2 * criticalDisplacement s.re * finiteRadialGreenEnergy p M s +
        finiteSignedCpGreenBoundary M s := by
  have hbulk :=
    finiteOrientedCpGreenFlux_eq_radialDifference_mul_pairing p M hp s
  have hradial :=
    cpRadialDifference_eq_two_mul_delta_mul_cofactor
      p (criticalDisplacement s.re)
  unfold finiteSignedCpGreenFlux finiteRadialGreenEnergy
    finiteSignedCpGreenBoundary
  rw [hbulk, finiteReflectedStokesFlux_eq_endpoints]
  change
    (cpRadialDifference p (criticalDisplacement s.re) *
        (finiteReflectedGradientPairing M s).re) +
      (finiteReflectedOuterEndpoint M s -
        finiteReflectedOuterEndpoint 0 s).re = _
  rw [hradial]
  rfl

end

end CPFormal.Analytic.Cp
