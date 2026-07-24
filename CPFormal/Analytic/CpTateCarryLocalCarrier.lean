import CPFormal.Analytic.CpCarryAmplitudeIdentification
import CPFormal.Analytic.CpCarryWeightedVerticalTfvdFinite
import CPFormal.Analytic.CpFiniteGreenRadial

/-!
# Carrier local de Tate e covariancia de fase da TFVD do carry

Este modulo formaliza somente o dicionario local sugerido pelo caracter
nao ramificado trivial na decomposicao de Tate. O caso geral teria ainda o
fator local do caracter. Nao formalizamos adeles, integrais zeta, Poisson ou
uma equacao funcional.

Para uma base prima `p`, o carrier local e

`r_p(s) = p^(-s)`,

implementado pelo monomio de Dirichlet ja usado no Green. Sua torre de
valuacoes e `r_p(s)^k`. Provamos:

* a torre geometrica esta no kernel da segunda diferenca cujo peso acompanha
  o proprio carrier;
* o traco inicial da torre e `(1, 0)`, portanto o estado nao e zero;
* a primeira diferenca, o bracket, o traco e a soma Green finita sao
  covariantes pelo dressing complexo `x_k |-> u^k x_k`;
* o normalizador de fase ja presente no Green transporta o carrier de Tate
  para a amplitude real do ramo e, no equilibrio critico, para
  `primeCarryAmplitudeRatio p`;
* congelar o bracket no peso critico produz exatamente um defeito quadratico
  entre a amplitude radial e a amplitude do carry.

O ultimo ponto e um guarda de escopo: provar que um zero Genuine anula esse
defeito ainda seria a ponte de observabilidade `Genuine -> Green`. Nenhuma
afirmacao desse tipo e usada ou declarada aqui.
-/

open scoped BigOperators

namespace CPFormal.Analytic.Cp

open CPFormal.Carry.Cp

noncomputable section

/-! ## Torre local do caracter nao ramificado trivial -/

/-- Razao do carrier local para o caracter nao ramificado trivial: `p^(-s)`. -/
def tateUnramifiedLocalRatio (p : ℕ) (s : ℂ) : ℂ :=
  natDirichletTerm s p

/-- Casca de valuacao `k` da torre local nao ramificada. -/
def tateUnramifiedValuationShell
    (p : ℕ) (s : ℂ) (k : ℕ) : ℂ :=
  tateUnramifiedLocalRatio p s ^ k

/-- A razao local nunca zera numa base prima. -/
theorem tateUnramifiedLocalRatio_ne_zero
    (p : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    tateUnramifiedLocalRatio p s ≠ 0 := by
  have hpC : (p : ℂ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  simp [tateUnramifiedLocalRatio, natDirichletTerm, dirichletTerm, hpC]

/-- A norma do carrier local e a amplitude real da primeira camada do ramo. -/
theorem norm_tateUnramifiedLocalRatio_eq_branchAmplitude
    (p : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    ‖tateUnramifiedLocalRatio p s‖ =
      branchAmplitude p s.re 1 := by
  have hpR : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp.pos
  unfold tateUnramifiedLocalRatio natDirichletTerm dirichletTerm
  change ‖((p : ℝ) : ℂ) ^ (-s)‖ = branchAmplitude p s.re 1
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hpR]
  simp [branchAmplitude]

/-- Na meia-abscissa, a norma da razao local e exatamente a razao de
amplitude usada pela valvula vertical do carry. -/
theorem norm_tateUnramifiedLocalRatio_eq_primeCarryAmplitudeRatio
    (p : ℕ) (hp : Nat.Prime p) (s : ℂ)
    (hre : s.re = (1 : ℝ) / 2) :
    ‖tateUnramifiedLocalRatio p s‖ =
      primeCarryAmplitudeRatio p := by
  rw [norm_tateUnramifiedLocalRatio_eq_branchAmplitude p hp s]
  exact
    (branchAmplitude_one_eq_primeCarryAmplitudeRatio_iff
      p hp s.re).2 hre

/-- A primeira diferenca adaptada ao proprio carrier ve a torre padrao como
constante em coordenadas despidas. -/
theorem tateUnramifiedValuationShell_firstDifference_eq_zero
    (p : ℕ) (hp : Nat.Prime p) (s : ℂ) (k : ℕ) :
    carryWeightedScalarFirstDifference
      (tateUnramifiedLocalRatio p s)
      (tateUnramifiedValuationShell p s) k = 0 := by
  have hr := tateUnramifiedLocalRatio_ne_zero p hp s
  unfold carryWeightedScalarFirstDifference
    tateUnramifiedValuationShell
  rw [pow_succ]
  field_simp [hr]
  ring

/-- Consequentemente, o bracket adaptado ao carrier local anula a torre para
todo parametro `s`, e nao somente na meia-abscissa. -/
theorem tateUnramifiedValuationShell_secondDifference_eq_zero
    (p : ℕ) (hp : Nat.Prime p) (s : ℂ) (k : ℕ) :
    carryWeightedScalarSecondDifference
      (tateUnramifiedLocalRatio p s)
      (tateUnramifiedValuationShell p s) k = 0 := by
  unfold carryWeightedScalarSecondDifference
  rw [
    tateUnramifiedValuationShell_firstDifference_eq_zero p hp s (k + 1),
    tateUnramifiedValuationShell_firstDifference_eq_zero p hp s k]
  simp

/-- O bracket nulo nao apaga o estado: o traco valor--inclinacao da torre
padrao e `(1, 0)`. -/
theorem tateUnramifiedValuationShell_initialTrace
    (p : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    (tateUnramifiedValuationShell p s 0,
      carryWeightedScalarFirstDifference
        (tateUnramifiedLocalRatio p s)
        (tateUnramifiedValuationShell p s) 0) =
      ((1 : ℂ), 0) := by
  rw [tateUnramifiedValuationShell_firstDifference_eq_zero p hp s 0]
  simp [tateUnramifiedValuationShell]

/-! ## Covariancia por dressing complexo -/

/-- Dressing diagonal de uma sequencia por uma razao complexa `u`.
Apesar do nome historico, `u` nao precisa ter norma um; a identidade e uma
covariancia geometrica geral. -/
def carryPhaseDress
    (u : ℂ) (x : ℕ → ℂ) (k : ℕ) : ℂ :=
  u ^ k * x k

/-- A primeira diferenca e covariante pelo dressing. -/
theorem carryWeightedScalarFirstDifference_phaseDress
    {u q : ℂ} (hu : u ≠ 0) (hq : q ≠ 0)
    (x : ℕ → ℂ) (k : ℕ) :
    carryWeightedScalarFirstDifference (u * q)
        (carryPhaseDress u x) k =
      u ^ k * carryWeightedScalarFirstDifference q x k := by
  unfold carryWeightedScalarFirstDifference carryPhaseDress
  rw [pow_succ]
  field_simp [hu, hq]

/-- O bracket ganha uma potencia adicional da fase. -/
theorem carryWeightedScalarSecondDifference_phaseDress
    {u q : ℂ} (hu : u ≠ 0) (hq : q ≠ 0)
    (x : ℕ → ℂ) (k : ℕ) :
    carryWeightedScalarSecondDifference (u * q)
        (carryPhaseDress u x) k =
      u ^ (k + 1) * carryWeightedScalarSecondDifference q x k := by
  unfold carryWeightedScalarSecondDifference
  rw [
    carryWeightedScalarFirstDifference_phaseDress hu hq x (k + 1),
    carryWeightedScalarFirstDifference_phaseDress hu hq x k,
    pow_succ]
  ring

/-- Traco escalar valor--inclinacao correspondente a TFVD finita. -/
def carryWeightedScalarTrace
    (q : ℂ) (x : ℕ → ℂ) : ℂ × ℂ :=
  (x 0, carryWeightedScalarFirstDifference q x 0)

/-- O traco inicial e invariante pelo dressing. -/
theorem carryWeightedScalarTrace_phaseDress
    {u q : ℂ} (hu : u ≠ 0) (hq : q ≠ 0)
    (x : ℕ → ℂ) :
    carryWeightedScalarTrace (u * q) (carryPhaseDress u x) =
      carryWeightedScalarTrace q x := by
  unfold carryWeightedScalarTrace
  rw [carryWeightedScalarFirstDifference_phaseDress hu hq x 0]
  simp [carryPhaseDress]

/-- A soma Green finita transforma coordenada a coordenada pelo mesmo
dressing. -/
theorem carryWeightedScalarGreenSum_phaseDress
    {u q : ℂ} (hu : u ≠ 0) (hq : q ≠ 0)
    (x : ℕ → ℂ) (n : ℕ) :
    carryWeightedScalarGreenSum (u * q)
        (carryPhaseDress u x) n =
      u ^ n * carryWeightedScalarGreenSum q x n := by
  unfold carryWeightedScalarGreenSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < n := Finset.mem_range.mp hj
  have hexponent : n - 1 - j + (j + 1) = n := by
    omega
  rw [
    carryWeightedScalarSecondDifference_phaseDress hu hq x j,
    mul_pow]
  have hphase :
      u ^ (n - 1 - j) * u ^ (j + 1) = u ^ n := by
    rw [← pow_add, hexponent]
  calc
    ((n - 1 - j : ℕ) : ℂ) *
          (u ^ (n - 1 - j) * q ^ (n - 1 - j)) *
          (u ^ (j + 1) *
            carryWeightedScalarSecondDifference q x j) =
        (u ^ (n - 1 - j) * u ^ (j + 1)) *
          (((n - 1 - j : ℕ) : ℂ) * q ^ (n - 1 - j) *
            carryWeightedScalarSecondDifference q x j) := by
      ring
    _ = u ^ n *
          (((n - 1 - j : ℕ) : ℂ) * q ^ (n - 1 - j) *
            carryWeightedScalarSecondDifference q x j) := by
      rw [hphase]

/-! ## Retirada da fase e identificacao com a amplitude do carry -/

/-- Normalizador que retira somente a fase do carrier local. O fator
`cpPhaseNormalizer` retira fase e escala critica; multiplicar pela razao
critica recoloca a escala `p^(-1/2)`. -/
def tateCarryPhaseNormalizer (p : ℕ) (s : ℂ) : ℂ :=
  (primeCarryAmplitudeRatio p : ℂ) * cpPhaseNormalizer p s

/-- Depois da retirada de fase, a razao local se torna a amplitude real do
ramo, escrita relativamente a amplitude critica. -/
theorem tateCarryPhaseNormalizer_mul_localRatio
    (p : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    tateCarryPhaseNormalizer p s *
        tateUnramifiedLocalRatio p s =
      (primeCarryAmplitudeRatio p : ℂ) *
        (((p : ℝ) ^ (-criticalDisplacement s.re) : ℝ) : ℂ) := by
  unfold tateCarryPhaseNormalizer tateUnramifiedLocalRatio
  rw [mul_assoc, cpPhaseNormalizer_mul_eigenvalue p hp s]

/-- No equilibrio critico, a razao local despida e literalmente a razao de
amplitude da valvula vertical. -/
theorem tateCarryPhaseNormalizer_mul_localRatio_of_critical
    (p : ℕ) (hp : Nat.Prime p) (s : ℂ)
    (hdelta : criticalDisplacement s.re = 0) :
    tateCarryPhaseNormalizer p s *
        tateUnramifiedLocalRatio p s =
      (primeCarryAmplitudeRatio p : ℂ) := by
  rw [tateCarryPhaseNormalizer_mul_localRatio p hp s, hdelta]
  simp

/-- A retirada diagonal de fase transporta cada casca local para a torre
geometrica real do carry no equilibrio critico. -/
theorem tateCarryPhaseDressedShell_eq_primeCarryShell
    (p : ℕ) (hp : Nat.Prime p) (s : ℂ)
    (hdelta : criticalDisplacement s.re = 0) (k : ℕ) :
    carryPhaseDress (tateCarryPhaseNormalizer p s)
        (tateUnramifiedValuationShell p s) k =
      (primeCarryAmplitudeRatio p : ℂ) ^ k := by
  unfold carryPhaseDress tateUnramifiedValuationShell
  rw [← mul_pow,
    tateCarryPhaseNormalizer_mul_localRatio_of_critical
      p hp s hdelta]

/-- A torre despida coincide coordenada a coordenada com o modo de retorno
de bordo `(1, 0)` da TFVD material. -/
theorem tateCarryPhaseDressedShell_eq_primeCarryReturn
    (p : ℕ) (hp : Nat.Prime p) (s : ℂ)
    (hdelta : criticalDisplacement s.re = 0) (k : ℕ) :
    carryPhaseDress (tateCarryPhaseNormalizer p s)
        (tateUnramifiedValuationShell p s) k =
      primeCarryWeightedVerticalReturn p hp.two_le ((1 : ℂ), 0) k := by
  rw [tateCarryPhaseDressedShell_eq_primeCarryShell p hp s hdelta k]
  simp [primeCarryWeightedVerticalReturn]

/-! ## Defeito ao congelar o carrier critico -/

/-- Aplicar um bracket de peso `q` a uma torre geometrica de razao `r`
produz um mismatch quadratico exato. -/
theorem carryWeightedScalarSecondDifference_geometricMismatch
    {q : ℂ} (hq : q ≠ 0) (r : ℂ) (k : ℕ) :
    carryWeightedScalarSecondDifference q (fun n : ℕ => r ^ n) k =
      q⁻¹ * r ^ k * (r - q) ^ 2 := by
  rw [carryWeightedScalarSecondDifference_eq hq]
  simp only [pow_add]
  field_simp [hq]
  ring

/-- Ja na primeira camada, o bracket congelado zera exatamente quando as
duas razoes coincidem. -/
theorem carryWeightedScalarSecondDifference_geometric_zero_iff
    {q : ℂ} (hq : q ≠ 0) (r : ℂ) :
    carryWeightedScalarSecondDifference q (fun n : ℕ => r ^ n) 0 = 0 ↔
      r = q := by
  rw [carryWeightedScalarSecondDifference_geometricMismatch hq r 0]
  simp [hq, sub_eq_zero]

/-- Para uma base prima, congelar o bracket na amplitude critica seleciona a
meia-abscissa entre as torres de amplitude radial. -/
theorem primeCarryCriticalBracket_radialShell_zero_iff
    (p : ℕ) (hp : Nat.Prime p) (sigma : ℝ) :
    carryWeightedScalarSecondDifference
        (primeCarryAmplitudeRatio p : ℂ)
        (fun k : ℕ => ((branchAmplitude p sigma 1 : ℝ) : ℂ) ^ k) 0 = 0 ↔
      sigma = (1 : ℝ) / 2 := by
  have hq :
      (primeCarryAmplitudeRatio p : ℂ) ≠ 0 := by
    exact_mod_cast
      (primeCarryAmplitudeRatio_pos p hp.one_le).ne'
  rw [
    carryWeightedScalarSecondDifference_geometric_zero_iff hq
      ((branchAmplitude p sigma 1 : ℝ) : ℂ)]
  constructor
  · intro heq
    have heqReal :
        branchAmplitude p sigma 1 =
          primeCarryAmplitudeRatio p := by
      exact_mod_cast heq
    exact
      (branchAmplitude_one_eq_primeCarryAmplitudeRatio_iff
        p hp sigma).1 heqReal
  · intro hsigma
    exact_mod_cast
      (branchAmplitude_one_eq_primeCarryAmplitudeRatio_iff
        p hp sigma).2 hsigma

end

end CPFormal.Analytic.Cp
