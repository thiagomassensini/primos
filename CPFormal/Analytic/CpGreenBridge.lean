import CPFormal.Analytic.CpTiltRigidity

/-!
# Criterio Green para fechar a ponte Genuine--ramo

Este modulo nao postula uma instancia de `GenuineBranchBridge`. Em vez disso,
decompoe a obrigacao analitica em dados verificaveis de uma identidade de
Green assinada:

`flux = 2 * criticalDisplacement * radialEnergy + boundary`.

Para um zero Genuine, ainda e necessario provar separadamente que o fluxo e o
termo de bordo se anulam. A positividade estrita da energia entao impede que o
deslocamento critico seja nao nulo. Somente depois desses quatro fatos o
certificado pode produzir uma `GenuineBranchBridge`.

Nenhum certificado concreto e construido neste arquivo.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-
Certificado completo da relacao de Green necessaria para transportar zeros
Genuine ate a linha critica. Os campos deixam expostos, sem circularidade, a
identidade bulk--bordo e os dois lemas de fechamento no zero.
-/
structure SignedGreenCertificate (genuine : ℂ → ℂ) where
  /-- Fluxo total da geometria de carry. -/
  flux : ℂ → ℝ
  /-- Energia radial positiva no bulk. -/
  radialEnergy : ℂ → ℝ
  /-- Contribuicao de cauda/bordo que completa a identidade. -/
  boundary : ℂ → ℝ
  /-- Identidade assinada de Green no semiplano positivo. -/
  green_identity :
    ∀ {s : ℂ}, 0 < s.re →
      flux s =
        2 * criticalDisplacement s.re * radialEnergy s + boundary s
  /-- A energia nao pode desaparecer no dominio em que consumimos zeros. -/
  radialEnergy_pos :
    ∀ {s : ℂ}, 0 < s.re → 0 < radialEnergy s
  /-- O escalar Genuine anula o fluxo total. -/
  flux_zero_of_genuine_zero :
    ∀ {s : ℂ}, genuine s = 0 → 0 < s.re → flux s = 0
  /-- A cauda genuina fechada nao deixa um residual de bordo no zero. -/
  boundary_zero_of_genuine_zero :
    ∀ {s : ℂ}, genuine s = 0 → 0 < s.re → boundary s = 0

/-
Coracao logico da rota Green: no zero Genuine, a identidade e a positividade
forcam o deslocamento critico a se anular.
-/
theorem SignedGreenCertificate.criticalDisplacement_eq_zero_of_genuine_zero
    {genuine : ℂ → ℂ} (certificate : SignedGreenCertificate genuine)
    {s : ℂ} (hzero : genuine s = 0) (hre : 0 < s.re) :
    criticalDisplacement s.re = 0 := by
  have hgreen := certificate.green_identity hre
  have hflux := certificate.flux_zero_of_genuine_zero hzero hre
  have hboundary := certificate.boundary_zero_of_genuine_zero hzero hre
  have henergy := certificate.radialEnergy_pos hre
  rw [hflux, hboundary, add_zero] at hgreen
  have hproduct :
      criticalDisplacement s.re * certificate.radialEnergy s = 0 := by
    nlinarith
  exact (mul_eq_zero.mp hproduct).resolve_right (ne_of_gt henergy)

/-- Um certificado Green concreto fabrica a ponte Genuine--ramo, para cada primo. -/
def SignedGreenCertificate.toGenuineBranchBridge
    {genuine : ℂ → ℂ} (certificate : SignedGreenCertificate genuine)
    (p : ℕ) (hp : Nat.Prime p) :
    GenuineBranchBridge p genuine := by
  refine ⟨?_⟩
  intro s hzero hre
  apply (branchNormSq_eq_one_iff p hp hre).2
  have hdelta :=
    certificate.criticalDisplacement_eq_zero_of_genuine_zero hzero hre
  unfold criticalDisplacement at hdelta
  linarith

/-- A mesma relacao Green transporta zeros Genuine para o zero de todo tilt Cp. -/
theorem SignedGreenCertificate.cpTiltAtSigma_eq_zero_of_genuine_zero
    {genuine : ℂ → ℂ} (certificate : SignedGreenCertificate genuine)
    (p : ℕ) (hpodd : Odd p)
    {s : ℂ} (hzero : genuine s = 0) (hre : 0 < s.re)
    (center : ℝ) :
    cpTiltAtSigma p s.re center = 0 := by
  have hdelta :=
    certificate.criticalDisplacement_eq_zero_of_genuine_zero hzero hre
  have hhalf : s.re = (1 : ℝ) / 2 := by
    unfold criticalDisplacement at hdelta
    linarith
  rw [hhalf]
  exact cpTiltAtSigma_half p hpodd center

/-- Consequencia final condicional, agora fatorada pelo certificado Green explicito. -/
theorem SignedGreenCertificate.re_eq_half_of_genuine_zero
    {genuine : ℂ → ℂ} (certificate : SignedGreenCertificate genuine)
    {s : ℂ} (hzero : genuine s = 0) (hre : 0 < s.re) :
    s.re = (1 : ℝ) / 2 := by
  have hdelta :=
    certificate.criticalDisplacement_eq_zero_of_genuine_zero hzero hre
  unfold criticalDisplacement at hdelta
  linarith

end

end CPFormal.Analytic.Cp
