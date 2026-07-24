import CPFormal.Analytic.CpGenuineGreenKernelInclusion
import CPFormal.Analytic.CpTateCarryLocalCarrier

/-!
# Guarda do bracket radial critico

O dicionario local de Tate e a covariancia geometrica da TFVD nao produzem
por si so uma ponte global. Este modulo registra separadamente a obrigacao
radial que seria necessaria para localizar zeros Genuine.

O enunciado abaixo usa diretamente a torre de amplitude radial, nao um objeto
adelico. O teorema principal prova que fecha-la em todo zero Genuine e
equivalente ao enunciado forte de nao anulacao off-critical. Nenhuma instancia
dessa hipotese e declarada.
-/

namespace CPFormal.Analytic.Cp

open CPFormal.Carry.Cp

noncomputable section

/-- Formulacao radial da ponte ainda ausente: todo zero Genuine no strip
anularia o bracket critico congelado aplicado a torre de amplitude do ramo. -/
def GenuineKernelClosesCriticalRadialBracket (p : ℕ) : Prop :=
  ∀ {s : ℂ}, genuineContinuation s = 0 →
    s ∈ genuineCriticalStrip →
      carryWeightedScalarSecondDifference
          (primeCarryAmplitudeRatio p : ℂ)
          (fun k : ℕ =>
            ((branchAmplitude p s.re 1 : ℝ) : ℂ) ^ k) 0 = 0

/-- Para uma base prima, fechar o bracket radial critico em todo zero Genuine
e exatamente o enunciado forte de nao anulacao off-critical. Este teorema
impede que a covariancia local seja confundida com a observabilidade global
ainda aberta. -/
theorem genuineKernelClosesCriticalRadialBracket_iff_strongNonvanishing
    (p : ℕ) (hp : Nat.Prime p) :
    GenuineKernelClosesCriticalRadialBracket p ↔
      GenuineStrongNonvanishingInStrip := by
  constructor
  · intro hbridge s hs hoff hzero
    have hre :
        s.re = (1 : ℝ) / 2 :=
      (primeCarryCriticalBracket_radialShell_zero_iff
        p hp s.re).1 (hbridge hzero hs)
    exact hoff hre
  · intro hstrong s hzero hs
    apply
      (primeCarryCriticalBracket_radialShell_zero_iff
        p hp s.re).2
    by_contra hoff
    exact (hstrong hs hoff) hzero

end

end CPFormal.Analytic.Cp
