import CPFormal.Logic.HilbertPolya

/-!
# Interface para a realizacao espectral de fronteira

O objeto abaixo e um alvo de construcao. Nenhum valor concreto do Genuine e
nenhum zero numerico e usado para fabrica-lo.
-/

namespace CPFormal

structure BoundarySpectralRealization (GenuineZero : ℂ → Prop)
    extends RealSpectralCarrier where
  spectral_iff : ∀ {s : ℂ},
    GenuineZero s ↔ IsEigenvalue (spectralParameter s)

theorem criticalLine_of_boundarySpectralRealization
    (GenuineZero : ℂ → Prop)
    (model : BoundarySpectralRealization GenuineZero)
    {s : ℂ} (hs : GenuineZero s) : OnCriticalLine s := by
  exact hilbertPolya_implication GenuineZero model.toRealSpectralCarrier
    (fun hz ↦ model.spectral_iff.mp hz) hs

end CPFormal
