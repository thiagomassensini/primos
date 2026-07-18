import Mathlib

/-!
# Nucleo logico de Hilbert--Polya

Este arquivo prova somente a implicacao logica. Ele nao afirma que o operador
espectral existe. A existencia e a correspondencia exata permanecem como
obrigacoes explicitas.
-/

namespace CPFormal

/-- Um ponto complexo esta na linha critica. -/
def OnCriticalLine (s : ℂ) : Prop :=
  s.re = (1 : ℝ) / 2

/-- Rotacao que transforma a linha critica no eixo real espectral. -/
def spectralParameter (s : ℂ) : ℂ :=
  ⟨s.im, (1 : ℝ) / 2 - s.re⟩

@[simp] theorem spectralParameter_re (s : ℂ) :
    (spectralParameter s).re = s.im := rfl

@[simp] theorem spectralParameter_im (s : ℂ) :
    (spectralParameter s).im = (1 : ℝ) / 2 - s.re := rfl

theorem onCriticalLine_of_spectralParameter_im_eq_zero {s : ℂ}
    (h : (spectralParameter s).im = 0) : OnCriticalLine s := by
  rw [spectralParameter_im] at h
  unfold OnCriticalLine
  linarith

theorem spectralParameter_im_eq_zero_iff (s : ℂ) :
    (spectralParameter s).im = 0 ↔ OnCriticalLine s := by
  constructor
  · exact onCriticalLine_of_spectralParameter_im_eq_zero
  · intro h
    rw [spectralParameter_im]
    unfold OnCriticalLine at h
    linarith

/--
Interface minima para a unica consequencia espectral usada pela deducao de
Hilbert--Polya: todo autovalor admitido tem parte imaginaria zero.

Uma etapa posterior devera construir este objeto a partir de um operador
autoadjunto real da mathlib, e nao postula-lo para o Genuine.
-/
structure RealSpectralCarrier where
  IsEigenvalue : ℂ → Prop
  eigenvalue_im_eq_zero : ∀ {λ : ℂ}, IsEigenvalue λ → λ.im = 0

/--
A correspondencia de todos os zeros Genuine com um espectro real implica que
todos esses zeros estao na linha critica.
-/
theorem hilbertPolya_implication
    (GenuineZero : ℂ → Prop)
    (carrier : RealSpectralCarrier)
    (spectralCorrespondence :
      ∀ {s : ℂ}, GenuineZero s →
        carrier.IsEigenvalue (spectralParameter s))
    {s : ℂ} (hs : GenuineZero s) : OnCriticalLine s := by
  apply onCriticalLine_of_spectralParameter_im_eq_zero
  exact carrier.eigenvalue_im_eq_zero (spectralCorrespondence hs)

end CPFormal
