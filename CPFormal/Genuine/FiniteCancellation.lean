import Mathlib

/-!
# Lei finita do Genuine

Esta e a identidade central anterior a toda analise:

`canal direto das pernas - canal bracketado = centros sobreviventes`.

Nao ha zeta, zeros, limite ou continuacao analitica neste arquivo.
-/

open scoped BigOperators

namespace CPFormal.Genuine

variable {ι R : Type*} [CommRing R]

/-- Soma ponderada das pernas ja agrupadas por centro. -/
def directChannel
    (centers : Finset ι) (weight legs : ι → R) : R :=
  ∑ c in centers, weight c * legs c

/--
Canal bracketado: em cada centro, subtrai-se da soma das pernas o multiplo
central determinado pela camera.
-/
def bracketChannel
    (centers : Finset ι) (weight legs coefficient centerValue : ι → R) : R :=
  ∑ c in centers,
    weight c * (legs c - coefficient c * centerValue c)

/-- Canal formado somente pelos centros que sobrevivem ao cancelamento. -/
def survivingCenterChannel
    (centers : Finset ι) (weight coefficient centerValue : ι → R) : R :=
  ∑ c in centers, weight c * coefficient c * centerValue c

/-- Cancelamento local de uma camera em um unico centro. -/
theorem localCancellation (legs coefficient centerValue : R) :
    legs - (legs - coefficient * centerValue) = coefficient * centerValue := by
  ring

/--
Lei Genuine finita. Cada termo de perna cancela literalmente e resta apenas o
termo central ponderado. A identidade vale para qualquer conjunto finito de
centros e nao depende da origem analitica dos valores.
-/
theorem finiteCancellation
    (centers : Finset ι) (weight legs coefficient centerValue : ι → R) :
    directChannel centers weight legs -
        bracketChannel centers weight legs coefficient centerValue =
      survivingCenterChannel centers weight coefficient centerValue := by
  classical
  simp only [directChannel, bracketChannel, survivingCenterChannel]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  ring

end CPFormal.Genuine
