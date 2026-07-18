import CPFormal.Genuine.FiniteCancellation

/-!
# Camera Genuine C2 finita

O indice e inteiro para que as duas pernas `c-1` e `c+1` sejam literais. A
restricao aos centros positivos e a bijecao com os impares entram na camada de
carry, nao na identidade algebrica.
-/

open scoped BigOperators

namespace CPFormal.Genuine.C2

variable {R : Type*} [CommRing R]

/-- Soma das duas pernas gemeas da camera C2. -/
def legSum (f : ℤ → R) (center : ℤ) : R :=
  f (center - 1) + f (center + 1)

/-- Segunda diferenca C2: pernas menos duas copias do centro. -/
def bracket (f : ℤ → R) (center : ℤ) : R :=
  legSum f center - (2 : R) * f center

@[simp] theorem local_genuine_cancellation (f : ℤ → R) (center : ℤ) :
    legSum f center - bracket f center = (2 : R) * f center := by
  simp [bracket]

/-- Canal direto C2 em uma caixa finita de centros. -/
def finiteDirect
    (centers : Finset ℤ) (weight : ℤ → R) (f : ℤ → R) : R :=
  ∑ c ∈ centers, weight c * legSum f c

/-- Canal de brackets C2 na mesma caixa e com os mesmos pesos. -/
def finiteBrackets
    (centers : Finset ℤ) (weight : ℤ → R) (f : ℤ → R) : R :=
  ∑ c ∈ centers, weight c * bracket f c

/-- Canal dos centros C2 que sobrevivem. -/
def finiteCenters
    (centers : Finset ℤ) (weight : ℤ → R) (f : ℤ → R) : R :=
  ∑ c ∈ centers, weight c * (2 : R) * f c

/-- Versao C2 da lei Genuine finita. -/
theorem finite_genuine_cancellation
    (centers : Finset ℤ) (weight : ℤ → R) (f : ℤ → R) :
    finiteDirect centers weight f - finiteBrackets centers weight f =
      finiteCenters centers weight f := by
  classical
  simp only [finiteDirect, finiteBrackets, finiteCenters]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  simp [bracket]
  ring

end CPFormal.Genuine.C2
