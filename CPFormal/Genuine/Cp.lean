import CPFormal.Genuine.BalancedOffsets
import CPFormal.Genuine.FiniteCancellation

/-!
# Camera Genuine Cp finita

Para uma camera de base `p`, as pernas sao indexadas pelos offsets balanceados
nao nulos. O bracket subtrai `(p-1)` copias do centro. A lei de cancelamento e
puramente finita e vale antes de assumir que `p` e primo.
-/

open scoped BigOperators

namespace CPFormal.Genuine.Cp

variable {R : Type*} [CommRing R]

noncomputable section

/-- Soma das `p-1` pernas formais da camera Cp. -/
def legSum (p : ℕ) (f : ℤ → R) (center : ℤ) : R :=
  ∑ a ∈ balancedOffsets p, f (center + a)

/-- Bracket saturado da camera Cp. -/
def bracket (p : ℕ) (f : ℤ → R) (center : ℤ) : R :=
  legSum p f center - ((p - 1 : ℕ) : R) * f center

@[simp] theorem local_genuine_cancellation
    (p : ℕ) (f : ℤ → R) (center : ℤ) :
    legSum p f center - bracket p f center =
      ((p - 1 : ℕ) : R) * f center := by
  simp [bracket]

/-- Canal direto Cp numa caixa finita. -/
def finiteDirect
    (p : ℕ) (centers : Finset ℤ) (weight : ℤ → R) (f : ℤ → R) : R :=
  ∑ c ∈ centers, weight c * legSum p f c

/-- Canal dos brackets Cp na mesma caixa. -/
def finiteBrackets
    (p : ℕ) (centers : Finset ℤ) (weight : ℤ → R) (f : ℤ → R) : R :=
  ∑ c ∈ centers, weight c * bracket p f c

/-- Centros Cp sobreviventes, com multiplicidade `p-1`. -/
def finiteCenters
    (p : ℕ) (centers : Finset ℤ) (weight : ℤ → R) (f : ℤ → R) : R :=
  ∑ c ∈ centers, weight c * ((p - 1 : ℕ) : R) * f c

/-- Versao Cp da lei Genuine finita. -/
theorem finite_genuine_cancellation
    (p : ℕ) (centers : Finset ℤ) (weight : ℤ → R) (f : ℤ → R) :
    finiteDirect p centers weight f - finiteBrackets p centers weight f =
      finiteCenters p centers weight f := by
  classical
  simp only [finiteDirect, finiteBrackets, finiteCenters]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  simp [bracket]
  ring

end
end CPFormal.Genuine.Cp
