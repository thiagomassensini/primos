import Mathlib

/-!
# Offsets balanceados da camera prima

Para um natural `p`, usamos o semialcance `(p-1)/2` e removemos o zero do
intervalo simetrico. As hipoteses "p primo e impar" entram nos teoremas de
cardinalidade e cobertura residual, que serao adicionados separadamente.
-/

namespace CPFormal.Genuine.Cp

noncomputable section

/-- Semialcance da camera prima. -/
def halfRange (p : ℕ) : ℕ :=
  (p - 1) / 2

/-- Conjunto finito `{-h, ..., -1, 1, ..., h}`. -/
def balancedOffsets (p : ℕ) : Finset ℤ :=
  (Finset.Icc (-(halfRange p : ℤ)) (halfRange p : ℤ)).erase 0

@[simp] theorem zero_not_mem_balancedOffsets (p : ℕ) :
    (0 : ℤ) ∉ balancedOffsets p := by
  simp [balancedOffsets]

theorem mem_balancedOffsets_iff {p : ℕ} {a : ℤ} :
    a ∈ balancedOffsets p ↔
      a ≠ 0 ∧ (-(halfRange p : ℤ) ≤ a ∧ a ≤ (halfRange p : ℤ)) := by
  simp [balancedOffsets]

end
end CPFormal.Genuine.Cp
