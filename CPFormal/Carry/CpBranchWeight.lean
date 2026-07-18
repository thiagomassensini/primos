import CPFormal.Carry.CpAlignedBox
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Pesos de profundidade do operador de ramo `Cₚ`

Este arquivo faz a primeira ligacao exata entre a geometria finita do carry e
os pesos do operador de ramo. Na abscissa critica, uma camada de profundidade
`k` recebe

`massa(p,k) = p^(-k)`

e amplitude

`amplitude(p,k) = p^(-k/2)`.

O quadrado da amplitude e provado igual a massa. Em seguida, o teorema de
reindexacao da caixa alinhada e especializado para esse peso concreto. Assim,
o expoente `k` usado pelo operador de ramo e literalmente a profundidade de
carry ja identificada pela camera `Cₚ`; nao e um indice calibrado depois.

O arquivo tambem define os pesos em uma abscissa real arbitraria `sigma`. A
serie infinita e a norma quadratica ficam no modulo analitico seguinte.
-/

open scoped BigOperators

namespace CPFormal.Carry.Cp

noncomputable section

/-- Massa critica de uma coordenada na profundidade de carry `k`: `p^(-k)`. -/
def criticalMass (p k : ℕ) : ℝ :=
  (p : ℝ) ^ (-((k : ℝ)))

/-- Amplitude critica na profundidade `k`: `p^(-k/2)`. -/
def criticalAmplitude (p k : ℕ) : ℝ :=
  (p : ℝ) ^ (-((k : ℝ)) / 2)

/-- Amplitude do ramo na abscissa `sigma`: `p^(-k sigma)`. -/
def branchAmplitude (p : ℕ) (sigma : ℝ) (k : ℕ) : ℝ :=
  (p : ℝ) ^ (-((k : ℝ)) * sigma)

/-- Razao quadratica entre duas profundidades consecutivas. -/
def branchRatio (p : ℕ) (sigma : ℝ) : ℝ :=
  (p : ℝ) ^ (-2 * sigma)

/-- Massa quadratica de uma perna na profundidade `k`. -/
def branchMassWeight (p : ℕ) (sigma : ℝ) (k : ℕ) : ℝ :=
  (branchRatio p sigma) ^ k

/-- A amplitude critica e nao negativa. -/
theorem criticalAmplitude_nonneg (p k : ℕ) :
    0 ≤ criticalAmplitude p k := by
  unfold criticalAmplitude
  exact Real.rpow_nonneg (by positivity) _

/-- Identidade local amplitude--massa: `(p^(-k/2))^2 = p^(-k)`. -/
@[simp] theorem criticalAmplitude_sq_eq_mass (p k : ℕ) :
    (criticalAmplitude p k) ^ 2 = criticalMass p k := by
  unfold criticalAmplitude criticalMass
  have hp0 : 0 ≤ (p : ℝ) := by positivity
  rw [← Real.rpow_mul_natCast hp0 (-((k : ℝ)) / 2) 2]
  congr 1
  ring

/-- O quadrado de `p^(-k sigma)` e a massa geometrica de razao `p^(-2 sigma)`. -/
@[simp] theorem branchAmplitude_sq_eq_massWeight
    (p : ℕ) (sigma : ℝ) (k : ℕ) :
    (branchAmplitude p sigma k) ^ 2 = branchMassWeight p sigma k := by
  unfold branchAmplitude branchMassWeight branchRatio
  have hp0 : 0 ≤ (p : ℝ) := by positivity
  calc
    ((p : ℝ) ^ (-((k : ℝ)) * sigma)) ^ 2 =
        (p : ℝ) ^ ((-((k : ℝ)) * sigma) * (2 : ℝ)) := by
      rw [Real.rpow_mul_natCast hp0]
    _ = (p : ℝ) ^ ((-2 * sigma) * (k : ℝ)) := by
      congr 1
      ring
    _ = ((p : ℝ) ^ (-2 * sigma)) ^ k := by
      rw [Real.rpow_mul_natCast hp0]

/-- Em `sigma = 1/2`, a amplitude geral vira `p^(-k/2)`. -/
@[simp] theorem branchAmplitude_half (p k : ℕ) :
    branchAmplitude p ((1 : ℝ) / 2) k = criticalAmplitude p k := by
  unfold branchAmplitude criticalAmplitude
  congr 1
  ring

/-- Em `sigma = 1/2`, a massa quadratica geral vira o peso de carry `p^(-k)`. -/
@[simp] theorem branchMassWeight_half (p k : ℕ) :
    branchMassWeight p ((1 : ℝ) / 2) k = criticalMass p k := by
  calc
    branchMassWeight p ((1 : ℝ) / 2) k =
        (branchAmplitude p ((1 : ℝ) / 2) k) ^ 2 :=
      (branchAmplitude_sq_eq_massWeight p ((1 : ℝ) / 2) k).symm
    _ = (criticalAmplitude p k) ^ 2 := by rw [branchAmplitude_half]
    _ = criticalMass p k := criticalAmplitude_sq_eq_mass p k

/--
O peso `p^(-k)` ve a mesma profundidade no canal direto e no centro canonico.
-/
@[simp] theorem criticalMass_effectiveDepth_eq_centerDepth
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (n : Nonmultiple p) :
    criticalMass p (effectiveDepth p n.1) =
      criticalMass p (centerDepth p hp hpodd n) := by
  rw [effectiveDepth_eq_centerDepth]

/--
Reindexacao sem bordo da caixa alinhada, agora com o peso concreto `p^(-k)`.
-/
theorem criticalMass_reindex_alignedBox
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) (M : ℕ)
    (value : ℤ → ℝ) :
    (∑ n ∈ alignedNonmultipleBox p hp hpodd M,
        nonmultipleTerm p (criticalMass p) value n) =
      ∑ x ∈ alignedIncidenceBox p hp M,
        incidenceTerm p (criticalMass p) value x := by
  exact weighted_reindex_alignedBox
    p hp hpodd M (criticalMass p) value

/-- A mesma reindexacao escrita como soma dos quadrados das amplitudes. -/
theorem criticalAmplitude_sq_reindex_alignedBox
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) (M : ℕ)
    (value : ℤ → ℝ) :
    (∑ n ∈ alignedNonmultipleBox p hp hpodd M,
        nonmultipleTerm p (fun k => (criticalAmplitude p k) ^ 2) value n) =
      ∑ x ∈ alignedIncidenceBox p hp M,
        incidenceTerm p (fun k => (criticalAmplitude p k) ^ 2) value x := by
  simpa only [criticalAmplitude_sq_eq_mass] using
    criticalMass_reindex_alignedBox p hp hpodd M value

end

end CPFormal.Carry.Cp
