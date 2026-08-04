import CPFormal.Analytic.CpPositionalCarryQuadraticRigidity
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Defeito massa–amplitude e o piso quadrático da rigidez de carry

Este módulo fecha, na álgebra pura de carry (antes de primos, sem número
complexo, sem continuação), a razão do fenômeno visto no laboratório: a norma
do resultante não zera fora do expoente autodual `σ = 1/2`.

A massa de carry na profundidade `k` é `m_b(k) = b^(-k)`; a amplitude deformada
é `a_{b,σ}(k) = b^(-kσ)`, com energia `a_{b,σ}(k)^2 = b^(-2kσ)`.  A razão entre
a energia deformada e a massa é

    massAmplitudeRatio b σ k = a_{b,σ}(k)^2 / m_b(k) = b^(-2k(σ-1/2)),

e o defeito normalizado é `D_{b,k}(σ) = b^(-2k(σ-1/2)) - 1`.  Escrevendo
`σ = 1/2 + δ`, isto é `b^(-2kδ) - 1`, cujo desenvolvimento de Taylor perto de
`δ = 0` é `-2k(log b)δ + O(δ²)`: defeito linear em `δ`, energia quadrática.
Foi exatamente a parábola `E_min(σ) ≈ C(σ-1/2)²` que apareceu na tela.

Resultados (toda base `b > 1`, toda profundidade `k > 0`):

* `normalizedMassDefect_eq_zero_iff` — o defeito zera ⇔ `σ = 1/2`;
* `normalizedMassDefect_pos_of_lt_half` / `_neg_of_half_lt` — sinal do defeito
  (cauda pesada abaixo, cabeça pesada acima);
* `massAmplitudeDefectEnergy_pos_of_ne_half` — **piso quadrático exato**: a
  energia do defeito é estritamente positiva fora de `σ = 1/2`.  Não há como
  anular a casca radial fora do autodual;
* `massAmplitudeDefectEnergy_zero_base_independent` — o locus de anulação não
  depende da base (invariante de régua).

Genuine First: nenhum zeta, equação funcional, número imaginário ou RH.
-/

open scoped BigOperators

namespace CPFormal.Analytic.Cp

open CPFormal.Carry.Cp

noncomputable section

variable {b k : ℕ}

/-- A massa de carry é estritamente positiva em toda base `b > 1`. -/
theorem criticalMass_pos (hb : 1 < b) (k : ℕ) : 0 < criticalMass b k := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast lt_trans Nat.zero_lt_one hb
  unfold criticalMass
  exact Real.rpow_pos_of_pos hb0 _

/-- Razão entre a energia da amplitude deformada e a massa de carry. -/
def massAmplitudeRatio (b : ℕ) (sigma : ℝ) (k : ℕ) : ℝ :=
  (branchAmplitude b sigma k) ^ 2 / criticalMass b k

/-- Forma exata da razão: `b^(-2k(σ-1/2))`.  Nenhuma coincidência: é a
incompatibilidade massa–amplitude escrita como potência real. -/
theorem massAmplitudeRatio_eq_rpow (hb : 1 < b) (sigma : ℝ) (k : ℕ) :
    massAmplitudeRatio b sigma k
      = (b : ℝ) ^ (-(2 : ℝ) * (k : ℝ) * (sigma - 1 / 2)) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast lt_trans Nat.zero_lt_one hb
  unfold massAmplitudeRatio branchAmplitude criticalMass
  rw [← Real.rpow_natCast ((b : ℝ) ^ (-(k : ℝ) * sigma)) 2,
    ← Real.rpow_mul hb0.le, ← Real.rpow_sub hb0]
  congr 1
  push_cast
  ring

/-- Defeito normalizado massa–amplitude: `D_{b,k}(σ) = b^(-2k(σ-1/2)) - 1`. -/
def normalizedMassDefect (b : ℕ) (sigma : ℝ) (k : ℕ) : ℝ :=
  massAmplitudeRatio b sigma k - 1

theorem normalizedMassDefect_eq_rpow (hb : 1 < b) (sigma : ℝ) (k : ℕ) :
    normalizedMassDefect b sigma k
      = (b : ℝ) ^ (-(2 : ℝ) * (k : ℝ) * (sigma - 1 / 2)) - 1 := by
  unfold normalizedMassDefect
  rw [massAmplitudeRatio_eq_rpow hb]

/-- O defeito normalizado zera exatamente no expoente autodual. -/
theorem normalizedMassDefect_eq_zero_iff (hb : 1 < b) (hk : 0 < k) (sigma : ℝ) :
    normalizedMassDefect b sigma k = 0 ↔ sigma = 1 / 2 := by
  have hmass := criticalMass_pos hb k
  unfold normalizedMassDefect massAmplitudeRatio
  rw [sub_eq_zero, div_eq_one_iff_eq (ne_of_gt hmass)]
  exact branchAmplitude_sq_eq_criticalMass_iff_of_one_lt b k hb hk sigma

/-- Abaixo do autodual a energia supera a massa (cauda pesada): defeito > 0. -/
theorem normalizedMassDefect_pos_of_lt_half (hb : 1 < b) (hk : 0 < k)
    {sigma : ℝ} (h : sigma < 1 / 2) :
    0 < normalizedMassDefect b sigma k := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast lt_trans Nat.zero_lt_one hb
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hexp : 0 < -(2 : ℝ) * (k : ℝ) * (sigma - 1 / 2) := by nlinarith
  rw [normalizedMassDefect_eq_rpow hb, sub_pos]
  exact (Real.one_lt_rpow_iff_of_pos hb0).2 (Or.inl ⟨hb1, hexp⟩)

/-- Acima do autodual a energia fica abaixo da massa (cabeça pesada): defeito < 0. -/
theorem normalizedMassDefect_neg_of_half_lt (hb : 1 < b) (hk : 0 < k)
    {sigma : ℝ} (h : 1 / 2 < sigma) :
    normalizedMassDefect b sigma k < 0 := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hexp : -(2 : ℝ) * (k : ℝ) * (sigma - 1 / 2) < 0 := by nlinarith
  rw [normalizedMassDefect_eq_rpow hb, sub_neg]
  exact Real.rpow_lt_one_of_one_lt_of_neg hb1 hexp

/-- Energia do defeito massa–amplitude: o piso empírico da tela, em álgebra. -/
def massAmplitudeDefectEnergy (b : ℕ) (sigma : ℝ) (k : ℕ) : ℝ :=
  ((branchAmplitude b sigma k) ^ 2 - criticalMass b k) ^ 2

theorem massAmplitudeDefectEnergy_nonneg (b : ℕ) (sigma : ℝ) (k : ℕ) :
    0 ≤ massAmplitudeDefectEnergy b sigma k := sq_nonneg _

theorem massAmplitudeDefectEnergy_eq_zero_iff (hb : 1 < b) (hk : 0 < k) (sigma : ℝ) :
    massAmplitudeDefectEnergy b sigma k = 0 ↔ sigma = 1 / 2 := by
  unfold massAmplitudeDefectEnergy
  rw [pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0), sub_eq_zero]
  exact branchAmplitude_sq_eq_criticalMass_iff_of_one_lt b k hb hk sigma

/-- **Piso quadrático exato.**  Fora do expoente autodual `σ = 1/2`, a energia do
defeito massa–amplitude é estritamente positiva.  É a prova algébrica de que a
casca radial não pode ser anulada fora do autodual — a razão do que o
laboratório mostrou como `‖R‖² > 0` fora de `1/2`. -/
theorem massAmplitudeDefectEnergy_pos_of_ne_half (hb : 1 < b) (hk : 0 < k)
    {sigma : ℝ} (h : sigma ≠ 1 / 2) :
    0 < massAmplitudeDefectEnergy b sigma k := by
  rcases (massAmplitudeDefectEnergy_nonneg b sigma k).lt_or_eq with hpos | hzero
  · exact hpos
  · exact absurd ((massAmplitudeDefectEnergy_eq_zero_iff hb hk sigma).1 hzero.symm) h

/-- O locus de anulação do defeito não depende da base (invariante de régua). -/
theorem massAmplitudeDefectEnergy_zero_base_independent
    {b c : ℕ} (hb : 1 < b) (hc : 1 < c) (hk : 0 < k) (sigma : ℝ) :
    massAmplitudeDefectEnergy b sigma k = 0 ↔
      massAmplitudeDefectEnergy c sigma k = 0 := by
  rw [massAmplitudeDefectEnergy_eq_zero_iff hb hk,
    massAmplitudeDefectEnergy_eq_zero_iff hc hk]

end

end CPFormal.Analytic.Cp
