import CPFormal.Analytic.CpBranchNorm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Rigidez quadratica posicional antes de primos e complexificacao

Este modulo isola a origem nativa do expoente `1/2`. A unica entrada e a
geometria de carry em uma base posicional natural `b > 1`:

* uma coordenada na profundidade `k` possui massa `b^(-k)`;
* uma familia deformada de amplitudes possui peso `b^(-k sigma)`;
* energia e o quadrado real da amplitude.

Em qualquer profundidade positiva, compatibilidade entre a energia deformada
e a massa de carry equivale a `sigma = 1/2`. O resultado nao exige que `b`
seja primo.

Tambem realizamos a amplitude em `R x R`. A direcao pode ser qualquer vetor
unitario; em particular, `(cos theta, sin theta)`. A energia nao depende de
`theta`. Assim, fase/rotacao e massa quadratica aparecem como dados
formalmente separados, sem numero complexo.

Finalmente, a norma geometrica global do ramo e tratada para toda base
`b > 1`. Todas as bases possuem o mesmo locus de saturacao. Primalidade pode
ser usada para escolher uma familia minima de cameras, mas nao participa da
rigidez quadratica.
-/

open scoped BigOperators

namespace CPFormal.Analytic.Cp

open CPFormal.Carry.Cp

noncomputable section

/-! ## Rigidez local da amplitude de carry -/

/--
Em qualquer base posicional nao degenerada e em qualquer profundidade
positiva, o quadrado de `b^(-k sigma)` coincide com a massa `b^(-k)` se, e
somente se, `sigma = 1/2`.
-/
theorem branchAmplitude_sq_eq_criticalMass_iff_of_one_lt
    (b k : ℕ) (hb : 1 < b) (hk : 0 < k) (sigma : ℝ) :
    (branchAmplitude b sigma k) ^ 2 = criticalMass b k ↔
      sigma = (1 : ℝ) / 2 := by
  have hb0 : 0 < (b : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hb)
  have hb1 : (b : ℝ) ≠ 1 := by
    exact_mod_cast (ne_of_gt hb)
  have hk0 : 0 < (k : ℝ) := by
    exact_mod_cast hk
  constructor
  · intro hmass
    unfold branchAmplitude criticalMass at hmass
    rw [← Real.rpow_mul_natCast (le_of_lt hb0)
      (-((k : ℝ)) * sigma) 2] at hmass
    have hexponent :
        (-((k : ℝ)) * sigma) * (2 : ℝ) = -((k : ℝ)) :=
      (Real.rpow_right_inj hb0 hb1).mp hmass
    nlinarith
  · intro hsigma
    subst sigma
    rw [branchAmplitude_half]
    exact criticalAmplitude_sq_eq_mass b k

/--
Um expoente e admissivel para a geometria posicional quando sua energia
reproduz a massa de carry em toda profundidade positiva.
-/
def PositionalCarryMassCompatible (b : ℕ) (sigma : ℝ) : Prop :=
  ∀ k : ℕ, 0 < k →
    (branchAmplitude b sigma k) ^ 2 = criticalMass b k

/--
O dominio de expoentes compativeis com a massa de carry e o singleton
`{1/2}`. Basta uma profundidade positiva para obter a reciproca.
-/
theorem positionalCarryMassCompatible_iff
    (b : ℕ) (hb : 1 < b) (sigma : ℝ) :
    PositionalCarryMassCompatible b sigma ↔
      sigma = (1 : ℝ) / 2 := by
  constructor
  · intro hcompatible
    exact
      (branchAmplitude_sq_eq_criticalMass_iff_of_one_lt
        b 1 hb (by norm_num) sigma).mp
        (hcompatible 1 (by norm_num))
  · intro hsigma
    subst sigma
    intro k hk
    rw [branchAmplitude_half]
    exact criticalAmplitude_sq_eq_mass b k

/-! ## Realizacao em plano real e invariancia de fase -/

/-- Plano real de amplitudes, sem estrutura complexa. -/
abbrev PositionalAmplitudePlane := ℝ × ℝ

/-- Energia quadratica euclidiana no plano real de amplitudes. -/
def positionalPlaneEnergy (u : PositionalAmplitudePlane) : ℝ :=
  u.1 ^ 2 + u.2 ^ 2

/-- Direcao real de angulo `theta`. -/
def realRotationDirection (theta : ℝ) : PositionalAmplitudePlane :=
  (Real.cos theta, Real.sin theta)

/-- A direcao de rotacao real possui energia unitaria. -/
@[simp] theorem positionalPlaneEnergy_realRotationDirection
    (theta : ℝ) :
    positionalPlaneEnergy (realRotationDirection theta) = 1 := by
  unfold positionalPlaneEnergy realRotationDirection
  rw [add_comm, Real.sin_sq_add_cos_sq]

/-- Casca de amplitude em uma direcao real arbitraria. -/
def positionalBranchShell
    (b : ℕ) (sigma : ℝ) (k : ℕ)
    (u : PositionalAmplitudePlane) :
    PositionalAmplitudePlane :=
  (branchAmplitude b sigma k * u.1,
    branchAmplitude b sigma k * u.2)

/-- Escalar uma direcao multiplica sua energia pelo quadrado da amplitude. -/
theorem positionalPlaneEnergy_positionalBranchShell
    (b : ℕ) (sigma : ℝ) (k : ℕ)
    (u : PositionalAmplitudePlane) :
    positionalPlaneEnergy (positionalBranchShell b sigma k u) =
      (branchAmplitude b sigma k) ^ 2 * positionalPlaneEnergy u := by
  unfold positionalPlaneEnergy positionalBranchShell
  ring

/--
Em qualquer direcao unitaria, a energia da casca e exatamente o peso
quadratico do ramo.
-/
theorem positionalPlaneEnergy_shell_eq_branchMassWeight
    (b : ℕ) (sigma : ℝ) (k : ℕ)
    (u : PositionalAmplitudePlane)
    (hu : positionalPlaneEnergy u = 1) :
    positionalPlaneEnergy (positionalBranchShell b sigma k u) =
      branchMassWeight b sigma k := by
  rw [positionalPlaneEnergy_positionalBranchShell, hu, mul_one]
  exact branchAmplitude_sq_eq_massWeight b sigma k

/--
Para a orbita real `cos`/`sin`, a energia nao depende do angulo.
-/
@[simp] theorem positionalPlaneEnergy_rotatedShell_eq_branchMassWeight
    (b : ℕ) (sigma theta : ℝ) (k : ℕ) :
    positionalPlaneEnergy
        (positionalBranchShell b sigma k (realRotationDirection theta)) =
      branchMassWeight b sigma k := by
  exact positionalPlaneEnergy_shell_eq_branchMassWeight
    b sigma k (realRotationDirection theta)
    (positionalPlaneEnergy_realRotationDirection theta)

/--
Rigidez local no plano real: para qualquer angulo, igualar a energia da casca
a massa de carry equivale a `sigma = 1/2`.
-/
theorem positionalPlaneEnergy_rotatedShell_eq_criticalMass_iff
    (b k : ℕ) (hb : 1 < b) (hk : 0 < k)
    (sigma theta : ℝ) :
    positionalPlaneEnergy
        (positionalBranchShell b sigma k (realRotationDirection theta)) =
        criticalMass b k ↔
      sigma = (1 : ℝ) / 2 := by
  rw [positionalPlaneEnergy_rotatedShell_eq_branchMassWeight]
  rw [← branchAmplitude_sq_eq_massWeight]
  exact branchAmplitude_sq_eq_criticalMass_iff_of_one_lt
    b k hb hk sigma

/-! ## Saturacao global sem hipotese de primalidade -/

/-- A razao quadratica e positiva em toda base `b > 1`. -/
theorem branchRatio_pos_of_one_lt
    (b : ℕ) (hb : 1 < b) (sigma : ℝ) :
    0 < branchRatio b sigma := by
  unfold branchRatio
  apply Real.rpow_pos_of_pos
  exact_mod_cast (lt_trans Nat.zero_lt_one hb)

/-- Para `sigma > 0`, a razao quadratica esta abaixo de um em toda base. -/
theorem branchRatio_lt_one_of_one_lt
    (b : ℕ) (hb : 1 < b)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    branchRatio b sigma < 1 := by
  unfold branchRatio
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast hb
  · linarith

/-- Forma em norma da condicao de convergencia geometrica. -/
theorem norm_branchRatio_lt_one_of_one_lt
    (b : ℕ) (hb : 1 < b)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    ‖branchRatio b sigma‖ < 1 := by
  rw [Real.norm_eq_abs,
    abs_of_pos (branchRatio_pos_of_one_lt b hb sigma)]
  exact branchRatio_lt_one_of_one_lt b hb hsigma

/-- Forma fechada da norma do ramo para qualquer base `b > 1`. -/
theorem branchNormSq_eq_closed_of_one_lt
    (b : ℕ) (hb : 1 < b)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    branchNormSq b sigma =
      ((b - 1 : ℕ) : ℝ) * branchRatio b sigma *
        (1 - branchRatio b sigma)⁻¹ := by
  have hnorm :=
    norm_branchRatio_lt_one_of_one_lt b hb hsigma
  unfold branchNormSq branchMassWeight
  rw [← geom_series_mul_shift (branchRatio b sigma) hnorm]
  rw [tsum_geometric_of_norm_lt_one hnorm]
  ring

/--
Com `b-1` pernas, a massa geometrica normalizada vale um exatamente quando
sua razao vale `1/b`; nenhuma fatoracao de `b` e usada.
-/
theorem normalizedGeometricMass_eq_one_iff_of_one_lt
    (b : ℕ) (hb : 1 < b)
    {q : ℝ} (hq : q < 1) :
    ((b - 1 : ℕ) : ℝ) * q * (1 - q)⁻¹ = 1 ↔
      q = (b : ℝ)⁻¹ := by
  have hb0 : (b : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hb))
  have hb1 : (b : ℝ) ≠ 1 := by
    exact_mod_cast (ne_of_gt hb)
  have hden : 1 - q ≠ 0 := by
    linarith
  rw [Nat.cast_sub (Nat.le_of_lt hb), Nat.cast_one]
  constructor
  · intro h
    have hdiv : (((b : ℝ) - 1) * q) / (1 - q) = 1 := by
      simpa [div_eq_mul_inv, mul_assoc] using h
    have hmul : ((b : ℝ) - 1) * q = 1 - q := by
      simpa using (div_eq_iff hden).mp hdiv
    have hqb : q * (b : ℝ) = 1 := by
      nlinarith
    simpa only [one_div] using (eq_div_iff hb0).2 hqb
  · intro hqeq
    rw [hqeq]
    field_simp [hb0, hb1]

/-- A razao `b^(-2 sigma)` vale `1/b` somente em `sigma = 1/2`. -/
theorem branchRatio_eq_inv_iff_of_one_lt
    (b : ℕ) (hb : 1 < b) (sigma : ℝ) :
    branchRatio b sigma = (b : ℝ)⁻¹ ↔
      sigma = (1 : ℝ) / 2 := by
  have hb0 : 0 < (b : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hb)
  have hb1 : (b : ℝ) ≠ 1 := by
    exact_mod_cast (ne_of_gt hb)
  constructor
  · intro hratio
    have hpow :
        (b : ℝ) ^ (-2 * sigma) =
          (b : ℝ) ^ (-1 : ℝ) := by
      simpa [branchRatio, Real.rpow_neg_one] using hratio
    have hexponent : -2 * sigma = (-1 : ℝ) :=
      (Real.rpow_right_inj hb0 hb1).mp hpow
    linarith
  · intro hsigma
    subst sigma
    exact branchRatio_half b

/--
Coracao global sem primalidade: no semiplano de convergencia, a norma
quadratica do ramo vale um exatamente em `sigma = 1/2`.
-/
theorem branchNormSq_eq_one_iff_of_one_lt
    (b : ℕ) (hb : 1 < b)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    branchNormSq b sigma = 1 ↔
      sigma = (1 : ℝ) / 2 := by
  rw [branchNormSq_eq_closed_of_one_lt b hb hsigma]
  rw [normalizedGeometricMass_eq_one_iff_of_one_lt b hb
    (branchRatio_lt_one_of_one_lt b hb hsigma)]
  exact branchRatio_eq_inv_iff_of_one_lt b hb sigma

/--
Invariancia multibase do locus de saturacao: duas bases posicionais
arbitrarias veem exatamente o mesmo expoente admissivel.
-/
theorem branchNormSq_eq_one_base_independent
    (b c : ℕ) (hb : 1 < b) (hc : 1 < c)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    branchNormSq b sigma = 1 ↔
      branchNormSq c sigma = 1 := by
  rw [branchNormSq_eq_one_iff_of_one_lt b hb hsigma,
    branchNormSq_eq_one_iff_of_one_lt c hc hsigma]

end

end CPFormal.Analytic.Cp
