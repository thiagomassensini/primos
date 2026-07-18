import CPFormal.Carry.CpBranchWeight
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Norma quadratica do operador de ramo `Cₚ`

Para primo impar `p`, a camera possui `p-1` pernas e a profundidade inicial e
`1`. A massa quadratica do operador de ramo puro e portanto definida pela
serie, e nao pela sua forma fechada,

`(p-1) * sum_{k >= 1} p^(-2 k sigma)`.

Este arquivo prova a soma geometrica, a saturacao em `sigma = 1/2` e a
reciproca: para `sigma > 0`, a norma quadratica vale `1` se, e somente se,
`sigma = 1/2`.

O deslocamento critico `sigma - 1/2` e registrado como mediador entre o
defeito da norma e o futuro tilt transversal. Nenhuma implicacao a partir de
zeros Genuine e assumida aqui; a interface final deixa essa ponte explicita.
-/

open scoped BigOperators Topology

namespace CPFormal.Analytic.Cp

open CPFormal.Carry.Cp

noncomputable section

/-- Norma quadratica do ramo puro, definida pela serie de todas as profundidades. -/
def branchNormSq (p : ℕ) (sigma : ℝ) : ℝ :=
  ((p - 1 : ℕ) : ℝ) *
    ∑' k : ℕ, branchMassWeight p sigma (k + 1)

/-- Defeito em relacao a saturacao unitaria. -/
def branchDefect (p : ℕ) (sigma : ℝ) : ℝ :=
  branchNormSq p sigma - 1

/-- Coordenada transversal comum: distancia assinada ate a linha critica. -/
def criticalDisplacement (sigma : ℝ) : ℝ :=
  sigma - (1 : ℝ) / 2

/-- A razao geometrica e positiva para uma base prima. -/
theorem branchRatio_pos (p : ℕ) (hp : Nat.Prime p) (sigma : ℝ) :
    0 < branchRatio p sigma := by
  unfold branchRatio
  apply Real.rpow_pos_of_pos
  exact_mod_cast hp.pos

/-- Para `sigma > 0`, a razao quadratica esta estritamente abaixo de um. -/
theorem branchRatio_lt_one
    (p : ℕ) (hp : Nat.Prime p) {sigma : ℝ} (hsigma : 0 < sigma) :
    branchRatio p sigma < 1 := by
  unfold branchRatio
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast hp.one_lt
  · linarith

/-- Forma em norma da hipotese usada pela serie geometrica da Mathlib. -/
theorem norm_branchRatio_lt_one
    (p : ℕ) (hp : Nat.Prime p) {sigma : ℝ} (hsigma : 0 < sigma) :
    ‖branchRatio p sigma‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (branchRatio_pos p hp sigma)]
  exact branchRatio_lt_one p hp hsigma

/-- Forma fechada da serie da norma quadratica. -/
theorem branchNormSq_eq_closed
    (p : ℕ) (hp : Nat.Prime p) {sigma : ℝ} (hsigma : 0 < sigma) :
    branchNormSq p sigma =
      ((p - 1 : ℕ) : ℝ) * branchRatio p sigma *
        (1 - branchRatio p sigma)⁻¹ := by
  have hnorm := norm_branchRatio_lt_one p hp hsigma
  unfold branchNormSq branchMassWeight
  rw [← geom_series_mul_shift (branchRatio p sigma) hnorm]
  rw [tsum_geometric_of_norm_lt_one hnorm]
  ring

/-- Na meia abscissa, a razao quadratica e exatamente `1/p`. -/
@[simp] theorem branchRatio_half (p : ℕ) :
    branchRatio p ((1 : ℝ) / 2) = (p : ℝ)⁻¹ := by
  unfold branchRatio
  convert Real.rpow_neg_one (p : ℝ) using 1 <;> ring

/--
Lema algebrico: com `p-1` pernas, a massa geometrica normalizada vale um
exatamente quando sua razao vale `1/p`.
-/
theorem normalizedGeometricMass_eq_one_iff
    (p : ℕ) (hp : Nat.Prime p) {q : ℝ} (hq : q < 1) :
    ((p - 1 : ℕ) : ℝ) * q * (1 - q)⁻¹ = 1 ↔
      q = (p : ℝ)⁻¹ := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast hp.ne_one
  have hden : 1 - q ≠ 0 := by linarith
  rw [Nat.cast_sub hp.one_le, Nat.cast_one]
  constructor
  · intro h
    have hdiv : (((p : ℝ) - 1) * q) / (1 - q) = 1 := by
      simpa [div_eq_mul_inv, mul_assoc] using h
    have hmul : ((p : ℝ) - 1) * q = 1 - q := by
      simpa using (div_eq_iff hden).mp hdiv
    apply (eq_div_iff hp0).2
    change q * (p : ℝ) = 1
    nlinarith
  · intro hqeq
    rw [hqeq]
    field_simp [hp0, hp1]

/-- A razao `p^(-2 sigma)` vale `1/p` somente na meia abscissa. -/
theorem branchRatio_eq_inv_iff
    (p : ℕ) (hp : Nat.Prime p) (sigma : ℝ) :
    branchRatio p sigma = (p : ℝ)⁻¹ ↔
      sigma = (1 : ℝ) / 2 := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast hp.ne_one
  constructor
  · intro hratio
    have hpow :
        (p : ℝ) ^ (-2 * sigma) = (p : ℝ) ^ (-1 : ℝ) := by
      simpa [branchRatio, Real.rpow_neg_one] using hratio
    have hexponent : -2 * sigma = (-1 : ℝ) :=
      (Real.rpow_right_inj hp0 hp1).mp hpow
    linarith
  · intro hsigma
    subst sigma
    exact branchRatio_half p

/-- A cardinalidade `p-1` da camera satura a norma em `sigma = 1/2`. -/
@[simp] theorem branchNormSq_half (p : ℕ) (hp : Nat.Prime p) :
    branchNormSq p ((1 : ℝ) / 2) = 1 := by
  rw [branchNormSq_eq_closed p hp (by norm_num), branchRatio_half]
  exact (normalizedGeometricMass_eq_one_iff p hp (by
    have hpgt : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    exact inv_lt_one_of_one_lt₀ hpgt)).2 rfl

/--
Coracao quadratico: no semiplano de convergencia, a norma do ramo vale um se,
e somente se, `sigma = 1/2`.
-/
theorem branchNormSq_eq_one_iff
    (p : ℕ) (hp : Nat.Prime p) {sigma : ℝ} (hsigma : 0 < sigma) :
    branchNormSq p sigma = 1 ↔ sigma = (1 : ℝ) / 2 := by
  rw [branchNormSq_eq_closed p hp hsigma]
  rw [normalizedGeometricMass_eq_one_iff p hp
    (branchRatio_lt_one p hp hsigma)]
  exact branchRatio_eq_inv_iff p hp sigma

/-- O defeito da norma e o deslocamento critico possuem exatamente o mesmo zero. -/
theorem branchDefect_eq_zero_iff_criticalDisplacement_eq_zero
    (p : ℕ) (hp : Nat.Prime p) {sigma : ℝ} (hsigma : 0 < sigma) :
    branchDefect p sigma = 0 ↔ criticalDisplacement sigma = 0 := by
  rw [branchDefect, sub_eq_zero]
  rw [branchNormSq_eq_one_iff p hp hsigma]
  simp [criticalDisplacement]

/--
Interface da ponte ainda aberta entre zeros Genuine e saturacao do ramo.
Construir uma instancia exige derivar a saturacao a partir da carta Genuine;
nenhuma instancia e postulada neste modulo.
-/
structure GenuineBranchBridge (p : ℕ) (genuine : ℂ → ℂ) : Prop where
  saturation_of_zero :
    ∀ {s : ℂ}, genuine s = 0 → 0 < s.re → branchNormSq p s.re = 1

/-- Se a ponte Genuine--ramo for construida, a parte real do zero e `1/2`. -/
theorem re_eq_half_of_genuine_zero
    (p : ℕ) (hp : Nat.Prime p) (genuine : ℂ → ℂ)
    (bridge : GenuineBranchBridge p genuine)
    {s : ℂ} (hzero : genuine s = 0) (hre : 0 < s.re) :
    s.re = (1 : ℝ) / 2 := by
  apply (branchNormSq_eq_one_iff p hp hre).mp
  exact bridge.saturation_of_zero hzero hre

end

end CPFormal.Analytic.Cp
