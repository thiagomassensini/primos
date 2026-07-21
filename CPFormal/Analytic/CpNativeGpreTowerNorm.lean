import CPFormal.Analytic.CpNativeGpreTowerLift
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Norma da torre nativa de G_pre

Este modulo formaliza a parte material do majorante 0.52. O perfil
`h_(p,tau,j)=p^(-j*tau)/j` e construido como vetor de ell^2. Para tempos
positivos, sua norma quadrada e majorada por `(4/3) p^(-2*tau)`; no endpoint
`tau=0`, uma soma telescopica fornece a cota `2` sem usar uma avaliacao
fechada da serie de Basel.

O componente de fluxo `N h` vive em H^-1. Ao transportar essa norma para
coordenadas de contagem, dividir pelo nivel `j` recupera exatamente o mesmo
coeficiente do componente de valor, inclusive no endpoint. Tambem registramos
que a completacao reciproca e contrativa e que cada produto de canto e no
maximo `8 e^2`.

Nenhuma hipotese espectral, zero Genuine ou lei Green entra neste arquivo.
-/
open scoped BigOperators ENNReal NNReal

namespace CPFormal.Analytic.Cp

noncomputable section



theorem nativeUnitMassTowerProfile_pow_identity (p j tau : ℕ) :
    (((p : ℝ) ^ (j * tau))⁻¹) ^ 2 =
      (((p : ℝ) ^ (2 * tau))⁻¹) ^ j := by
  calc
    (((p : ℝ) ^ (j * tau))⁻¹) ^ 2 =
        ((p : ℝ)⁻¹) ^ ((j * tau) * 2) := by
      rw [← inv_pow, ← pow_mul]
    _ = ((p : ℝ)⁻¹) ^ ((2 * tau) * j) := by
      congr 1
      ring
    _ = (((p : ℝ)⁻¹) ^ (2 * tau)) ^ j := by
      rw [pow_mul]
    _ = (((p : ℝ) ^ (2 * tau))⁻¹) ^ j := by
      rw [inv_pow]

theorem nativeUnitMassTowerProfile_sq_le_geometric (p j tau : ℕ) :
    nativeUnitMassTowerProfile p tau j ^ 2 ≤
      (((p : ℝ) ^ (2 * tau))⁻¹) ^ j := by
  by_cases hj : j = 0
  · subst j
    simp
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
  rw [nativeUnitMassTowerProfile, if_neg hj, div_pow]
  rw [← nativeUnitMassTowerProfile_pow_identity p j tau]
  exact div_le_self (sq_nonneg _) (by nlinarith)

theorem nativeGpreGeometricRatio_le_quarter
    (p tau : ℕ) (hp : 2 ≤ p) (htau : 1 ≤ tau) :
    ((p : ℝ) ^ (2 * tau))⁻¹ ≤ (1 / 4 : ℝ) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hbase : (1 : ℝ) ≤ p := le_trans (by norm_num) hpR
  have hexp : 2 ≤ 2 * tau := by omega
  have hfour : (4 : ℝ) ≤ (p : ℝ) ^ (2 * tau) := by
    calc
      (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (p : ℝ) ^ 2 := by gcongr
      _ ≤ (p : ℝ) ^ (2 * tau) := pow_le_pow_right₀ hbase hexp
  rw [one_div]
  exact (inv_le_inv₀
    (a := (p : ℝ) ^ (2 * tau)) (b := (4 : ℝ))
    (by positivity) (by norm_num)).2 hfour

theorem nativeUnitMassTowerProfile_sq_summable_of_pos
    (p tau : ℕ) (hp : 2 ≤ p) (htau : 1 ≤ tau) :
    Summable (fun j : ℕ => nativeUnitMassTowerProfile p tau j ^ 2) := by
  let q : ℝ := ((p : ℝ) ^ (2 * tau))⁻¹
  have hq0 : 0 ≤ q := by positivity
  have hq4 : q ≤ (1 / 4 : ℝ) := nativeGpreGeometricRatio_le_quarter p tau hp htau
  have hq1 : q < 1 := lt_of_le_of_lt hq4 (by norm_num)
  exact Summable.of_nonneg_of_le
    (fun j => sq_nonneg (nativeUnitMassTowerProfile p tau j))
    (fun j => nativeUnitMassTowerProfile_sq_le_geometric p j tau)
    (summable_geometric_of_lt_one hq0 hq1)

theorem nativeUnitMassTowerProfile_sq_tsum_le_of_pos
    (p tau : ℕ) (hp : 2 ≤ p) (htau : 1 ≤ tau) :
    (∑' j : ℕ, nativeUnitMassTowerProfile p tau j ^ 2) ≤
      (4 / 3 : ℝ) * ((p : ℝ) ^ (2 * tau))⁻¹ := by
  let q : ℝ := ((p : ℝ) ^ (2 * tau))⁻¹
  let f : ℕ → ℝ := fun j => nativeUnitMassTowerProfile p tau j ^ 2
  have hq0 : 0 ≤ q := by positivity
  have hq4 : q ≤ (1 / 4 : ℝ) := nativeGpreGeometricRatio_le_quarter p tau hp htau
  have hq1 : q < 1 := lt_of_le_of_lt hq4 (by norm_num)
  have hf : Summable f := nativeUnitMassTowerProfile_sq_summable_of_pos p tau hp htau
  have hgeom : Summable (fun j : ℕ => q ^ j) :=
    summable_geometric_of_lt_one hq0 hq1
  have hfshift : (∑' j : ℕ, f j) = ∑' j : ℕ, f (j + 1) := by
    have h := hf.sum_add_tsum_nat_add 1
    rw [Finset.sum_range_one] at h
    calc
      (∑' j : ℕ, f j) = f 0 + ∑' j : ℕ, f (j + 1) := h.symm
      _ = ∑' j : ℕ, f (j + 1) := by
        simp [f, nativeUnitMassTowerProfile]
  have hle : (∑' j : ℕ, f (j + 1)) ≤ ∑' j : ℕ, q ^ (j + 1) := by
    exact Summable.tsum_le_tsum
      (fun j => nativeUnitMassTowerProfile_sq_le_geometric p (j + 1) tau)
      ((summable_nat_add_iff 1).2 hf)
      ((summable_nat_add_iff 1).2 hgeom)
  have hgeomSum : (∑' j : ℕ, q ^ (j + 1)) = q * (1 - q)⁻¹ := by
    simp_rw [pow_succ']
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  have hden : (3 / 4 : ℝ) ≤ 1 - q := by linarith
  have hdenpos : 0 < 1 - q := sub_pos.mpr hq1
  have hinv : (1 - q)⁻¹ ≤ (4 / 3 : ℝ) := by
    rw [show (4 / 3 : ℝ) = (3 / 4 : ℝ)⁻¹ by norm_num]
    exact (inv_le_inv₀ hdenpos (by norm_num : (0 : ℝ) < 3 / 4)).2 hden
  rw [hfshift]
  calc
    (∑' j : ℕ, f (j + 1)) ≤ ∑' j : ℕ, q ^ (j + 1) := hle
    _ = q * (1 - q)⁻¹ := hgeomSum
    _ ≤ q * (4 / 3 : ℝ) := mul_le_mul_of_nonneg_left hinv hq0
    _ = (4 / 3 : ℝ) * ((p : ℝ) ^ (2 * tau))⁻¹ := by
      dsimp [q]
      ring

theorem nativeUnitMassTowerProfile_zero_sq_eq (p j : ℕ) :
    nativeUnitMassTowerProfile p 0 j ^ 2 = ((j : ℝ) ^ 2)⁻¹ := by
  by_cases hj : j = 0
  · subst j
    simp
  rw [nativeUnitMassTowerProfile_zero_time p j hj]
  rw [← inv_pow]

def nativeGpreTelescopingSquareMajorant (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2)

theorem nativeGpreTelescopingSquareMajorant_nonneg (n : ℕ) :
    0 ≤ nativeGpreTelescopingSquareMajorant n := by
  unfold nativeGpreTelescopingSquareMajorant
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : (n : ℝ) + 1 ≤ (n : ℝ) + 2 := by linarith
  exact sub_nonneg.mpr (one_div_le_one_div_of_le h1 h2)

theorem nativeGpreTelescopingSquareMajorant_hasSum :
    HasSum nativeGpreTelescopingSquareMajorant 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg nativeGpreTelescopingSquareMajorant_nonneg]
  have hpartial : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, nativeGpreTelescopingSquareMajorant n) =
        1 - 1 / ((N : ℝ) + 1) := by
    intro N
    let a : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
    calc
      (∑ n ∈ Finset.range N, nativeGpreTelescopingSquareMajorant n) =
          ∑ n ∈ Finset.range N, (a n - a (n + 1)) := by
        apply Finset.sum_congr rfl
        intro n hn
        dsimp [a, nativeGpreTelescopingSquareMajorant]
        congr 2
        push_cast
        ring
      _ = a 0 - a N := Finset.sum_range_sub' a N
      _ = 1 - 1 / ((N : ℝ) + 1) := by simp [a]
  simp_rw [hpartial]
  simpa using
    (tendsto_const_nhds.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))

theorem nativeGpreShiftedInverseSquare_le_telescoping (n : ℕ) :
    (((n : ℝ) + 2) ^ 2)⁻¹ ≤ nativeGpreTelescopingSquareMajorant n := by
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hrewrite : nativeGpreTelescopingSquareMajorant n =
      1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
    unfold nativeGpreTelescopingSquareMajorant
    field_simp
    ring
  rw [hrewrite]
  rw [inv_eq_one_div]
  apply one_div_le_one_div_of_le (mul_pos h1 h2)
  nlinarith

theorem nativeGpreShiftedInverseSquare_summable :
    Summable (fun n : ℕ => (((n : ℝ) + 2) ^ 2)⁻¹) := by
  exact Summable.of_nonneg_of_le
    (fun n => by positivity)
    nativeGpreShiftedInverseSquare_le_telescoping
    nativeGpreTelescopingSquareMajorant_hasSum.summable

theorem nativeGpreShiftedInverseSquare_tsum_le_one :
    (∑' n : ℕ, (((n : ℝ) + 2) ^ 2)⁻¹) ≤ 1 := by
  calc
    (∑' n : ℕ, (((n : ℝ) + 2) ^ 2)⁻¹) ≤
        ∑' n : ℕ, nativeGpreTelescopingSquareMajorant n :=
      Summable.tsum_le_tsum
        nativeGpreShiftedInverseSquare_le_telescoping
        nativeGpreShiftedInverseSquare_summable
        nativeGpreTelescopingSquareMajorant_hasSum.summable
    _ = 1 := nativeGpreTelescopingSquareMajorant_hasSum.tsum_eq

theorem nativeUnitMassTowerProfile_zero_sq_summable (p : ℕ) :
    Summable (fun j : ℕ => nativeUnitMassTowerProfile p 0 j ^ 2) := by
  let f : ℕ → ℝ := fun j => nativeUnitMassTowerProfile p 0 j ^ 2
  have htail : Summable (fun n : ℕ => f (n + 2)) := by
    refine nativeGpreShiftedInverseSquare_summable.congr ?_
    intro n
    dsimp [f]
    rw [nativeUnitMassTowerProfile_zero_sq_eq]
    norm_cast
  exact (summable_nat_add_iff 2).1 htail

theorem nativeUnitMassTowerProfile_zero_sq_tsum_le_two (p : ℕ) :
    (∑' j : ℕ, nativeUnitMassTowerProfile p 0 j ^ 2) ≤ 2 := by
  let f : ℕ → ℝ := fun j => nativeUnitMassTowerProfile p 0 j ^ 2
  have hf : Summable f := nativeUnitMassTowerProfile_zero_sq_summable p
  have hsplit := hf.sum_add_tsum_nat_add 2
  have htail : (∑' n : ℕ, f (n + 2)) ≤ 1 := by
    have heq : (fun n : ℕ => f (n + 2)) =
        fun n : ℕ => (((n : ℝ) + 2) ^ 2)⁻¹ := by
      funext n
      dsimp [f]
      rw [nativeUnitMassTowerProfile_zero_sq_eq]
      norm_cast
    rw [heq]
    exact nativeGpreShiftedInverseSquare_tsum_le_one
  have hhead : (∑ j ∈ Finset.range 2, f j) = 1 := by
    norm_num [Finset.sum_range_succ, f, nativeUnitMassTowerProfile]
  rw [hhead] at hsplit
  linarith

theorem nativeUnitMassTowerProfile_sq_summable (p tau : ℕ) :
    Summable (fun j : ℕ => nativeUnitMassTowerProfile p tau j ^ 2) := by
  by_cases htau : tau = 0
  · subst tau
    exact nativeUnitMassTowerProfile_zero_sq_summable p
  by_cases hp0 : p = 0
  · subst p
    have hzero : (fun j : ℕ => nativeUnitMassTowerProfile 0 tau j ^ 2) = 0 := by
      funext j
      by_cases hj : j = 0
      · subst j
        simp
      · have hjtau : j * tau ≠ 0 := Nat.mul_ne_zero hj htau
        simp [nativeUnitMassTowerProfile, hj, hjtau]
    rw [hzero]
    exact summable_zero
  by_cases hp1 : p = 1
  · subst p
    refine (nativeUnitMassTowerProfile_zero_sq_summable 1).congr ?_
    intro j
    by_cases hj : j = 0
    · subst j
      simp
    · simp [nativeUnitMassTowerProfile, hj]
  have hp : 2 ≤ p := by omega
  exact nativeUnitMassTowerProfile_sq_summable_of_pos p tau hp (Nat.one_le_iff_ne_zero.mpr htau)

abbrev NativeGpreTowerHilbert := lp (fun _ : ℕ => ℝ) 2

noncomputable def nativeGpreTowerProfileVector (p tau : ℕ) : NativeGpreTowerHilbert :=
  let f : PreLp (fun _ : ℕ => ℝ) :=
    fun j => nativeUnitMassTowerProfile p tau j
  ⟨f, by
    change Memℓp f 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    simpa [Real.norm_eq_abs, sq_abs] using nativeUnitMassTowerProfile_sq_summable p tau⟩

@[simp] theorem nativeGpreTowerProfileVector_apply (p tau j : ℕ) :
    nativeGpreTowerProfileVector p tau j = nativeUnitMassTowerProfile p tau j := rfl

theorem nativeGpreTowerProfileVector_norm_sq (p tau : ℕ) :
    ‖nativeGpreTowerProfileVector p tau‖ ^ 2 =
      ∑' j : ℕ, nativeUnitMassTowerProfile p tau j ^ 2 := by
  have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num)
    (nativeGpreTowerProfileVector p tau)
  simpa [Real.norm_eq_abs, sq_abs] using h.tsum_eq.symm

theorem nativeGpreTowerProfileVector_norm_sq_le_of_pos
    (p tau : ℕ) (hp : 2 ≤ p) (htau : 1 ≤ tau) :
    ‖nativeGpreTowerProfileVector p tau‖ ^ 2 ≤
      (4 / 3 : ℝ) * ((p : ℝ) ^ (2 * tau))⁻¹ := by
  rw [nativeGpreTowerProfileVector_norm_sq]
  exact nativeUnitMassTowerProfile_sq_tsum_le_of_pos p tau hp htau

theorem nativeGpreTowerProfileVector_zero_norm_sq_le_two (p : ℕ) :
    ‖nativeGpreTowerProfileVector p 0‖ ^ 2 ≤ 2 := by
  rw [nativeGpreTowerProfileVector_norm_sq]
  exact nativeUnitMassTowerProfile_zero_sq_tsum_le_two p

def nativeGpreContextAsValue (c : NativeGpreContext) : NativeGpreContext :=
  { c with role := .value }

noncomputable def nativeGpreGraphNormCoordinateCoefficient
    (c : NativeGpreContext) : ℝ :=
  match c.role with
  | .value => nativeGpreTowerCoordinateCoefficient c
  | .numberFlux =>
      if c.towerLevel.val = 0 then 0
      else nativeGpreTowerCoordinateCoefficient c / c.towerLevel.val

theorem nativeGpreGraphNormCoordinateCoefficient_eq_value (c : NativeGpreContext) :
    nativeGpreGraphNormCoordinateCoefficient c =
      nativeGpreTowerCoordinateCoefficient (nativeGpreContextAsValue c) := by
  cases hrole : c.role with
  | value =>
      cases c
      simp_all [nativeGpreGraphNormCoordinateCoefficient, nativeGpreContextAsValue]
  | numberFlux =>
      by_cases hj : c.towerLevel.val = 0
      · simp [nativeGpreGraphNormCoordinateCoefficient, nativeGpreContextAsValue, hrole, hj,
          nativeGpreTowerCoordinateCoefficient, nativeUnitMassTowerProfile]
      · by_cases hcell : c.cell = 0
        · simp [nativeGpreGraphNormCoordinateCoefficient, nativeGpreContextAsValue, hrole, hj,
            nativeGpreTowerCoordinateCoefficient, hcell]
        · by_cases htower :
            c.towerPrime.val = c.arithmeticPrime.val
          · let u := nativeGpreCornerU c.cell c.corner
            let v := nativeGpreCornerV c.cell c.corner
            by_cases hd : c.jordanDivisor.val ∣ Nat.gcd u v
            · simp [nativeGpreGraphNormCoordinateCoefficient, nativeGpreContextAsValue, hrole, hj,
                nativeGpreTowerCoordinateCoefficient, hcell, htower, hd,
                u, v, nativeGpreGraphRoleFactor]
            · simp [nativeGpreGraphNormCoordinateCoefficient, nativeGpreContextAsValue, hrole, hj,
                nativeGpreTowerCoordinateCoefficient, hcell, htower, hd,
                u, v]
          · simp [nativeGpreGraphNormCoordinateCoefficient, nativeGpreContextAsValue, hrole, hj,
              nativeGpreTowerCoordinateCoefficient, hcell, htower]

theorem nativeGpreCornerV_le_cornerU
    (e : ℕ) (he : e ≠ 0) (corner : GpreCorner) :
    nativeGpreCornerV e corner ≤ nativeGpreCornerU e corner := by
  have he1 : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr he
  cases corner <;> simp [nativeGpreCornerU, nativeGpreCornerV] <;> omega

theorem nativeGpreOrientationFactor_abs_le_one
    (e : ℕ) (he : e ≠ 0) (corner : GpreCorner)
    (orientation : GpreOrientation) :
    |nativeGpreOrientationFactor e corner orientation| ≤ 1 := by
  cases orientation with
  | original => simp [nativeGpreOrientationFactor]
  | reciprocal =>
      have huNat : nativeGpreCornerU e corner ≠ 0 :=
        nativeGpreCornerU_ne_zero e he corner
      have hu : (0 : ℝ) < nativeGpreCornerU e corner := by
        exact_mod_cast Nat.pos_of_ne_zero huNat
      have hv : (0 : ℝ) ≤ nativeGpreCornerV e corner := by positivity
      have hvu :
          (nativeGpreCornerV e corner : ℝ) ≤ nativeGpreCornerU e corner := by
        exact_mod_cast nativeGpreCornerV_le_cornerU e he corner
      rw [nativeGpreOrientationFactor, abs_neg, abs_of_nonneg (div_nonneg hv hu.le)]
      exact (div_le_one hu).2 hvu

theorem nativeGpreCornerProduct_le_eight_square
    (e : ℕ) (he : e ≠ 0) (corner : GpreCorner) :
    nativeGpreCornerU e corner * nativeGpreCornerV e corner ≤ 8 * e ^ 2 := by
  have he1 : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr he
  cases corner <;> simp [nativeGpreCornerU, nativeGpreCornerV] <;> nlinarith


end
end CPFormal.Analytic.Cp

