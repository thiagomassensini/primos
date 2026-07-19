import CPFormal.Analytic.CpFiniteGreenRadial

/-!
# Positividade termo a termo da energia Green refletida

Este arquivo fecha a obrigacao de sinal que restou depois da normalizacao
radial. Primeiro abrimos cada aresta do pareamento refletido. Os dois termos
diagonais sao os endpoints positivos `1/(n+1)` e `1/(n+2)`; as partes reais
dos dois termos cruzados sao dominadas por suas normas.

Para `x=n+1`, `y=n+2`, `r=y/x` e `sigma=Re(s)`, a margem estrita reduz-se a

`(1-r^(-sigma)) * (1-r^(sigma-1)) > 0`

no interior `0 < sigma < 1`. A positividade local e entao somada em todo
corte nao vazio e multiplicada pelo cofator radial positivo.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-- Um somador individual do pareamento refletido de gradientes. -/
def finiteReflectedGradientEdge (n : ℕ) (s : ℂ) : ℂ :=
  (starRingEnd ℂ) (positiveDirichletGradient s n) *
    positiveDirichletGradient (reflectedParameter s) n

/-- O gradiente entre vertices consecutivos, escrito pelos valores positivos. -/
theorem positiveDirichletGradient_eq_value_sub_value
    (s : ℂ) (n : ℕ) :
    positiveDirichletGradient s n =
      positiveDirichletValue s (n + 1) - positiveDirichletValue s n := by
  simp [positiveDirichletGradient,
    positiveDirichletValue_eq_natDirichletTerm, Nat.add_assoc]

/-- Norma exata de um valor positivo de Dirichlet. -/
theorem norm_positiveDirichletValue (s : ℂ) (n : ℕ) :
    ‖positiveDirichletValue s n‖ =
      ((n + 1 : ℕ) : ℝ) ^ (-s.re) := by
  have hn : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  simpa [positiveDirichletValue] using
    (Complex.norm_cpow_eq_rpow_re_of_pos hn (-s))

/-- Expansao exata de uma aresta em dois diagonais menos dois cruzados. -/
theorem finiteReflectedGradientEdge_eq_diagonal_sub_cross
    (n : ℕ) (s : ℂ) :
    finiteReflectedGradientEdge n s =
      (((n + 2 : ℕ) : ℂ))⁻¹ + (((n + 1 : ℕ) : ℂ))⁻¹ -
        ((starRingEnd ℂ) (positiveDirichletValue s (n + 1)) *
            positiveDirichletValue (reflectedParameter s) n +
          (starRingEnd ℂ) (positiveDirichletValue s n) *
            positiveDirichletValue (reflectedParameter s) (n + 1)) := by
  have hy := finiteReflectedOuterEndpoint_eq_inv (n + 1) s
  have hx := finiteReflectedOuterEndpoint_eq_inv n s
  unfold finiteReflectedOuterEndpoint at hy hx
  unfold finiteReflectedGradientEdge
  rw [positiveDirichletGradient_eq_value_sub_value,
    positiveDirichletGradient_eq_value_sub_value]
  simp only [map_sub]
  calc
    ((starRingEnd ℂ) (positiveDirichletValue s (n + 1)) -
          (starRingEnd ℂ) (positiveDirichletValue s n)) *
        (positiveDirichletValue (reflectedParameter s) (n + 1) -
          positiveDirichletValue (reflectedParameter s) n) =
      (starRingEnd ℂ) (positiveDirichletValue s (n + 1)) *
          positiveDirichletValue (reflectedParameter s) (n + 1) +
        (starRingEnd ℂ) (positiveDirichletValue s n) *
          positiveDirichletValue (reflectedParameter s) n -
        ((starRingEnd ℂ) (positiveDirichletValue s (n + 1)) *
            positiveDirichletValue (reflectedParameter s) n +
          (starRingEnd ℂ) (positiveDirichletValue s n) *
            positiveDirichletValue (reflectedParameter s) (n + 1)) := by
      ring
    _ = (((n + 2 : ℕ) : ℂ))⁻¹ + (((n + 1 : ℕ) : ℂ))⁻¹ -
        ((starRingEnd ℂ) (positiveDirichletValue s (n + 1)) *
            positiveDirichletValue (reflectedParameter s) n +
          (starRingEnd ℂ) (positiveDirichletValue s n) *
            positiveDirichletValue (reflectedParameter s) (n + 1)) := by
      rw [hy, hx]

/-- Norma do primeiro termo cruzado. -/
theorem norm_reflectedGradientCross_forward (n : ℕ) (s : ℂ) :
    ‖(starRingEnd ℂ) (positiveDirichletValue s (n + 1)) *
        positiveDirichletValue (reflectedParameter s) n‖ =
      ((n + 2 : ℕ) : ℝ) ^ (-s.re) *
        ((n + 1 : ℕ) : ℝ) ^ (s.re - 1) := by
  rw [norm_mul, Complex.norm_conj, norm_positiveDirichletValue,
    norm_positiveDirichletValue]
  simp only [reflectedParameter_re, neg_sub]

/-- Norma do segundo termo cruzado. -/
theorem norm_reflectedGradientCross_backward (n : ℕ) (s : ℂ) :
    ‖(starRingEnd ℂ) (positiveDirichletValue s n) *
        positiveDirichletValue (reflectedParameter s) (n + 1)‖ =
      ((n + 1 : ℕ) : ℝ) ^ (-s.re) *
        ((n + 2 : ℕ) : ℝ) ^ (s.re - 1) := by
  rw [norm_mul, Complex.norm_conj, norm_positiveDirichletValue,
    norm_positiveDirichletValue]
  simp only [reflectedParameter_re, neg_sub]

/-!
Lema real central. Ele contem toda a margem estrita: as normas cruzadas sao
menores que a soma dos dois diagonais para `0 < sigma < 1`.
-/
theorem reflected_rpow_cross_sum_lt_inv_sum
    {x y sigma : ℝ}
    (hx : 0 < x) (hxy : x < y)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    y ^ (-sigma) * x ^ (sigma - 1) +
        x ^ (-sigma) * y ^ (sigma - 1) <
      y⁻¹ + x⁻¹ := by
  let r : ℝ := y / x
  have hr : 1 < r := by
    dsimp [r]
    exact (lt_div_iff₀ hx).2 (by simpa using hxy)
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  have hyr : y = x * r := by
    dsimp [r]
    field_simp [ne_of_gt hx]
  have hxcombine :
      x ^ (-sigma) * x ^ (sigma - 1) = x⁻¹ := by
    rw [← Real.rpow_add hx, ← Real.rpow_neg_one x]
    congr 1
    ring
  have hforward :
      y ^ (-sigma) * x ^ (sigma - 1) =
        x⁻¹ * r ^ (-sigma) := by
    rw [hyr, Real.mul_rpow hx.le hrpos.le]
    calc
      (x ^ (-sigma) * r ^ (-sigma)) * x ^ (sigma - 1) =
          (x ^ (-sigma) * x ^ (sigma - 1)) * r ^ (-sigma) := by ring
      _ = x⁻¹ * r ^ (-sigma) := by rw [hxcombine]
  have hbackward :
      x ^ (-sigma) * y ^ (sigma - 1) =
        x⁻¹ * r ^ (sigma - 1) := by
    rw [hyr, Real.mul_rpow hx.le hrpos.le]
    calc
      x ^ (-sigma) * (x ^ (sigma - 1) * r ^ (sigma - 1)) =
          (x ^ (-sigma) * x ^ (sigma - 1)) * r ^ (sigma - 1) := by ring
      _ = x⁻¹ * r ^ (sigma - 1) := by rw [hxcombine]
  have ha : r ^ (-sigma) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hr (by linarith)
  have hb : r ^ (sigma - 1) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hr (by linarith)
  have hab :
      r ^ (-sigma) * r ^ (sigma - 1) = r ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hrpos]
    congr 1
    ring
  have hgap :
      0 < 1 + r ^ (-1 : ℝ) -
        (r ^ (-sigma) + r ^ (sigma - 1)) := by
    calc
      1 + r ^ (-1 : ℝ) -
          (r ^ (-sigma) + r ^ (sigma - 1)) =
        (1 - r ^ (-sigma)) * (1 - r ^ (sigma - 1)) := by
          rw [← hab]
          ring
      _ > 0 := mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb)
  calc
    y ^ (-sigma) * x ^ (sigma - 1) +
        x ^ (-sigma) * y ^ (sigma - 1) =
      x⁻¹ * (r ^ (-sigma) + r ^ (sigma - 1)) := by
        rw [hforward, hbackward]
        ring
    _ < x⁻¹ * (1 + r ^ (-1 : ℝ)) := by
      apply mul_lt_mul_of_pos_left
      · linarith
      · exact inv_pos.mpr hx
  _ = y⁻¹ + x⁻¹ := by
    rw [Real.rpow_neg_one, hyr]
    field_simp [ne_of_gt hx, ne_of_gt hrpos]
    ring

/-- Cada aresta refletida tem parte real estritamente positiva na faixa. -/
theorem finiteReflectedGradientEdge_re_pos
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) (n : ℕ) :
    0 < (finiteReflectedGradientEdge n s).re := by
  let crossForward : ℂ :=
    (starRingEnd ℂ) (positiveDirichletValue s (n + 1)) *
      positiveDirichletValue (reflectedParameter s) n
  let crossBackward : ℂ :=
    (starRingEnd ℂ) (positiveDirichletValue s n) *
      positiveDirichletValue (reflectedParameter s) (n + 1)
  have hforwardRe : crossForward.re ≤ ‖crossForward‖ :=
    Complex.re_le_norm crossForward
  have hbackwardRe : crossBackward.re ≤ ‖crossBackward‖ :=
    Complex.re_le_norm crossBackward
  have hcross :
      ((n + 2 : ℕ) : ℝ) ^ (-s.re) *
          ((n + 1 : ℕ) : ℝ) ^ (s.re - 1) +
        ((n + 1 : ℕ) : ℝ) ^ (-s.re) *
          ((n + 2 : ℕ) : ℝ) ^ (s.re - 1) <
      (((n + 2 : ℕ) : ℝ))⁻¹ + (((n + 1 : ℕ) : ℝ))⁻¹ := by
    apply reflected_rpow_cross_sum_lt_inv_sum
    · positivity
    · exact_mod_cast Nat.lt_succ_self (n + 1)
    · exact hs.1
    · exact hs.2
  rw [finiteReflectedGradientEdge_eq_diagonal_sub_cross]
  change
    0 < (((n + 2 : ℕ) : ℂ)⁻¹).re +
        (((n + 1 : ℕ) : ℂ)⁻¹).re -
      (crossForward.re + crossBackward.re)
  have hforwardNorm :
      ‖crossForward‖ =
        ((n + 2 : ℕ) : ℝ) ^ (-s.re) *
          ((n + 1 : ℕ) : ℝ) ^ (s.re - 1) := by
    exact norm_reflectedGradientCross_forward n s
  have hbackwardNorm :
      ‖crossBackward‖ =
        ((n + 1 : ℕ) : ℝ) ^ (-s.re) *
          ((n + 2 : ℕ) : ℝ) ^ (s.re - 1) := by
    exact norm_reflectedGradientCross_backward n s
  rw [hforwardNorm] at hforwardRe
  rw [hbackwardNorm] at hbackwardRe
  have hdiagForward :
      (((n + 2 : ℕ) : ℂ)⁻¹).re = (((n + 2 : ℕ) : ℝ))⁻¹ := by
    change ((↑(((n + 2 : ℕ) : ℝ)) : ℂ)⁻¹).re =
      (((n + 2 : ℕ) : ℝ))⁻¹
    rw [← Complex.ofReal_inv]
    rfl
  have hdiagBackward :
      (((n + 1 : ℕ) : ℂ)⁻¹).re = (((n + 1 : ℕ) : ℝ))⁻¹ := by
    change ((↑(((n + 1 : ℕ) : ℝ)) : ℂ)⁻¹).re =
      (((n + 1 : ℕ) : ℝ))⁻¹
    rw [← Complex.ofReal_inv]
    rfl
  rw [hdiagForward, hdiagBackward]
  linarith

/-- A parte real, vista como homomorfismo aditivo. -/
def complexRealPartAddHom : ℂ →+ ℝ where
  toFun z := z.re
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem complexRealPartAddHom_apply (z : ℂ) :
    complexRealPartAddHom z = z.re := rfl

/-- O pareamento refletido finito possui parte real positiva em corte nao vazio. -/
theorem finiteReflectedGradientPairing_re_pos
    {M : ℕ} (hM : 0 < M) {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    0 < (finiteReflectedGradientPairing M s).re := by
  unfold finiteReflectedGradientPairing
  change 0 < complexRealPartAddHom
    (∑ n ∈ Finset.range M,
      (starRingEnd ℂ) (positiveDirichletGradient s n) *
        positiveDirichletGradient (reflectedParameter s) n)
  rw [map_sum]
  change 0 < ∑ n ∈ Finset.range M, (finiteReflectedGradientEdge n s).re
  apply Finset.sum_pos
  · intro n hn
    exact finiteReflectedGradientEdge_re_pos hs n
  · exact ⟨0, Finset.mem_range.mpr hM⟩

/-- A energia radial finita completa e estritamente positiva. -/
theorem finiteRadialGreenEnergy_pos
    (p M : ℕ) (hp : Nat.Prime p) (hM : 0 < M)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    0 < finiteRadialGreenEnergy p M s := by
  unfold finiteRadialGreenEnergy
  exact mul_pos
    (cpRadialCofactor_pos p hp (criticalDisplacement s.re))
    (finiteReflectedGradientPairing_re_pos hM hs)

end

end CPFormal.Analytic.Cp
