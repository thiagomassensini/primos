import CPFormal.Analytic.CpTilt

/-!
# Rigidez de sinal do tilt multibase `Cₚ`

Este arquivo fecha a hipotese abstrata `TiltRigidityAt` para todo primo impar,
desde que o centro esteja estritamente fora da camera balanceada:

`halfRange p < center`.

A prova tem tres passos finitos e explicitos:

1. subtrair uma copia do valor central de cada perna;
2. usar a involucao `a ↦ -a` para escrever o tilt como metade da soma dos
   brackets simetricos de raios `a`;
3. aplicar convexidade estrita para `delta > 0` e concavidade estrita para
   `-1 < delta < 0`.

No semiplano `sigma > 0`, temos sempre
`delta = sigma - 1/2 > -1`. Portanto o unico zero admissivel e `delta = 0`.
-/

open scoped BigOperators

namespace CPFormal.Analytic.Cp

open CPFormal.Carry.Cp
open CPFormal.Genuine.Cp

noncomputable section

/-- Contribuicao de uma perna depois de retirar sua copia do centro. -/
def cpLegTilt (delta center : ℝ) (a : ℤ) : ℝ :=
  (center + (a : ℝ)) ^ (-delta) - center ^ (-delta)

/-- Bracket simetrico associado ao par de pernas `{-a,a}`. -/
def cpPairTilt (delta center : ℝ) (a : ℤ) : ℝ :=
  (center - (a : ℝ)) ^ (-delta) +
    (center + (a : ℝ)) ^ (-delta) -
      2 * center ^ (-delta)

/-- A camera balanceada e invariante pela involucao `a ↦ -a`. -/
@[simp] theorem neg_mem_balancedOffsets_iff
    (p : ℕ) (a : ℤ) :
    -a ∈ balancedOffsets p ↔ a ∈ balancedOffsets p := by
  simp only [mem_balancedOffsets_iff]
  omega

/-- Reindexar uma soma balanceada por negacao nao altera seu valor. -/
theorem sum_balancedOffsets_neg
    (p : ℕ) (f : ℤ → ℝ) :
    (∑ a ∈ balancedOffsets p, f (-a)) =
      ∑ a ∈ balancedOffsets p, f a := by
  classical
  have hbij : Function.Bijective (fun a : ℤ => -a) := by
    constructor
    · intro a b hab
      simpa using congrArg (fun z : ℤ => -z) hab
    · intro b
      exact ⟨-b, by simp⟩
  apply Finset.sum_bijective (fun a : ℤ => -a) hbij
  · intro a
    exact (neg_mem_balancedOffsets_iff p a).symm
  · intro a ha
    rfl

/-- O tilt e a soma das contribuicoes centralizadas de todas as pernas. -/
theorem cpTilt_eq_sum_leg
    (p : ℕ) (hpodd : Odd p) (delta center : ℝ) :
    cpTilt p delta center =
      ∑ a ∈ balancedOffsets p, cpLegTilt delta center a := by
  classical
  simp [cpTilt, cpLegTilt, Finset.sum_sub_distrib,
    card_balancedOffsets hpodd, nsmul_eq_mul]

/-- Somar uma perna e sua oposta produz exatamente o bracket simetrico. -/
theorem cpLegTilt_add_neg
    (delta center : ℝ) (a : ℤ) :
    cpLegTilt delta center a + cpLegTilt delta center (-a) =
      cpPairTilt delta center a := by
  simp [cpLegTilt, cpPairTilt]
  ring_nf

/--
Decomposicao angular fundamental: o tilt inteiro e metade da soma dos
brackets dos pares `±a`. Cada par aparece duas vezes na soma balanceada,
justificando o fator `1/2`.
-/
theorem cpTilt_eq_half_sum_pair
    (p : ℕ) (hpodd : Odd p) (delta center : ℝ) :
    cpTilt p delta center =
      ((1 : ℝ) / 2) *
        ∑ a ∈ balancedOffsets p, cpPairTilt delta center a := by
  rw [cpTilt_eq_sum_leg p hpodd]
  have hneg :=
    sum_balancedOffsets_neg p (cpLegTilt delta center)
  calc
    (∑ a ∈ balancedOffsets p, cpLegTilt delta center a) =
        ((1 : ℝ) / 2) *
          ((∑ a ∈ balancedOffsets p, cpLegTilt delta center a) +
            ∑ a ∈ balancedOffsets p, cpLegTilt delta center a) := by
      ring
    _ = ((1 : ℝ) / 2) *
          ((∑ a ∈ balancedOffsets p, cpLegTilt delta center a) +
            ∑ a ∈ balancedOffsets p, cpLegTilt delta center (-a)) := by
      rw [hneg]
    _ = ((1 : ℝ) / 2) *
          ∑ a ∈ balancedOffsets p,
            (cpLegTilt delta center a + cpLegTilt delta center (-a)) := by
      rw [Finset.sum_add_distrib]
    _ = ((1 : ℝ) / 2) *
          ∑ a ∈ balancedOffsets p, cpPairTilt delta center a := by
      refine congrArg (fun x : ℝ => ((1 : ℝ) / 2) * x) ?_
      apply Finset.sum_congr rfl
      intro a ha
      exact cpLegTilt_add_neg delta center a

/--
Uma funcao estritamente convexa em `(0,∞)` possui segunda diferenca
central estritamente positiva em qualquer raio nao nulo cujas pontas
permanecam no dominio.
-/
lemma centeredSecond_pos_of_strictConvexOn_Ioi_radius
    {f : ℝ → ℝ}
    (hconv : StrictConvexOn ℝ (Set.Ioi 0) f)
    {center radius : ℝ}
    (hradius : radius ≠ 0)
    (hminus : 0 < center - radius)
    (hplus : 0 < center + radius) :
    0 < f (center - radius) + f (center + radius) - 2 * f center := by
  have hxy : center - radius ≠ center + radius := by
    intro h
    apply hradius
    linarith
  have hmid := hconv.2 hminus hplus hxy
    (by norm_num : 0 < (1 / 2 : ℝ))
    (by norm_num : 0 < (1 / 2 : ℝ))
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hcomb :
      (2 : ℝ)⁻¹ * (center - radius) +
          (2 : ℝ)⁻¹ * (center + radius) = center := by
    ring
  have hmid0 :
      f ((2 : ℝ)⁻¹ * (center - radius) +
          (2 : ℝ)⁻¹ * (center + radius)) <
        (2 : ℝ)⁻¹ * f (center - radius) +
          (2 : ℝ)⁻¹ * f (center + radius) := by
    simpa [smul_eq_mul] using hmid
  have hmid1 :
      f center <
        (2 : ℝ)⁻¹ * f (center - radius) +
          (2 : ℝ)⁻¹ * f (center + radius) := by
    simpa [hcomb] using hmid0
  nlinarith [hmid1]

/-- Versao concava estrita da segunda diferenca central. -/
lemma centeredSecond_neg_of_strictConcaveOn_Ici_radius
    {f : ℝ → ℝ}
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) f)
    {center radius : ℝ}
    (hradius : radius ≠ 0)
    (hminus : 0 < center - radius)
    (hplus : 0 < center + radius) :
    f (center - radius) + f (center + radius) - 2 * f center < 0 := by
  have hxy : center - radius ≠ center + radius := by
    intro h
    apply hradius
    linarith
  have hmid := hconc.2 (le_of_lt hminus) (le_of_lt hplus) hxy
    (by norm_num : 0 < (1 / 2 : ℝ))
    (by norm_num : 0 < (1 / 2 : ℝ))
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hcomb :
      (2 : ℝ)⁻¹ * (center - radius) +
          (2 : ℝ)⁻¹ * (center + radius) = center := by
    ring
  have hmid0 :
      (2 : ℝ)⁻¹ * f (center - radius) +
          (2 : ℝ)⁻¹ * f (center + radius) <
        f ((2 : ℝ)⁻¹ * (center - radius) +
          (2 : ℝ)⁻¹ * (center + radius)) := by
    simpa [smul_eq_mul] using hmid
  have hmid1 :
      (2 : ℝ)⁻¹ * f (center - radius) +
          (2 : ℝ)⁻¹ * f (center + radius) < f center := by
    simpa [hcomb] using hmid0
  nlinarith [hmid1]

/-- Para expoente real negativo, `x ↦ x^exponent` e estritamente convexa. -/
theorem strictConvexOn_rpow_of_neg
    {exponent : ℝ} (hexponent : exponent < 0) :
    StrictConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => x ^ exponent) := by
  apply strictConvexOn_of_deriv2_pos (convex_Ioi 0)
  · exact fun x hx =>
      (Real.continuousAt_rpow_const x exponent
        (Or.inl (ne_of_gt hx))).continuousWithinAt
  intro x hx
  rw [interior_Ioi, Set.mem_Ioi] at hx
  simp only [Real.iter_deriv_rpow_const]
  apply mul_pos
  · have hpochhammer :
        (descPochhammer ℝ 2).eval exponent =
          exponent * (exponent - 1) := by
      simp [descPochhammer, Polynomial.eval_mul, Polynomial.eval_sub]
    rw [hpochhammer]
    exact mul_pos_of_neg_of_neg hexponent (by linarith)
  · exact Real.rpow_pos_of_pos hx _

/-- Todo bracket de uma perna da camera e positivo quando `delta > 0`. -/
theorem cpPairTilt_pos_of_delta_pos
    {p : ℕ} {delta center : ℝ} {a : ℤ}
    (ha : a ∈ balancedOffsets p)
    (hcenter : (halfRange p : ℝ) < center)
    (hdelta : 0 < delta) :
    0 < cpPairTilt delta center a := by
  obtain ⟨ha0z, halowz, hauppz⟩ := mem_balancedOffsets_iff.mp ha
  have ha0 : (a : ℝ) ≠ 0 := by
    exact_mod_cast ha0z
  have halow : -(halfRange p : ℝ) ≤ (a : ℝ) := by
    exact_mod_cast halowz
  have haupp : (a : ℝ) ≤ (halfRange p : ℝ) := by
    exact_mod_cast hauppz
  have hminus : 0 < center - (a : ℝ) := by
    linarith
  have hplus : 0 < center + (a : ℝ) := by
    linarith
  have hconv := strictConvexOn_rpow_of_neg (by linarith : -delta < 0)
  have hsign := centeredSecond_pos_of_strictConvexOn_Ioi_radius
    hconv ha0 hminus hplus
  simpa [cpPairTilt] using hsign

/-- Todo bracket e negativo no regime concavo `-1 < delta < 0`. -/
theorem cpPairTilt_neg_of_neg_one_lt_delta
    {p : ℕ} {delta center : ℝ} {a : ℤ}
    (ha : a ∈ balancedOffsets p)
    (hcenter : (halfRange p : ℝ) < center)
    (hdeltaLower : -1 < delta)
    (hdeltaUpper : delta < 0) :
    cpPairTilt delta center a < 0 := by
  obtain ⟨ha0z, halowz, hauppz⟩ := mem_balancedOffsets_iff.mp ha
  have ha0 : (a : ℝ) ≠ 0 := by
    exact_mod_cast ha0z
  have halow : -(halfRange p : ℝ) ≤ (a : ℝ) := by
    exact_mod_cast halowz
  have haupp : (a : ℝ) ≤ (halfRange p : ℝ) := by
    exact_mod_cast hauppz
  have hminus : 0 < center - (a : ℝ) := by
    linarith
  have hplus : 0 < center + (a : ℝ) := by
    linarith
  have hpow0 : 0 < -delta := by linarith
  have hpow1 : -delta < 1 := by linarith
  have hconc :
      StrictConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ (-delta)) :=
    Real.strictConcaveOn_rpow hpow0 hpow1
  have hsign := centeredSecond_neg_of_strictConcaveOn_Ici_radius
    hconc ha0 hminus hplus
  simpa [cpPairTilt] using hsign

/-- Uma camera prima impar possui pelo menos um par de pernas. -/
theorem balancedOffsets_nonempty_of_prime_odd
    {p : ℕ} (hp : Nat.Prime p) (hpodd : Odd p) :
    (balancedOffsets p).Nonempty := by
  have hpform := two_mul_halfRange_add_one hpodd
  have hh : 1 ≤ halfRange p := by
    have hpgt := hp.one_lt
    omega
  have hhInt : (1 : ℤ) ≤ (halfRange p : ℤ) := by
    exact_mod_cast hh
  refine ⟨1, mem_balancedOffsets_iff.mpr ?_⟩
  refine ⟨by norm_num, ?_, hhInt⟩
  omega

/-- Sinal global estritamente positivo do tilt para `delta > 0`. -/
theorem cpTilt_pos_of_delta_pos
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {delta center : ℝ}
    (hdelta : 0 < delta)
    (hcenter : (halfRange p : ℝ) < center) :
    0 < cpTilt p delta center := by
  rw [cpTilt_eq_half_sum_pair p hpodd]
  apply mul_pos (by norm_num : (0 : ℝ) < 1 / 2)
  apply Finset.sum_pos
  · intro a ha
    exact cpPairTilt_pos_of_delta_pos ha hcenter hdelta
  · exact balancedOffsets_nonempty_of_prime_odd hp hpodd

/-- Sinal global estritamente negativo do tilt para `-1 < delta < 0`. -/
theorem cpTilt_neg_of_neg_one_lt_delta
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {delta center : ℝ}
    (hdeltaLower : -1 < delta)
    (hdeltaUpper : delta < 0)
    (hcenter : (halfRange p : ℝ) < center) :
    cpTilt p delta center < 0 := by
  rw [cpTilt_eq_half_sum_pair p hpodd]
  apply mul_neg_of_pos_of_neg (by norm_num : (0 : ℝ) < 1 / 2)
  apply Finset.sum_neg
  · intro a ha
    exact cpPairTilt_neg_of_neg_one_lt_delta
      ha hcenter hdeltaLower hdeltaUpper
  · exact balancedOffsets_nonempty_of_prime_odd hp hpodd

/--
Rigidez canonica do tilt: fora da camera, no semiplano `sigma > 0`, a soma
bracketada so pode se anular na meia abscissa.
-/
theorem tiltRigidityAt_of_halfRange_lt_center
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {center : ℝ} (hcenter : (halfRange p : ℝ) < center) :
    TiltRigidityAt p center := by
  refine ⟨?_⟩
  intro sigma hsigma hzero
  by_contra hdelta
  rcases lt_or_gt_of_ne hdelta with hdeltaNeg | hdeltaPos
  · have hdeltaLower : -1 < criticalDisplacement sigma := by
      unfold criticalDisplacement
      linarith
    have hsign : cpTiltAtSigma p sigma center < 0 := by
      simpa [cpTiltAtSigma] using
        cpTilt_neg_of_neg_one_lt_delta p hp hpodd
          hdeltaLower hdeltaNeg hcenter
    rw [hzero] at hsign
    linarith
  · have hsign : 0 < cpTiltAtSigma p sigma center := by
      simpa [cpTiltAtSigma] using
        cpTilt_pos_of_delta_pos p hp hpodd hdeltaPos hcenter
    rw [hzero] at hsign
    linarith

/-- Forma escalar da rigidez: os zeros do tilt sao exatamente `sigma = 1/2`. -/
theorem cpTiltAtSigma_eq_zero_iff_half
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {sigma center : ℝ} (hsigma : 0 < sigma)
    (hcenter : (halfRange p : ℝ) < center) :
    cpTiltAtSigma p sigma center = 0 ↔ sigma = (1 : ℝ) / 2 := by
  constructor
  · intro htilt
    have hdelta :=
      (tiltRigidityAt_of_halfRange_lt_center p hp hpodd hcenter).zero_only
        hsigma htilt
    unfold criticalDisplacement at hdelta
    linarith
  · intro hsigmaHalf
    subst sigma
    exact cpTiltAtSigma_half p hpodd center

/--
Versao sem hipotese abstrata da ponte norma--tilt: em todo centro admissivel,
o defeito quadratico e o tilt possuem exatamente o mesmo zero.
-/
theorem branchDefect_eq_zero_iff_cpTiltAtSigma_eq_zero_of_admissible_center
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {sigma center : ℝ} (hsigma : 0 < sigma)
    (hcenter : (halfRange p : ℝ) < center) :
    branchDefect p sigma = 0 ↔ cpTiltAtSigma p sigma center = 0 := by
  exact branchDefect_eq_zero_iff_cpTiltAtSigma_eq_zero
    p hp hpodd center
      (tiltRigidityAt_of_halfRange_lt_center p hp hpodd hcenter)
      hsigma

end

end CPFormal.Analytic.Cp
