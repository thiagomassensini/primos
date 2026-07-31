import CPFormal.Analytic.CpNativeCarryFiniteCameraAlgebra
import CPFormal.Analytic.CpNaturalEvenCameraRegularity
import CPFormal.Analytic.CpGenuineCompatibility

/-!
# Analytic continuation of every natural carry camera

The native finite scanner is defined for every natural width.  Odd widths
tile complete blocks, while even widths display one missing dilation channel.
The finite algebra for those two geometries is proved in
`CpNativeCarryFiniteCameraAlgebra`.

This file closes the analytic passage without a primality hypothesis:

* the saturated bracket series converges for every width `b ≥ 2` on
  `re(s) > -1`;
* the resulting chart is holomorphic on that half-plane;
* every natural width `b ≥ 3` has the factor selected by its exact finite
  normal form;
* on the critical strip the chart is that factor times the canonical
  `genuineContinuation`;
* on the critical line the factor never vanishes, so every natural camera
  has exactly the canonical Genuine zeros;
* the scanner's specially named aligned `C₂` camera is included because it
  is exactly the native width-four camera.

No prime-only residue chart is used below.  Primality remains relevant only
to older presentations through balanced prime offsets, not to the native
saturated scanner.
-/

open scoped BigOperators Topology

namespace CPFormal.Analytic.Cp

open CPFormal.Genuine.Cp
open Filter Metric Set

noncomputable section

attribute [local instance 10000]
  NormedAddCommGroup.toAddCommGroup
  CommCStarAlgebra.toNonUnitalCommCStarAlgebra
  NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra
  NonUnitalCStarAlgebra.toNormedSpace
  NormedSpace.toModule

/-! ## Width-neutral convergence estimates -/

/--
For every width at least two, an admissible left leg stays beyond `k+1`.
This is the geometric fact for which the legacy theorem used primality.
-/
theorem natCast_add_one_le_alignedCenter_sub_radius_of_two_le
    {b radius k : ℕ} (hb : 2 ≤ b)
    (hradius : radius ≤ halfRange b) :
    ((k + 1 : ℕ) : ℝ) ≤
      (b : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ) := by
  have hhalf : halfRange b ≤ b - 1 := by
    unfold halfRange
    exact Nat.div_le_self (b - 1) 2
  have hradius' : radius ≤ b - 1 := le_trans hradius hhalf
  have hbone : 1 ≤ b := by omega
  have hboneReal : (1 : ℝ) ≤ (b : ℝ) := by
    exact_mod_cast hbone
  have hbnonneg : 0 ≤ (b : ℝ) - 1 := sub_nonneg.mpr hboneReal
  have hkNat : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
  have hk : 1 ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast hkNat
  have hradiusRealNat : (radius : ℝ) ≤ ((b - 1 : ℕ) : ℝ) := by
    exact_mod_cast hradius'
  have hbCast : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
    rw [Nat.cast_sub hbone]
    norm_num
  have hradiusReal : (radius : ℝ) ≤ (b : ℝ) - 1 := by
    simpa [hbCast] using hradiusRealNat
  nlinarith [mul_nonneg hbnonneg (sub_nonneg.mpr hk)]

/-- Pointwise second-difference estimate for an arbitrary natural width. -/
theorem norm_realCpPairBracket_le_of_two_le
    {b radius k : ℕ} (hb : 2 ≤ b)
    {s : ℂ} (hs : -1 < s.re)
    (hradius : radius ∈ Finset.Icc 1 (halfRange b)) :
    ‖realCpPairBracket b radius k s‖ ≤
      (2 * ‖s * (s + 1)‖ * (radius : ℝ) ^ 2) *
        ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) := by
  have hradiusUpper : radius ≤ halfRange b :=
    (Finset.mem_Icc.mp hradius).2
  have hleftLower :=
    natCast_add_one_le_alignedCenter_sub_radius_of_two_le
      (k := k) hb hradiusUpper
  have hkpos : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  have hleft :
      0 < (b : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ) :=
    lt_of_lt_of_le hkpos hleftLower
  have hraw := norm_realDirichletPower_centeredSecondDifference_le
    hs (show 0 ≤ (radius : ℝ) by positivity) hleft
  have hpower :
      ((b : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ)) ^
          (-s.re - 2) ≤
        ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) :=
    Real.rpow_le_rpow_of_nonpos hkpos hleftLower (by linarith [hs])
  calc
    ‖realCpPairBracket b radius k s‖ ≤
        2 *
          (‖s * (s + 1)‖ *
            ((b : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ)) ^
              (-s.re - 2)) *
          (radius : ℝ) ^ 2 := by
      simpa [realCpPairBracket] using hraw
    _ = (2 * ‖s * (s + 1)‖ * (radius : ℝ) ^ 2) *
          (((b : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ)) ^
            (-s.re - 2)) := by ring
    _ ≤ (2 * ‖s * (s + 1)‖ * (radius : ℝ) ^ 2) *
          ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) :=
      mul_le_mul_of_nonneg_left hpower (by positivity)

/-- A full saturated block is bounded by one shifted p-series. -/
theorem norm_realCpSaturatedBracket_le_of_two_le
    {b k : ℕ} (hb : 2 ≤ b)
    {s : ℂ} (hs : -1 < s.re) :
    ‖realCpSaturatedBracket b k s‖ ≤
      cpBracketMajorantConstant b s *
        ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) := by
  classical
  unfold realCpSaturatedBracket cpBracketMajorantConstant
  calc
    ‖∑ radius ∈ Finset.Icc 1 (halfRange b),
        realCpPairBracket b radius k s‖ ≤
        ∑ radius ∈ Finset.Icc 1 (halfRange b),
          ‖realCpPairBracket b radius k s‖ := norm_sum_le _ _
    _ ≤ ∑ radius ∈ Finset.Icc 1 (halfRange b),
          (2 * ‖s * (s + 1)‖ * (radius : ℝ) ^ 2) *
            ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) := by
      exact Finset.sum_le_sum fun radius hradius ↦
        norm_realCpPairBracket_le_of_two_le hb hs hradius
    _ = (∑ radius ∈ Finset.Icc 1 (halfRange b),
          2 * ‖s * (s + 1)‖ * (radius : ℝ) ^ 2) *
            ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) := by
      rw [Finset.sum_mul]

/-- Absolute summability of every native saturated camera. -/
theorem summable_norm_realCpSaturatedBracket_of_two_le
    (b : ℕ) (hb : 2 ≤ b)
    {s : ℂ} (hs : -1 < s.re) :
    Summable (fun k : ℕ ↦ ‖realCpSaturatedBracket b k s‖) := by
  have hpower := summable_nat_add_one_rpow_neg_re_sub_two hs
  have hmajorant := hpower.mul_left (cpBracketMajorantConstant b s)
  exact hmajorant.of_norm_bounded
    (fun k ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact norm_realCpSaturatedBracket_le_of_two_le hb hs)

/-- Complex summability follows from absolute summability. -/
theorem summable_realCpSaturatedBracket_of_two_le
    (b : ℕ) (hb : 2 ≤ b)
    {s : ℂ} (hs : -1 < s.re) :
    Summable (fun k : ℕ ↦ realCpSaturatedBracket b k s) :=
  (summable_norm_realCpSaturatedBracket_of_two_le b hb hs).of_norm

/--
The analytic finite chart and the additive native chart are literally the
same finite object for every width.
-/
theorem finiteBracketedDirichletChart_eq_nativeCarryFiniteSaturatedChart
    (b M : ℕ) (s : ℂ) :
    finiteBracketedDirichletChart b M s =
      nativeCarryFiniteSaturatedChart b M (dirichletTerm s) := by
  classical
  unfold finiteBracketedDirichletChart
    nativeCarryFiniteSaturatedChart
    CPFormal.Genuine.Cp.seedSum
  apply congrArg
    (fun tail : ℂ ↦
      (∑ n ∈ Finset.Icc (1 : ℤ) (halfRange b : ℤ),
        dirichletTerm s n) + tail)
  apply Finset.sum_congr rfl
  intro k hk
  exact realCpSaturatedBracket_eq_saturatedBracket b k s

/-- Finite bracketed prefixes converge without a primality hypothesis. -/
theorem finiteBracketedDirichletChart_tendsto_of_two_le
    (b : ℕ) (hb : 2 ≤ b)
    {s : ℂ} (hs : -1 < s.re) :
    Tendsto (fun M : ℕ ↦ finiteBracketedDirichletChart b M s)
      atTop (nhds (bracketedDirichletChart b s)) := by
  have hsum :=
    (summable_realCpSaturatedBracket_of_two_le b hb hs).tendsto_sum_tsum_nat
  simpa [finiteBracketedDirichletChart, bracketedDirichletChart] using
    tendsto_const_nhds.add hsum

/--
The scanner's native finite chart converges on the whole bracket half-plane
for every material natural width.
-/
theorem nativeCarryFiniteSaturatedChart_dirichlet_tendsto_of_two_le
    (b : ℕ) (hb : 2 ≤ b)
    {s : ℂ} (hs : -1 < s.re) :
    Tendsto
      (fun M : ℕ ↦
        nativeCarryFiniteSaturatedChart b M (dirichletTerm s))
      atTop (nhds (bracketedDirichletChart b s)) := by
  exact
    (finiteBracketedDirichletChart_tendsto_of_two_le b hb hs).congr'
      (Filter.Eventually.of_forall fun M ↦
        finiteBracketedDirichletChart_eq_nativeCarryFiniteSaturatedChart
          b M s)

/-! ## Width-neutral holomorphy -/

/-- Every admissible pair bracket is entire in the spectral parameter. -/
theorem differentiable_realCpPairBracket_of_two_le
    {b radius k : ℕ} (hb : 2 ≤ b)
    (hradius : radius ∈ Finset.Icc 1 (halfRange b)) :
    Differentiable ℂ (realCpPairBracket b radius k) := by
  have hradiusUpper : radius ≤ halfRange b :=
    (Finset.mem_Icc.mp hradius).2
  have hleftLower :=
    natCast_add_one_le_alignedCenter_sub_radius_of_two_le
      (k := k) hb hradiusUpper
  have hkpos : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  have hleft :
      0 < (b : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ) :=
    lt_of_lt_of_le hkpos hleftLower
  have hbpos : 0 < (b : ℝ) := by
    exact_mod_cast (show 0 < b by omega)
  have hcenter : 0 < (b : ℝ) * ((k + 1 : ℕ) : ℝ) := by
    exact mul_pos hbpos (by positivity)
  have hright :
      0 < (b : ℝ) * ((k + 1 : ℕ) : ℝ) + (radius : ℝ) :=
    add_pos_of_pos_of_nonneg hcenter (by positivity)
  have hleftDiff :=
    differentiable_realDirichletPower_in_parameter (ne_of_gt hleft)
  have hcenterDiff :=
    differentiable_realDirichletPower_in_parameter (ne_of_gt hcenter)
  have hrightDiff :=
    differentiable_realDirichletPower_in_parameter (ne_of_gt hright)
  rw [show realCpPairBracket b radius k =
      ((fun s : ℂ ↦ realDirichletPower s
          ((b : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ))) -
        ((fun s : ℂ ↦ realDirichletPower s
            ((b : ℝ) * ((k + 1 : ℕ) : ℝ))) +
          (fun s : ℂ ↦ realDirichletPower s
            ((b : ℝ) * ((k + 1 : ℕ) : ℝ))))) +
        (fun s : ℂ ↦ realDirichletPower s
          ((b : ℝ) * ((k + 1 : ℕ) : ℝ) + (radius : ℝ))) by
    funext s
    simp [realCpPairBracket, two_smul]]
  exact (hleftDiff.sub (hcenterDiff.add hcenterDiff)).add hrightDiff

/-- Every full block is an entire finite sum. -/
theorem differentiable_realCpSaturatedBracket_of_two_le
    (b k : ℕ) (hb : 2 ≤ b) :
    Differentiable ℂ (realCpSaturatedBracket b k) := by
  classical
  unfold realCpSaturatedBracket
  exact Differentiable.fun_sum fun radius hradius ↦
    differentiable_realCpPairBracket_of_two_le hb hradius

/-- Local uniform majorant for an arbitrary natural width. -/
theorem norm_realCpSaturatedBracket_le_local_of_two_le
    (b : ℕ) (hb : 2 ≤ b) {z w : ℂ}
    (hz : z ∈ bracketHalfPlane)
    (hw : w ∈ Metric.ball z (bracketNeighborhoodRadius z)) (k : ℕ) :
    ‖realCpSaturatedBracket b k w‖ ≤
      localCpBracketMajorantConstant b z (bracketNeighborhoodRadius z) *
        ((k + 1 : ℕ) : ℝ) ^ (-bracketNeighborhoodFloor z - 2) := by
  have hfloor := bracketNeighborhoodFloor_lt_re hw
  have hwDomain : -1 < w.re :=
    lt_trans (neg_one_lt_bracketNeighborhoodFloor hz) hfloor
  have hconstant := cpBracketMajorantConstant_le_local (p := b)
    (le_of_lt (bracketNeighborhoodRadius_pos hz)) hw
  have hbase : 1 ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hpower :
      ((k + 1 : ℕ) : ℝ) ^ (-w.re - 2) ≤
        ((k + 1 : ℕ) : ℝ) ^ (-bracketNeighborhoodFloor z - 2) :=
    Real.monotone_rpow_of_base_ge_one hbase (by linarith [hfloor])
  calc
    ‖realCpSaturatedBracket b k w‖ ≤
        cpBracketMajorantConstant b w *
          ((k + 1 : ℕ) : ℝ) ^ (-w.re - 2) :=
      norm_realCpSaturatedBracket_le_of_two_le hb hwDomain
    _ ≤ localCpBracketMajorantConstant b z (bracketNeighborhoodRadius z) *
          ((k + 1 : ℕ) : ℝ) ^ (-bracketNeighborhoodFloor z - 2) := by
      calc
        cpBracketMajorantConstant b w *
            ((k + 1 : ℕ) : ℝ) ^ (-w.re - 2) ≤
            localCpBracketMajorantConstant b z (bracketNeighborhoodRadius z) *
              ((k + 1 : ℕ) : ℝ) ^ (-w.re - 2) :=
          mul_le_mul_of_nonneg_right hconstant
            (Real.rpow_nonneg (by positivity) _)
        _ ≤ localCpBracketMajorantConstant b z (bracketNeighborhoodRadius z) *
              ((k + 1 : ℕ) : ℝ) ^ (-bracketNeighborhoodFloor z - 2) :=
          mul_le_mul_of_nonneg_left hpower
            (localCpBracketMajorantConstant_nonneg
              (le_of_lt (bracketNeighborhoodRadius_pos hz)))

/-- The bracket tail is holomorphic for every natural width at least two. -/
theorem differentiableOn_tsum_realCpSaturatedBracket_of_two_le
    (b : ℕ) (hb : 2 ≤ b) :
    DifferentiableOn ℂ
      (fun s : ℂ ↦ ∑' k : ℕ, realCpSaturatedBracket b k s)
      bracketHalfPlane := by
  intro z hz
  let R := bracketNeighborhoodRadius z
  let U : Set ℂ := Metric.ball z R
  let u : ℕ → ℝ := fun k ↦
    localCpBracketMajorantConstant b z R *
      ((k + 1 : ℕ) : ℝ) ^ (-bracketNeighborhoodFloor z - 2)
  have hR : 0 < R := bracketNeighborhoodRadius_pos hz
  have hu : Summable u := by
    simpa [u, R] using summable_localCpBracketMajorant b hz
  have hUOpen : IsOpen U := Metric.isOpen_ball
  have htailOn : DifferentiableOn ℂ
      (fun w : ℂ ↦ ∑' k : ℕ, realCpSaturatedBracket b k w) U := by
    apply Complex.differentiableOn_tsum_of_summable_norm hu
    · intro k
      exact
        (differentiable_realCpSaturatedBracket_of_two_le b k hb).differentiableOn
    · exact hUOpen
    · intro k w hw
      simpa [u, U, R] using
        norm_realCpSaturatedBracket_le_local_of_two_le b hb hz hw k
  have hzU : z ∈ U := by
    change dist z z < R
    simpa using hR
  exact
    (htailOn.differentiableAt
      (hUOpen.mem_nhds hzU)).differentiableWithinAt

/-- Every native natural-camera chart is holomorphic on `re(s) > -1`. -/
theorem differentiableOn_bracketedDirichletChart_of_two_le
    (b : ℕ) (hb : 2 ≤ b) :
    DifferentiableOn ℂ (bracketedDirichletChart b) bracketHalfPlane := by
  exact
    (differentiable_seedSum_dirichletTerm b).differentiableOn.add
      (differentiableOn_tsum_realCpSaturatedBracket_of_two_le b hb)

/-- `AnalyticOnNhd` form of natural-camera holomorphy. -/
theorem analyticOnNhd_bracketedDirichletChart_of_two_le
    (b : ℕ) (hb : 2 ≤ b) :
    AnalyticOnNhd ℂ (bracketedDirichletChart b) bracketHalfPlane :=
  (differentiableOn_bracketedDirichletChart_of_two_le b hb).analyticOnNhd
    isOpen_bracketHalfPlane

/-! ## Finite Dirichlet normal forms -/

/-- The literal integer prefix agrees with the standard positive prefix. -/
theorem nativeCarryPositivePrefix_dirichletTerm_eq
    (N : ℕ) (s : ℂ) :
    nativeCarryPositivePrefix (N : ℤ) (dirichletTerm s) =
      positiveDirichletPrefix s N := by
  simpa [nativeCarryPositivePrefix] using
    (positiveDirichletPrefix_eq_sum_Icc s N).symm

/-- Every aligned centre channel is a dilated positive Dirichlet prefix. -/
theorem nativeCarryCenterChannel_dirichletTerm_eq
    (b M : ℕ) (s : ℂ) :
    nativeCarryCenterChannel b M (dirichletTerm s) =
      dirichletTerm s (b : ℤ) * positiveDirichletPrefix s M := by
  classical
  unfold nativeCarryCenterChannel positiveDirichletPrefix
  simp_rw [dirichletTerm_alignedCenter]
  rw [← Finset.mul_sum]

/-- The explicit dilation channel also factors as one Dirichlet monomial. -/
theorem nativeCarryDilationChannel_dirichletTerm_eq
    (d L : ℕ) (s : ℂ) :
    nativeCarryDilationChannel d L (dirichletTerm s) =
      dirichletTerm s (d : ℤ) * positiveDirichletPrefix s L := by
  classical
  unfold nativeCarryDilationChannel positiveDirichletPrefix
  change
    (∑ j ∈ Finset.range L,
      dirichletTerm s (CPFormal.Genuine.Cp.alignedCenter d j)) =
        dirichletTerm s (d : ℤ) *
          ∑ j ∈ Finset.range L,
            dirichletTerm s (((j + 1 : ℕ) : ℤ))
  simp_rw [dirichletTerm_alignedCenter]
  rw [← Finset.mul_sum]

/-- The elementary power identity `b * b^(-s) = b^(1-s)`. -/
theorem nat_mul_dirichletTerm_eq_cpow_one_sub
    (b : ℕ) (hb : 0 < b) (s : ℂ) :
    (b : ℂ) * dirichletTerm s (b : ℤ) =
      (b : ℂ) ^ (1 - s) := by
  have hb0 : (b : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hb)
  simpa [dirichletTerm, sub_eq_add_neg] using
    (Complex.cpow_add (x := (b : ℂ)) (1 : ℂ) (-s) hb0).symm

/-- Exact two-prefix form of every nontrivial odd native camera. -/
theorem nativeCarryFiniteSaturatedChart_dirichlet_odd_eq
    (b M : ℕ) (hbodd : Odd b) (hb : 1 < b) (s : ℂ) :
    nativeCarryFiniteSaturatedChart b M (dirichletTerm s) =
      positiveDirichletPrefix s (b * M + halfRange b) -
        (b : ℂ) ^ (1 - s) * positiveDirichletPrefix s M := by
  rw [nativeCarryFiniteSaturatedChart_odd_normal_form b M hbodd hb]
  rw [show
      (b : ℤ) * (M : ℤ) + (halfRange b : ℤ) =
        ((b * M + halfRange b : ℕ) : ℤ) by
      push_cast
      ring]
  rw [nativeCarryPositivePrefix_dirichletTerm_eq,
    nativeCarryCenterChannel_dirichletTerm_eq]
  simp only [nsmul_eq_mul]
  rw [← mul_assoc, nat_mul_dirichletTerm_eq_cpow_one_sub b (by omega) s]

/-- Exact three-prefix form of every nondegenerate even native camera. -/
theorem nativeCarryFiniteSaturatedChart_dirichlet_even_eq
    (b M : ℕ) (hbeven : Even b) (hb : 2 < b) (s : ℂ) :
    nativeCarryFiniteSaturatedChart b M (dirichletTerm s) =
      positiveDirichletPrefix s (b * M + halfRange b) -
        dirichletTerm s ((b / 2 : ℕ) : ℤ) *
          positiveDirichletPrefix s (2 * M) -
        ((b - 2 : ℕ) : ℂ) * dirichletTerm s (b : ℤ) *
          positiveDirichletPrefix s M := by
  rw [nativeCarryFiniteSaturatedChart_even_normal_form b M hbeven hb]
  rw [show
      (b : ℤ) * (M : ℤ) + (halfRange b : ℤ) =
        ((b * M + halfRange b : ℕ) : ℤ) by
      push_cast
      ring]
  rw [nativeCarryPositivePrefix_dirichletTerm_eq,
    nativeCarryDilationChannel_dirichletTerm_eq,
    nativeCarryCenterChannel_dirichletTerm_eq]
  simp only [nsmul_eq_mul]
  ring

/-! ## Limits in the original Dirichlet half-plane -/

/-- Every positive affine camera cutoff tends to infinity. -/
theorem naturalCameraCutoff_tendsto_atTop
    (b h : ℕ) (hb : 1 ≤ b) :
    Tendsto (fun M : ℕ ↦ b * M + h) atTop atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro N
  filter_upwards [eventually_ge_atTop N] with M hM
  calc
    N ≤ M := hM
    _ ≤ b * M := by
      simpa only [one_mul] using Nat.mul_le_mul_right M hb
    _ ≤ b * M + h := Nat.le_add_right _ _

/-- Odd natural cameras select the odd-camera factor already at finite limit. -/
theorem nativeCarryFiniteSaturatedChart_dirichlet_tendsto_odd_factor
    (b : ℕ) (hbodd : Odd b) (hb : 1 < b)
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto
      (fun M : ℕ ↦
        nativeCarryFiniteSaturatedChart b M (dirichletTerm s))
      atTop
      (nhds
        (naturalOddCameraFactor b s * genuineDirichlet s)) := by
  have hprefix := positiveDirichletPrefix_tendsto_genuineDirichlet hs
  have hlong :
      Tendsto
        (fun M : ℕ ↦
          positiveDirichletPrefix s (b * M + halfRange b))
        atTop (nhds (genuineDirichlet s)) := by
    simpa [Function.comp_def] using
      hprefix.comp
        (naturalCameraCutoff_tendsto_atTop b (halfRange b) (by omega))
  have hscaled :
      Tendsto
        (fun M : ℕ ↦
          (b : ℂ) ^ (1 - s) * positiveDirichletPrefix s M)
        atTop
        (nhds ((b : ℂ) ^ (1 - s) * genuineDirichlet s)) :=
    tendsto_const_nhds.mul hprefix
  have hdiff := hlong.sub hscaled
  have hchart :=
    hdiff.congr'
      (Filter.Eventually.of_forall fun M ↦
        (nativeCarryFiniteSaturatedChart_dirichlet_odd_eq
          b M hbodd hb s).symm)
  simpa [naturalOddCameraFactor, cpChartFactor, sub_mul, one_mul] using hchart

/-- Even natural cameras select the factor forced by their missing channel. -/
theorem nativeCarryFiniteSaturatedChart_dirichlet_tendsto_even_factor
    (b : ℕ) (hbeven : Even b) (hb : 2 < b)
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto
      (fun M : ℕ ↦
        nativeCarryFiniteSaturatedChart b M (dirichletTerm s))
      atTop
      (nhds
        (naturalEvenCameraFactor b s * genuineDirichlet s)) := by
  have hprefix := positiveDirichletPrefix_tendsto_genuineDirichlet hs
  have hlong :
      Tendsto
        (fun M : ℕ ↦
          positiveDirichletPrefix s (b * M + halfRange b))
        atTop (nhds (genuineDirichlet s)) := by
    simpa [Function.comp_def] using
      hprefix.comp
        (naturalCameraCutoff_tendsto_atTop b (halfRange b) (by omega))
  have hdouble :
      Tendsto
        (fun M : ℕ ↦ positiveDirichletPrefix s (2 * M))
        atTop (nhds (genuineDirichlet s)) := by
    simpa [Function.comp_def] using
      hprefix.comp (naturalCameraCutoff_tendsto_atTop 2 0 (by norm_num))
  have hmiddle :
      Tendsto
        (fun M : ℕ ↦
          dirichletTerm s ((b / 2 : ℕ) : ℤ) *
            positiveDirichletPrefix s (2 * M))
        atTop
        (nhds
          (dirichletTerm s ((b / 2 : ℕ) : ℤ) * genuineDirichlet s)) :=
    tendsto_const_nhds.mul hdouble
  have hcenter :
      Tendsto
        (fun M : ℕ ↦
          ((b - 2 : ℕ) : ℂ) * dirichletTerm s (b : ℤ) *
            positiveDirichletPrefix s M)
        atTop
        (nhds
          (((b - 2 : ℕ) : ℂ) * dirichletTerm s (b : ℤ) *
            genuineDirichlet s)) :=
    tendsto_const_nhds.mul hprefix
  have hdiff := (hlong.sub hmiddle).sub hcenter
  have hchart :=
    hdiff.congr'
      (Filter.Eventually.of_forall fun M ↦
        (nativeCarryFiniteSaturatedChart_dirichlet_even_eq
          b M hbeven hb s).symm)
  have hhalf :
      dirichletTerm s ((b / 2 : ℕ) : ℤ) =
        ((b / 2 : ℕ) : ℂ) ^ (-s) := by
    unfold dirichletTerm
    apply congrArg (fun z : ℂ ↦ z ^ (-s))
    norm_num
  have hbase :
      dirichletTerm s (b : ℤ) = (b : ℂ) ^ (-s) := by
    simp [dirichletTerm]
  rw [hhalf, hbase] at hchart
  simpa [naturalEvenCameraFactor, sub_mul, one_mul] using hchart

/-- Odd chart identification on the original half-plane of the Dirichlet sum. -/
theorem bracketedDirichletChart_eq_naturalOddCameraFactor_mul_genuineDirichlet
    (b : ℕ) (hbodd : Odd b) (hb : 1 < b)
    {s : ℂ} (hs : 1 < s.re) :
    bracketedDirichletChart b s =
      naturalOddCameraFactor b s * genuineDirichlet s := by
  exact tendsto_nhds_unique
    (nativeCarryFiniteSaturatedChart_dirichlet_tendsto_of_two_le
      b (by omega) (by linarith [hs]))
    (nativeCarryFiniteSaturatedChart_dirichlet_tendsto_odd_factor
      b hbodd hb hs)

/-- Even chart identification on the original half-plane of the Dirichlet sum. -/
theorem bracketedDirichletChart_eq_naturalEvenCameraFactor_mul_genuineDirichlet
    (b : ℕ) (hbeven : Even b) (hb : 2 < b)
    {s : ℂ} (hs : 1 < s.re) :
    bracketedDirichletChart b s =
      naturalEvenCameraFactor b s * genuineDirichlet s := by
  exact tendsto_nhds_unique
    (nativeCarryFiniteSaturatedChart_dirichlet_tendsto_of_two_le
      b (by omega) (by linarith [hs]))
    (nativeCarryFiniteSaturatedChart_dirichlet_tendsto_even_factor
      b hbeven hb hs)

/-! ## One factor for all natural cameras -/

/--
The factor selected by a native natural camera.  The branch is decidable
arithmetic (`b % 2 = 0`), so no primality classification is involved.
-/
def naturalCameraFactor (b : ℕ) (s : ℂ) : ℂ :=
  if b % 2 = 0 then
    naturalEvenCameraFactor b s
  else
    naturalOddCameraFactor b s

/-- The odd branch of the unified factor. -/
theorem naturalCameraFactor_eq_odd
    {b : ℕ} (hbodd : Odd b) (s : ℂ) :
    naturalCameraFactor b s = naturalOddCameraFactor b s := by
  have hmod : b % 2 = 1 := Nat.odd_iff.mp hbodd
  simp [naturalCameraFactor, hmod]

/-- The even branch of the unified factor. -/
theorem naturalCameraFactor_eq_even
    {b : ℕ} (hbeven : Even b) (s : ℂ) :
    naturalCameraFactor b s = naturalEvenCameraFactor b s := by
  have hmod : b % 2 = 0 := Nat.even_iff.mp hbeven
  simp [naturalCameraFactor, hmod]

/-- The odd-camera factor is entire for every positive natural width. -/
theorem differentiable_naturalOddCameraFactor
    (b : ℕ) (hb : 0 < b) :
    Differentiable ℂ (naturalOddCameraFactor b) := by
  have hbComplex : (b : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hb)
  letI : NeZero (b : ℂ) := ⟨hbComplex⟩
  change Differentiable ℂ (fun s : ℂ ↦ 1 - (b : ℂ) ^ (1 - s))
  exact
    (differentiable_const (c := (1 : ℂ))).sub
      ((differentiable_const_cpow_of_neZero (b : ℂ)).comp
        ((differentiable_const (c := (1 : ℂ))).sub differentiable_id))

/-- The even-camera factor is entire for every width at least two. -/
theorem differentiable_naturalEvenCameraFactor
    (b : ℕ) (hb : 2 ≤ b) :
    Differentiable ℂ (naturalEvenCameraFactor b) := by
  have hbComplex : (b : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hb))
  have hhalf : 0 < b / 2 := by omega
  have hhalfComplex : ((b / 2 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hhalf)
  letI : NeZero (b : ℂ) := ⟨hbComplex⟩
  letI : NeZero ((b / 2 : ℕ) : ℂ) := ⟨hhalfComplex⟩
  change Differentiable ℂ
    (fun s : ℂ ↦
      1 - ((b / 2 : ℕ) : ℂ) ^ (-s) -
        ((b - 2 : ℕ) : ℂ) * (b : ℂ) ^ (-s))
  exact
    ((differentiable_const (c := (1 : ℂ))).sub
      ((differentiable_const_cpow_of_neZero
        ((b / 2 : ℕ) : ℂ)).comp differentiable_neg)).sub
      ((differentiable_const (c := ((b - 2 : ℕ) : ℂ))).mul
        ((differentiable_const_cpow_of_neZero (b : ℂ)).comp
          differentiable_neg))

/-- The unified natural-camera factor is entire. -/
theorem differentiable_naturalCameraFactor
    (b : ℕ) (hb : 2 ≤ b) :
    Differentiable ℂ (naturalCameraFactor b) := by
  by_cases hmod : b % 2 = 0
  · have hfun :
        naturalCameraFactor b = naturalEvenCameraFactor b := by
      funext s
      simp [naturalCameraFactor, hmod]
    rw [hfun]
    exact differentiable_naturalEvenCameraFactor b hb
  · have hfun :
        naturalCameraFactor b = naturalOddCameraFactor b := by
      funext s
      simp [naturalCameraFactor, hmod]
    rw [hfun]
    exact differentiable_naturalOddCameraFactor b (by omega)

/-- Analytic form of unified factor regularity. -/
theorem analyticOnNhd_naturalCameraFactor
    (b : ℕ) (hb : 2 ≤ b) :
    AnalyticOnNhd ℂ (naturalCameraFactor b) bracketHalfPlane := by
  exact
    (differentiable_naturalCameraFactor b hb).differentiableOn.analyticOnNhd
      isOpen_bracketHalfPlane

/-- Unified factorization on the original Dirichlet half-plane. -/
theorem bracketedDirichletChart_eq_naturalCameraFactor_mul_genuineDirichlet
    (b : ℕ) (hb : 3 ≤ b)
    {s : ℂ} (hs : 1 < s.re) :
    bracketedDirichletChart b s =
      naturalCameraFactor b s * genuineDirichlet s := by
  by_cases hmod : b % 2 = 0
  · have hbeven : Even b := Nat.even_iff.mpr hmod
    rw [naturalCameraFactor_eq_even hbeven]
    exact
      bracketedDirichletChart_eq_naturalEvenCameraFactor_mul_genuineDirichlet
        b hbeven (by omega) hs
  · have hoddmod : b % 2 = 1 := by omega
    have hbodd : Odd b := Nat.odd_iff.mpr hoddmod
    rw [naturalCameraFactor_eq_odd hbodd]
    exact
      bracketedDirichletChart_eq_naturalOddCameraFactor_mul_genuineDirichlet
        b hbodd (by omega) hs

/-! ## Camera-independent analytic continuation -/

/-- Left side of the cross-normalized natural-camera identity. -/
def naturalCameraCrossLeft (b : ℕ) (s : ℂ) : ℂ :=
  cpChartFactor 3 s * bracketedDirichletChart b s

/-- Right side of the cross-normalized natural-camera identity. -/
def naturalCameraCrossRight (b : ℕ) (s : ℂ) : ℂ :=
  naturalCameraFactor b s * bracketedDirichletChart 3 s

/-- The left cross product is holomorphic on the bracket half-plane. -/
theorem analyticOnNhd_naturalCameraCrossLeft
    (b : ℕ) (hb : 3 ≤ b) :
    AnalyticOnNhd ℂ (naturalCameraCrossLeft b) bracketHalfPlane := by
  have hfactorAll : AnalyticOnNhd ℂ (cpChartFactor 3) Set.univ :=
    (differentiable_cpChartFactor 3 (by norm_num)).differentiableOn.analyticOnNhd
      isOpen_univ
  have hfactor : AnalyticOnNhd ℂ (cpChartFactor 3) bracketHalfPlane :=
    hfactorAll.mono (subset_univ _)
  exact hfactor.mul
    (analyticOnNhd_bracketedDirichletChart_of_two_le b (by omega))

/-- The right cross product is holomorphic on the bracket half-plane. -/
theorem analyticOnNhd_naturalCameraCrossRight
    (b : ℕ) (hb : 3 ≤ b) :
    AnalyticOnNhd ℂ (naturalCameraCrossRight b) bracketHalfPlane := by
  exact
    (analyticOnNhd_naturalCameraFactor b (by omega)).mul
      (analyticOnNhd_bracketedDirichletChart 3 (by norm_num))

/-- The two cross products agree in the original Dirichlet half-plane. -/
theorem naturalCameraCrossLeft_eq_right_of_one_lt_re
    (b : ℕ) (hb : 3 ≤ b)
    {s : ℂ} (hs : 1 < s.re) :
    naturalCameraCrossLeft b s = naturalCameraCrossRight b s := by
  unfold naturalCameraCrossLeft naturalCameraCrossRight
  rw [bracketedDirichletChart_eq_naturalCameraFactor_mul_genuineDirichlet
      b hb hs,
    bracketedDirichletChart_eq_cpChartFactor_mul_genuineDirichlet
      3 (by norm_num) (by norm_num) hs]
  ring

/--
Analytic continuation of the cross identity to the full half-plane
`re(s) > -1`.
-/
theorem naturalCameraCrossLeft_eq_right
    (b : ℕ) (hb : 3 ≤ b) :
    Set.EqOn (naturalCameraCrossLeft b)
      (naturalCameraCrossRight b) bracketHalfPlane := by
  have hrightOpen : IsOpen {s : ℂ | 1 < s.re} := by
    exact isOpen_lt continuous_const Complex.continuous_re
  have hrightMem : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
    hrightOpen.mem_nhds (by norm_num)
  have heventually :
      naturalCameraCrossLeft b =ᶠ[𝓝 (2 : ℂ)]
        naturalCameraCrossRight b := by
    filter_upwards [hrightMem] with s hs
    exact naturalCameraCrossLeft_eq_right_of_one_lt_re b hb hs
  exact
    (analyticOnNhd_naturalCameraCrossLeft b hb).eqOn_of_preconnected_of_eventuallyEq
      (analyticOnNhd_naturalCameraCrossRight b hb)
      isPreconnected_bracketHalfPlane
      (by norm_num [bracketHalfPlane]) heventually

/-- Pointwise cross identity on the full bracket half-plane. -/
theorem naturalCameraCrossLeft_eq_right_at
    (b : ℕ) (hb : 3 ≤ b)
    {s : ℂ} (hs : -1 < s.re) :
    naturalCameraCrossLeft b s = naturalCameraCrossRight b s :=
  naturalCameraCrossLeft_eq_right b hb hs

/--
Every natural camera is its exact finite-algebra factor times the same
canonical Genuine continuation throughout the critical strip.
-/
theorem bracketedDirichletChart_eq_naturalCameraFactor_mul_genuineContinuation
    (b : ℕ) (hb : 3 ≤ b)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    bracketedDirichletChart b s =
      naturalCameraFactor b s * genuineContinuation s := by
  have hcross :=
    naturalCameraCrossLeft_eq_right_at b hb (s := s) (by linarith [hs.1])
  have hthree :=
    bracketedDirichletChart_eq_cpChartFactor_mul_genuineContinuation
      3 (by norm_num) (by norm_num) hs
  have hfactor :
      cpChartFactor 3 s ≠ 0 :=
    cpChartFactor_ne_zero_on_genuineCriticalStrip 3 (by norm_num) hs
  unfold naturalCameraCrossLeft naturalCameraCrossRight at hcross
  rw [hthree] at hcross
  apply mul_left_cancel₀ hfactor
  calc
    cpChartFactor 3 s * bracketedDirichletChart b s =
        naturalCameraFactor b s *
          (cpChartFactor 3 s * genuineContinuation s) := hcross
    _ = cpChartFactor 3 s *
          (naturalCameraFactor b s * genuineContinuation s) := by ring

/--
Direct limit form: on the critical strip the native finite scanner converges
to the camera factor times the one canonical Genuine continuation.
-/
theorem nativeCarryFiniteSaturatedChart_dirichlet_tendsto_factor_mul_genuineContinuation
    (b : ℕ) (hb : 3 ≤ b)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ ↦
        nativeCarryFiniteSaturatedChart b M (dirichletTerm s))
      atTop
      (nhds (naturalCameraFactor b s * genuineContinuation s)) := by
  have hlim :=
    nativeCarryFiniteSaturatedChart_dirichlet_tendsto_of_two_le
      b (by omega) (s := s) (by linarith [hs.1])
  rw [bracketedDirichletChart_eq_naturalCameraFactor_mul_genuineContinuation
    b hb hs] at hlim
  exact hlim

/-! ## Critical-line zero independence -/

/-- Every material natural-camera factor is nonzero on the critical line. -/
theorem naturalCameraFactor_ne_zero_on_criticalLine
    (b : ℕ) (hb : 3 ≤ b)
    {s : ℂ} (hs : s.re = (1 : ℝ) / 2) :
    naturalCameraFactor b s ≠ 0 := by
  by_cases hmod : b % 2 = 0
  · have hbeven : Even b := Nat.even_iff.mpr hmod
    rw [naturalCameraFactor_eq_even hbeven]
    by_cases hbFour : b = 4
    · subst b
      exact naturalEvenCameraFactor_four_ne_zero_on_criticalLine hs
    · have hbSix : 6 ≤ b := by
        rcases hbeven with ⟨d, rfl⟩
        omega
      exact
        naturalEvenCameraFactor_ne_zero_on_criticalLine_of_six_le
          b hbeven hbSix hs
  · have hoddmod : b % 2 = 1 := by omega
    have hbodd : Odd b := Nat.odd_iff.mpr hoddmod
    rw [naturalCameraFactor_eq_odd hbodd]
    exact
      naturalOddCameraFactor_ne_zero_on_criticalLine
        b hbodd (by omega) hs

/--
On the critical line, every natural camera has exactly the zeros of the
canonical Genuine continuation.
-/
theorem bracketedDirichletChart_zero_iff_genuineContinuation_zero_of_three_le
    (b : ℕ) (hb : 3 ≤ b)
    {s : ℂ} (hs : s.re = (1 : ℝ) / 2) :
    bracketedDirichletChart b s = 0 ↔ genuineContinuation s = 0 := by
  have hsStrip : s ∈ genuineCriticalStrip := by
    constructor <;> linarith
  rw [bracketedDirichletChart_eq_naturalCameraFactor_mul_genuineContinuation
    b hb hsStrip]
  simp [naturalCameraFactor_ne_zero_on_criticalLine b hb hs]

/-! ## The aligned camera labelled `C₂` -/

/--
The finite aligned `C₂` scanner converges because it is exactly width four.
-/
theorem nativeCarryAlignedC2Chart_dirichlet_tendsto
    {s : ℂ} (hs : -1 < s.re) :
    Tendsto
      (fun M : ℕ ↦ nativeCarryAlignedC2Chart M (dirichletTerm s))
      atTop (nhds (bracketedDirichletChart 4 s)) := by
  exact
    (nativeCarryFiniteSaturatedChart_dirichlet_tendsto_of_two_le
      4 (by norm_num) hs).congr'
      (Filter.Eventually.of_forall fun M ↦
        (nativeCarryAlignedC2Chart_eq_width_four M (dirichletTerm s)).symm)

/-- The aligned `C₂` limit has the exact width-four even factor. -/
theorem alignedC2BracketedDirichletChart_eq_factor_mul_genuineContinuation
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    bracketedDirichletChart 4 s =
      naturalEvenCameraFactor 4 s * genuineContinuation s := by
  simpa [naturalCameraFactor] using
    (bracketedDirichletChart_eq_naturalCameraFactor_mul_genuineContinuation
      4 (by norm_num) hs)

/-- Direct factored limit of the specially labelled aligned `C₂` scanner. -/
theorem nativeCarryAlignedC2Chart_dirichlet_tendsto_factor_mul_genuineContinuation
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ ↦ nativeCarryAlignedC2Chart M (dirichletTerm s))
      atTop
      (nhds
        (naturalEvenCameraFactor 4 s * genuineContinuation s)) := by
  have hlim :=
    nativeCarryAlignedC2Chart_dirichlet_tendsto
      (s := s) (by linarith [hs.1])
  rw [alignedC2BracketedDirichletChart_eq_factor_mul_genuineContinuation hs]
    at hlim
  exact hlim

/-- The aligned `C₂` limit detects exactly the canonical critical zeros. -/
theorem alignedC2BracketedDirichletChart_zero_iff_genuineContinuation_zero
    {s : ℂ} (hs : s.re = (1 : ℝ) / 2) :
    bracketedDirichletChart 4 s = 0 ↔ genuineContinuation s = 0 := by
  exact
    bracketedDirichletChart_zero_iff_genuineContinuation_zero_of_three_le
      4 (by norm_num) hs

end

end CPFormal.Analytic.Cp
