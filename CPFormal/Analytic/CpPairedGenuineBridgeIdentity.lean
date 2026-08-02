import CPFormal.Analytic.CpPairedGenuineBridgeAnalytic
import CPFormal.Analytic.CpGenuineCompatibility

/-!
# The paired-channel identity on the whole critical strip

Combining the closed form on `re s > 1` with the holomorphy of the paired
channel, the identity

`pairedAltChannel s = (1 - 2^(1-s)) * genuineContinuation s`

is transported to the whole open critical strip.  The transport avoids the pole
of `genuineContinuation` at `s = 1` by clearing the camera factor: the cleared
identity

`cpChartFactor 3 s * pairedAltChannel s = (1 - 2^(1-s)) * bracketedDirichletChart 3 s`

holds on the connected half-plane `re s > 0`, where both sides are honestly
holomorphic, and the factor is cancelled only on the strip where it is nonzero.
-/

open Complex

open scoped Topology

namespace CPFormal.Analytic.Cp

noncomputable section

/-- The right half-plane is convex, hence preconnected. -/
theorem isPreconnected_rightHalfPlane :
    IsPreconnected {z : ℂ | 0 < z.re} := by
  have hconv : Convex ℝ {z : ℂ | 0 < z.re} := by
    intro z hz w hw a b ha hb hab
    simp only [Set.mem_setOf_eq, Complex.add_re, Complex.smul_re, smul_eq_mul] at hz hw ⊢
    rcases eq_or_lt_of_le ha with rfl | haPos
    · have hb1 : b = 1 := by linarith
      subst hb1; simpa using hw
    · have h1 : 0 < a * z.re := mul_pos haPos hz
      have h2 : 0 ≤ b * w.re := mul_nonneg hb (le_of_lt hw)
      linarith
  exact hconv.isPreconnected

/-- Cleared paired-channel identity, valid on the whole open right half-plane. -/
theorem cpChartFactor_mul_pairedAltChannel_eq
    {s : ℂ} (hs : 0 < s.re) :
    cpChartFactor 3 s * pairedAltChannel s =
      (1 - (2 : ℂ) ^ (1 - s)) * bracketedDirichletChart 3 s := by
  have h3 : Nat.Prime 3 := by norm_num
  have h3odd : Odd 3 := by decide
  have hU_open : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hdiff2 : Differentiable ℂ (fun z : ℂ => 1 - (2 : ℂ) ^ (1 - z)) := by
    have h2 : (2 : ℂ) ≠ 0 := by norm_num
    letI : NeZero (2 : ℂ) := ⟨h2⟩
    exact (differentiable_const (c := (1 : ℂ))).sub
      ((differentiable_const_cpow_of_neZero (2 : ℂ)).comp
        ((differentiable_const (c := (1 : ℂ))).sub differentiable_id))
  have hLan : AnalyticOnNhd ℂ
      (fun z => cpChartFactor 3 z * pairedAltChannel z) {z : ℂ | 0 < z.re} :=
    AnalyticOnNhd.mul
      ((differentiable_cpChartFactor 3 h3).differentiableOn.analyticOnNhd hU_open)
      analyticOnNhd_pairedAltChannel
  have hRan : AnalyticOnNhd ℂ
      (fun z => (1 - (2 : ℂ) ^ (1 - z)) * bracketedDirichletChart 3 z)
      {z : ℂ | 0 < z.re} :=
    AnalyticOnNhd.mul
      (hdiff2.differentiableOn.analyticOnNhd hU_open)
      ((analyticOnNhd_bracketedDirichletChart 3 h3).mono (fun z hz => by
        show -1 < z.re
        have : (0 : ℝ) < z.re := hz
        linarith))
  have hev : (fun z => cpChartFactor 3 z * pairedAltChannel z)
      =ᶠ[𝓝 (2 : ℂ)] (fun z => (1 - (2 : ℂ) ^ (1 - z)) * bracketedDirichletChart 3 z) := by
    have hmem : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) := by
      refine (isOpen_lt continuous_const Complex.continuous_re).mem_nhds ?_
      show (1 : ℝ) < (2 : ℂ).re
      norm_num
    filter_upwards [hmem] with z hz
    have hz1 : 1 < z.re := hz
    rw [pairedAltChannel_eq_of_one_lt_re hz1,
      bracketedDirichletChart_eq_genuine_factor 3 h3 h3odd hz1]
    simp only [cpChartFactor]
    ring
  have h2mem : (2 : ℂ) ∈ {z : ℂ | 0 < z.re} := by
    show (0 : ℝ) < (2 : ℂ).re
    norm_num
  have heqOn := hLan.eqOn_of_preconnected_of_eventuallyEq hRan
    isPreconnected_rightHalfPlane h2mem hev
  have hkey := heqOn hs
  simpa using hkey

/-- The paired-channel identity on the whole open critical strip. -/
theorem pairedAltChannel_eq_genuineContinuation
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    pairedAltChannel s = (1 - (2 : ℂ) ^ (1 - s)) * genuineContinuation s := by
  have h3 : Nat.Prime 3 := by norm_num
  have h3odd : Odd 3 := by decide
  have hfac : cpChartFactor 3 s ≠ 0 :=
    cpChartFactor_ne_zero_on_genuineCriticalStrip 3 h3 hs
  have hkey := cpChartFactor_mul_pairedAltChannel_eq hs.1
  rw [bracketedDirichletChart_eq_cpChartFactor_mul_genuineContinuation 3 h3 h3odd hs]
    at hkey
  have hcancel : cpChartFactor 3 s * pairedAltChannel s =
      cpChartFactor 3 s * ((1 - (2 : ℂ) ^ (1 - s)) * genuineContinuation s) := by
    rw [hkey]; ring
  exact mul_left_cancel₀ hfac hcancel

/-- On the strip the eta-type factor `1 - 2^(1-s)` never vanishes. -/
theorem one_sub_two_cpow_one_sub_ne_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    (1 : ℂ) - (2 : ℂ) ^ (1 - s) ≠ 0 := by
  obtain ⟨_, hlt⟩ := hs
  have hnorm : ‖(2 : ℂ) ^ (1 - s)‖ = (2 : ℝ) ^ (1 - s.re) := by
    have h := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) (1 - s)
    simpa [Complex.sub_re, Complex.one_re] using h
  have hgt : (1 : ℝ) < ‖(2 : ℂ) ^ (1 - s)‖ := by
    rw [hnorm]
    have h0 : (2 : ℝ) ^ (0 : ℝ) < (2 : ℝ) ^ (1 - s.re) := by
      rw [Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)]; linarith
    rwa [Real.rpow_zero] at h0
  intro h
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at hgt
  exact lt_irrefl 1 hgt

/-- Native zero-equivalence on the strip: the paired channel and the canonical
Genuine continuation have exactly the same zeros. -/
theorem pairedAltChannel_eq_zero_iff_genuineContinuation
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    pairedAltChannel s = 0 ↔ genuineContinuation s = 0 := by
  rw [pairedAltChannel_eq_genuineContinuation hs]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (one_sub_two_cpow_one_sub_ne_zero hs)
  · intro h; rw [h, mul_zero]

end

end CPFormal.Analytic.Cp
