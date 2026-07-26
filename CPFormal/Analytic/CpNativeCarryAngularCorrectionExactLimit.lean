import CPFormal.Analytic.CpFiniteScalarSynthesisClosedDefectObstruction
import CPFormal.Analytic.CpNativeCarryReflectedLogGreenFluxCrosswalk

/-!
# Exact limit of the angular correction at a Genuine zero

The scalar angular readout decomposes exactly as

`ScalarPairing_M = GreenPairing_(3M) + GreenCorrection_M`.

At a Genuine zero the scalar pairing tends to zero, while the Green pairing
tends to the strictly positive infinite reflected pairing.  Hence the
correction does not become a small error: it converges exactly to the negative
Green pairing.

After multiplication by the radial carry coefficient, the correction converges
to the negative infinite Green bulk.  Therefore asking the scaled correction
to close is equivalent to asking the critical displacement to vanish.  This
module is a guardrail: the last operator obligation cannot be discharged by a
tail estimate that silently assumes the desired criticality.
-/

open scoped Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-- Resolve the angular budget for the correction. -/
theorem finiteCanonicalAngularGreenCorrection_eq_scalar_sub_green
    (M : ℕ) (s : ℂ) :
    finiteCanonicalAngularGreenCorrection M s =
      finiteCanonicalAngularScalarPairing M s -
        finiteReflectedGradientPairing (3 * M) s := by
  have hbudget :=
    finiteCanonicalAngularScalarPairing_eq_green_add_correction M s
  linear_combination hbudget

/-- The cofinal reindexing `M ↦ 3M` tends to infinity. -/
theorem tendsto_three_mul_atTop :
    Tendsto (fun M : ℕ => 3 * M) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop N] with M hM
  omega

/-- At a Genuine zero, the angular correction converges to the negative
infinite reflected Green pairing. -/
theorem finiteCanonicalAngularGreenCorrection_tendsto_neg_infinitePairing_of_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
      (fun M : ℕ => finiteCanonicalAngularGreenCorrection M s)
      atTop (nhds (-infiniteReflectedGradientPairing s)) := by
  have hscalar :=
    finiteCanonicalAngularScalarPairing_tendsto_zero_of_genuine_zero hs hzero
  have hgreen :=
    (finiteReflectedGradientPairing_tendsto_infinite hs).comp
      tendsto_three_mul_atTop
  have hsub := hscalar.sub hgreen
  have hpoint :
      (fun M : ℕ => finiteCanonicalAngularGreenCorrection M s) =
        (fun M : ℕ =>
          finiteCanonicalAngularScalarPairing M s -
            finiteReflectedGradientPairing (3 * M) s) := by
    funext M
    exact finiteCanonicalAngularGreenCorrection_eq_scalar_sub_green M s
  rw [hpoint]
  simpa using hsub

/-- The radially scaled correction has the exact opposite of the infinite Green
bulk as its limit. -/
theorem finiteCanonicalAngularScaledGreenCorrection_tendsto_neg_infiniteBulk_of_genuine_zero
    (p : ℕ) {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
      (fun M : ℕ =>
        ((cpRadialDifference p (criticalDisplacement s.re) : ℝ) : ℂ) *
          finiteCanonicalAngularGreenCorrection M s)
      atTop
      (nhds
        (-((cpRadialDifference p (criticalDisplacement s.re) : ℝ) : ℂ) *
          infiniteReflectedGradientPairing s)) := by
  have hcorr :=
    finiteCanonicalAngularGreenCorrection_tendsto_neg_infinitePairing_of_genuine_zero
      hs hzero
  have hscaled :=
    (tendsto_const_nhds :
      Tendsto
        (fun _ : ℕ =>
          ((cpRadialDifference p (criticalDisplacement s.re) : ℝ) : ℂ))
        atTop
        (nhds
          ((cpRadialDifference p (criticalDisplacement s.re) : ℝ) : ℂ))).mul
      hcorr
  simpa using hscaled

/-- The infinite reflected pairing is nonzero because its real part is strictly
positive throughout the Genuine strip. -/
theorem infiniteReflectedGradientPairing_ne_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    infiniteReflectedGradientPairing s ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  have hpos := infiniteReflectedGreenEnergy_pos hs
  unfold infiniteReflectedGreenEnergy at hpos
  simp only [Complex.zero_re] at hre
  linarith

/-- Exact no-hidden-hypothesis statement: at a Genuine zero, closing the scaled
angular correction is equivalent to criticality. -/
theorem scaledAngularGreenCorrection_closes_iff_criticalDisplacement_eq_zero
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
        (fun M : ℕ =>
          ((cpRadialDifference p (criticalDisplacement s.re) : ℝ) : ℂ) *
            finiteCanonicalAngularGreenCorrection M s)
        atTop (nhds 0) ↔
      criticalDisplacement s.re = 0 := by
  let c : ℂ :=
    ((cpRadialDifference p (criticalDisplacement s.re) : ℝ) : ℂ)
  let E : ℂ := infiniteReflectedGradientPairing s
  have hlimit :
      Tendsto
        (fun M : ℕ =>
          ((cpRadialDifference p (criticalDisplacement s.re) : ℝ) : ℂ) *
            finiteCanonicalAngularGreenCorrection M s)
        atTop (nhds (-c * E)) := by
    simpa [c, E] using
      finiteCanonicalAngularScaledGreenCorrection_tendsto_neg_infiniteBulk_of_genuine_zero
        p hs hzero
  constructor
  · intro hcloses
    have hproduct : -c * E = 0 := tendsto_nhds_unique hlimit hcloses
    have hE : E ≠ 0 := by
      simpa [E] using infiniteReflectedGradientPairing_ne_zero hs
    have hc : c = 0 := by
      have hnegc : -c = 0 :=
        (mul_eq_zero.mp hproduct).resolve_right hE
      linarith
    have hradial :
        cpRadialDifference p (criticalDisplacement s.re) = 0 := by
      exact_mod_cast hc
    exact
      (cpRadialDifference_eq_zero_iff
        p hp (criticalDisplacement s.re)).mp hradial
  · intro hcritical
    have hradial :
        cpRadialDifference p (criticalDisplacement s.re) = 0 :=
      (cpRadialDifference_eq_zero_iff
        p hp (criticalDisplacement s.re)).2 hcritical
    simpa [hradial] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (nhds 0))

/-- Consequently the old one-sided correction bridge is exactly the strong
complex-time zero-rigidity statement, not a weaker decay lemma. -/
theorem genuineOneSidedAngularGreenBridge_iff_zeroRigidity
    (p : ℕ) (hp : Nat.Prime p) :
    GenuineOneSidedAngularGreenBridge p ↔
      NativeCarryComplexTimeZeroRigidity := by
  constructor
  · intro bridge z hz hres
    have hzero : genuineContinuation (carryComplexTimeParameter z) = 0 := by
      simpa [IsNativeCarryComplexTimeResonance, carryComplexTimeGenuine] using hres
    have hcritical :=
      (scaledAngularGreenCorrection_closes_iff_criticalDisplacement_eq_zero
        p hp hz hzero).1
        (bridge.scaled_correction_closes hzero hz)
    rw [criticalDisplacement_carryComplexTimeParameter_re] at hcritical
    linarith
  · intro hrigid
    refine ⟨?_⟩
    intro s hzero hs
    let z := carryComplexTimeOfParameter s
    have hz : carryComplexTimeParameter z = s := by
      simp [z]
    have hres : IsNativeCarryComplexTimeResonance z := by
      unfold IsNativeCarryComplexTimeResonance carryComplexTimeGenuine
      simpa [hz] using hzero
    have him : z.im = 0 := hrigid z (by simpa [hz] using hs) hres
    have hcritical : criticalDisplacement s.re = 0 := by
      have hzIm := carryComplexTimeOfParameter_im s
      dsimp [z] at him
      linarith
    exact
      (scaledAngularGreenCorrection_closes_iff_criticalDisplacement_eq_zero
        p hp hs hzero).2 hcritical

end

end CPFormal.Analytic.Cp
