import CPFormal.Analytic.CpC2GpreCofinalTaggedSynthesis
import CPFormal.Analytic.CpCarryAmplitudeIdentification
import CPFormal.Analytic.CpGenuineGreenKernelInclusion

/-!
# Guard for activating Green closure from the tagged C2 synthesis

The cofinal tagged `G_pre` synthesis is an exact realization of the horizontal
cross-prime camera gap.  Its zero is therefore a rank-one scalar compression:
the two camera channels are subtracted only after all native tags have been
read.

The quadratic carry/Green channel is different.  It keeps camera coordinates
orthogonal and measures them with positive amplitudes `p^(-k/2)`.  A diagonal
pair `(z,z)` has zero scalar difference but positive quadratic energy.  Thus
positivity of the carry amplitudes does not turn scalar cancellation into
Green closure.

This module records that obstruction in the kernel and names the exact missing
activation statement.  For any fixed cofinal tagged atlas family, the claim

`tagged synthesis closes at a Genuine zero -> aligned Green closure`

is proved equivalent to the existing strong nonvanishing statement.  The same
is true if the target is phrased as saturation of the quadratic branch norm.
No instance of either activation statement is declared here.
-/

open scoped Topology

namespace CPFormal.Analytic.Cp

open Filter
open CPFormal.Carry.Cp

noncomputable section

/-! ## Scalar compression versus quadratic carry energy -/

/-- Rank-one compression used by the horizontal two-camera gap. -/
def c2GpreCameraPairCompression (z : ℂ × ℂ) : ℂ :=
  z.1 - z.2

/-- Positive quadratic energy before the two camera coordinates are compressed. -/
def c2GpreCameraPairQuadraticEnergy (z : ℂ × ℂ) : ℝ :=
  ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2

/-- The actual carry amplitudes may be inserted independently in both camera
coordinates. -/
def c2GpreCarryWeightedCameraPairEnergy
    (p q kp kq : ℕ) (z : ℂ × ℂ) : ℝ :=
  (criticalAmplitude p kp) ^ 2 * ‖z.1‖ ^ 2 +
    (criticalAmplitude q kq) ^ 2 * ‖z.2‖ ^ 2

@[simp] theorem c2GpreCameraPairCompression_diagonal (z : ℂ) :
    c2GpreCameraPairCompression (z, z) = 0 := by
  simp [c2GpreCameraPairCompression]

@[simp] theorem c2GpreCameraPairQuadraticEnergy_one_one :
    c2GpreCameraPairQuadraticEnergy ((1 : ℂ), (1 : ℂ)) = 2 := by
  norm_num [c2GpreCameraPairQuadraticEnergy]

/-- Even after inserting the canonical positive amplitudes `p^(-k/2)`, a
nonzero diagonal camera pair has zero scalar compression and positive energy. -/
theorem c2GpreCameraPairCompression_zero_with_positive_carryEnergy
    (p q kp kq : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    c2GpreCameraPairCompression ((1 : ℂ), (1 : ℂ)) = 0 ∧
      0 < c2GpreCarryWeightedCameraPairEnergy p q kp kq
        ((1 : ℂ), (1 : ℂ)) := by
  constructor
  · simp
  · have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq.pos
    have hmp : 0 < criticalMass p kp := by
      unfold criticalMass
      exact Real.rpow_pos_of_pos hp0 _
    have hmq : 0 < criticalMass q kq := by
      unfold criticalMass
      exact Real.rpow_pos_of_pos hq0 _
    simpa [c2GpreCarryWeightedCameraPairEnergy] using add_pos hmp hmq

/-- Therefore scalar camera cancellation is not coercive for the quadratic
carry energy. -/
theorem c2GpreCameraPairCompression_not_carryEnergy_coercive
    (p q kp kq : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    ¬ (∀ z : ℂ × ℂ,
      c2GpreCameraPairCompression z = 0 →
        c2GpreCarryWeightedCameraPairEnergy p q kp kq z = 0) := by
  intro hcoercive
  have hwitness :=
    c2GpreCameraPairCompression_zero_with_positive_carryEnergy
      p q kp kq hp hq
  have hzero := hcoercive ((1 : ℂ), (1 : ℂ)) hwitness.1
  exact (ne_of_gt hwitness.2) hzero

/-! ## The tagged synthesis is exactly that rank-one compression -/

/-- The two camera syntheses retained as separate complex coordinates before
forming their horizontal difference. -/
def c2GpreNormalizedCofinalTaggedCameraPair
    (verticalRatio : ℝ) {p q : ℕ}
    (family : C2GpreActiveCofinalAtlasFamily p q)
    (L : ℕ) (s : ℂ) : ℂ × ℂ :=
  (c2GpreNormalizedCameraPrefixTaggedSynthesis
      verticalRatio (family.support L) p
      (crossPrimeAlignedCutoff q L) (family.pPrefix L) s,
    c2GpreNormalizedCameraPrefixTaggedSynthesis
      verticalRatio (family.support L) q
      (crossPrimeAlignedCutoff p L) (family.qPrefix L) s)

/-- The previously proved tagged gap is obtained by applying the rank-one
compression to the separated camera pair. -/
theorem c2GpreNormalizedCofinalTaggedSynthesis_eq_pairCompression
    (verticalRatio : ℝ) {p q : ℕ}
    (family : C2GpreActiveCofinalAtlasFamily p q)
    (L : ℕ) (s : ℂ) :
    c2GpreNormalizedCofinalTaggedSynthesis verticalRatio family L s =
      c2GpreCameraPairCompression
        (c2GpreNormalizedCofinalTaggedCameraPair
          verticalRatio family L s) := by
  rfl

/-! ## Exact logical status of the requested activation -/

/-- Claim that closure of the tagged horizontal synthesis activates the actual
coordinatewise aligned Green closure. -/
def C2GpreTaggedSynthesisActivatesGreenClosure
    (verticalRatio : ℝ) {p q : ℕ}
    (family : C2GpreActiveCofinalAtlasFamily p q) : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    genuineContinuation s = 0 →
    Tendsto
      (fun L : ℕ =>
        c2GpreNormalizedCofinalTaggedSynthesis
          verticalRatio family L s)
      atTop (nhds 0) →
    CrossPrimeAlignedGreenClosure p q s

/-- For a fixed tagged family, activating Green closure from its already known
horizontal closure is exactly the strong Genuine nonvanishing statement. -/
theorem c2GpreTaggedSynthesisActivatesGreenClosure_iff_strongNonvanishing
    (verticalRatio : ℝ) {p q : ℕ}
    (family : C2GpreActiveCofinalAtlasFamily p q)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q) :
    C2GpreTaggedSynthesisActivatesGreenClosure verticalRatio family ↔
      GenuineStrongNonvanishingInStrip := by
  constructor
  · intro hactivate s hs hoff hzero
    have htagged :=
      c2GpreNormalizedCofinalTaggedSynthesis_tendsto_zero_of_genuine_zero
        verticalRatio family hp hpodd hq hqodd hs hzero
    have hgreen := hactivate hs hzero htagged
    have hcritical :=
      (crossPrimeAlignedGreenClosure_iff_criticalDisplacement_eq_zero
        p q hp hpodd hq hqodd hs hzero).1 hgreen
    apply hoff
    unfold criticalDisplacement at hcritical
    linarith
  · intro hstrong s hs hzero _htagged
    have hcritical : criticalDisplacement s.re = 0 := by
      by_contra hne
      have hoff : s.re ≠ (1 : ℝ) / 2 := by
        intro hre
        apply hne
        unfold criticalDisplacement
        linarith
      exact (hstrong hs hoff) hzero
    exact
      (crossPrimeAlignedGreenClosure_iff_criticalDisplacement_eq_zero
        p q hp hpodd hq hqodd hs hzero).2 hcritical

/-- The same requested activation phrased through saturation of the quadratic
branch norm determined by the amplitudes `r^(-k/2)`. -/
def C2GpreTaggedSynthesisActivatesCarrySaturation
    (verticalRatio : ℝ) {p q r : ℕ}
    (family : C2GpreActiveCofinalAtlasFamily p q) : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    genuineContinuation s = 0 →
    Tendsto
      (fun L : ℕ =>
        c2GpreNormalizedCofinalTaggedSynthesis
          verticalRatio family L s)
      atTop (nhds 0) →
    branchNormSq r s.re = 1

/-- Asking the tagged scalar closure to force saturation of the carry norm is
again exactly the strong nonvanishing theorem. -/
theorem c2GpreTaggedSynthesisActivatesCarrySaturation_iff_strongNonvanishing
    (verticalRatio : ℝ) {p q r : ℕ}
    (family : C2GpreActiveCofinalAtlasFamily p q)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    (hr : Nat.Prime r) :
    C2GpreTaggedSynthesisActivatesCarrySaturation
        verticalRatio (r := r) family ↔
      GenuineStrongNonvanishingInStrip := by
  constructor
  · intro hactivate s hs hoff hzero
    have htagged :=
      c2GpreNormalizedCofinalTaggedSynthesis_tendsto_zero_of_genuine_zero
        verticalRatio family hp hpodd hq hqodd hs hzero
    have hnorm := hactivate hs hzero htagged
    have hre : s.re = (1 : ℝ) / 2 :=
      (branchNormSq_eq_one_iff r hr hs.1).1 hnorm
    exact hoff hre
  · intro hstrong s hs hzero _htagged
    apply (branchNormSq_eq_one_iff r hr hs.1).2
    by_contra hoff
    exact (hstrong hs hoff) hzero

/-- The carry-amplitude and Green-closure formulations of the missing
activation have exactly the same logical strength. -/
theorem c2GpreTaggedGreenActivation_iff_carrySaturationActivation
    (verticalRatio : ℝ) {p q r : ℕ}
    (family : C2GpreActiveCofinalAtlasFamily p q)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    (hr : Nat.Prime r) :
    C2GpreTaggedSynthesisActivatesGreenClosure verticalRatio family ↔
      C2GpreTaggedSynthesisActivatesCarrySaturation
        verticalRatio (r := r) family := by
  rw [c2GpreTaggedSynthesisActivatesGreenClosure_iff_strongNonvanishing
      verticalRatio family hp hpodd hq hqodd,
    c2GpreTaggedSynthesisActivatesCarrySaturation_iff_strongNonvanishing
      verticalRatio family hp hpodd hq hqodd hr]

/-- Conditional composition of the requested chain, with the exact missing
activation premise visible. -/
theorem criticalDisplacement_eq_zero_of_c2GpreTaggedGreenActivation
    (verticalRatio : ℝ) {p q : ℕ}
    (family : C2GpreActiveCofinalAtlasFamily p q)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    (hactivate :
      C2GpreTaggedSynthesisActivatesGreenClosure verticalRatio family)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    criticalDisplacement s.re = 0 := by
  apply
    (crossPrimeAlignedGreenClosure_iff_criticalDisplacement_eq_zero
      p q hp hpodd hq hqodd hs hzero).1
  exact hactivate hs hzero
    (c2GpreNormalizedCofinalTaggedSynthesis_tendsto_zero_of_genuine_zero
      verticalRatio family hp hpodd hq hqodd hs hzero)

end

end CPFormal.Analytic.Cp
