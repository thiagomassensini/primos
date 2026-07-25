import CPFormal.Analytic.CpC2GpreCofinalSynthesis

/-!
# Tagged `G_pre` realization of the cofinal C2 synthesis

`CpC2GpreCofinalSynthesis` constructs the exact finite sum of normalized
log-Dirichlet atoms and proves that it is the aligned two-camera prefix gap.
This module realizes every summand literally as a readout of an active native
`G_pre` provenance tag.

The atlas is allowed to grow with the cofinal level.  At level `L`, it contains
one active context for every frequency in the two finite camera prefixes.  The
synthesis first reads each atom from `data.2.1`, multiplies it by the fixed
camera weight, and only then sums.  The kernel proves that this tagged
construction is exactly the atom synthesis, hence exactly the camera gap.

Existence of a particular arithmetic choice of active tags is deliberately
kept separate from the spectral reindexing: the structure below records only
the nonzero native coefficients required for coordinate readout.  No TFVD
reconstruction, zero hypothesis, or identification with a Green flux is used.
-/

open scoped BigOperators Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-- Active native tags covering one complete finite multiplicative camera
prefix.  The function is total on naturals, but its laws are required only on
`k < cutoff`, exactly the indices used by the finite sum. -/
structure C2GpreActiveCameraPrefixAtlas
    (S : Finset NativeGpreBoundaryContext) (base cutoff : ℕ) where
  vertex : ℕ → ↥S
  vertex_cell : ∀ k, k < cutoff →
    (vertex k).1.cell = base * (k + 1)
  vertex_active : ∀ k, k < cutoff →
    c2GpreProvenanceValueCoefficient (vertex k).1 ≠ 0

/-- The camera-prefix synthesis formed literally from normalized native
provenance readouts. -/
def c2GpreNormalizedCameraPrefixTaggedSynthesis
    (verticalRatio : ℝ) (S : Finset NativeGpreBoundaryContext)
    (base cutoff : ℕ)
    (atlas : C2GpreActiveCameraPrefixAtlas S base cutoff)
    (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.range cutoff,
    c2GpreCameraAtomWeight base (k + 1) *
      c2GpreNormalizedProvenanceValueReadout S (atlas.vertex k)
        (c2GpreNormalizedLogAtomAnalysis
          verticalRatio S (base * (k + 1)) s)

/-- Reading every active tag recovers the scalar atom synthesis term by term. -/
theorem c2GpreNormalizedCameraPrefixTaggedSynthesis_eq_atomSynthesis
    (verticalRatio : ℝ) (S : Finset NativeGpreBoundaryContext)
    (base cutoff : ℕ) (hbase : Nat.Prime base)
    (atlas : C2GpreActiveCameraPrefixAtlas S base cutoff)
    (s : ℂ) :
    c2GpreNormalizedCameraPrefixTaggedSynthesis
        verticalRatio S base cutoff atlas s =
      c2GpreNormalizedCameraPrefixSynthesis base cutoff s := by
  unfold c2GpreNormalizedCameraPrefixTaggedSynthesis
    c2GpreNormalizedCameraPrefixSynthesis
    c2GpreWeightedCameraAtom
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < cutoff := Finset.mem_range.mp hk
  rw [c2GpreNormalizedProvenanceValueReadout_logAtom
    verticalRatio S (atlas.vertex k)
    (n := base * (k + 1))
    (Nat.mul_ne_zero hbase.ne_zero (by omega))
    (atlas.vertex_cell k hklt)
    (atlas.vertex_active k hklt) s]

/-- A genuinely cofinal family: both the finite atlas and the active tags may
grow with `L`, while the two camera prefixes retain their aligned cutoffs. -/
structure C2GpreActiveCofinalAtlasFamily (p q : ℕ) where
  support : ℕ → Finset NativeGpreBoundaryContext
  pPrefix : ∀ L,
    C2GpreActiveCameraPrefixAtlas
      (support L) p (crossPrimeAlignedCutoff q L)
  qPrefix : ∀ L,
    C2GpreActiveCameraPrefixAtlas
      (support L) q (crossPrimeAlignedCutoff p L)

/-- Difference of the two tagged native-provenance prefix syntheses.  This
object is built from `G_pre` coordinate readouts and does not mention the
camera-gap formula. -/
def c2GpreNormalizedCofinalTaggedSynthesis
    (verticalRatio : ℝ) {p q : ℕ}
    (family : C2GpreActiveCofinalAtlasFamily p q)
    (L : ℕ) (s : ℂ) : ℂ :=
  c2GpreNormalizedCameraPrefixTaggedSynthesis
      verticalRatio (family.support L) p
      (crossPrimeAlignedCutoff q L) (family.pPrefix L) s -
    c2GpreNormalizedCameraPrefixTaggedSynthesis
      verticalRatio (family.support L) q
      (crossPrimeAlignedCutoff p L) (family.qPrefix L) s

/-- The tagged carrier realization is exactly the scalar atom synthesis. -/
theorem c2GpreNormalizedCofinalTaggedSynthesis_eq_atomSynthesis
    (verticalRatio : ℝ) {p q : ℕ}
    (family : C2GpreActiveCofinalAtlasFamily p q)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (L : ℕ) (s : ℂ) :
    c2GpreNormalizedCofinalTaggedSynthesis
        verticalRatio family L s =
      c2GpreNormalizedCofinalSynthesis p q L s := by
  unfold c2GpreNormalizedCofinalTaggedSynthesis
    c2GpreNormalizedCofinalSynthesis
  rw [c2GpreNormalizedCameraPrefixTaggedSynthesis_eq_atomSynthesis
      verticalRatio (family.support L) p
      (crossPrimeAlignedCutoff q L) hp (family.pPrefix L) s,
    c2GpreNormalizedCameraPrefixTaggedSynthesis_eq_atomSynthesis
      verticalRatio (family.support L) q
      (crossPrimeAlignedCutoff p L) hq (family.qPrefix L) s]

/-- Exact finite reindexing of the tagged native-provenance synthesis into the
aligned two-camera prefix gap. -/
theorem c2GpreNormalizedCofinalTaggedSynthesis_eq_cameraGap
    (verticalRatio : ℝ) {p q : ℕ}
    (family : C2GpreActiveCofinalAtlasFamily p q)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (L : ℕ) (s : ℂ) :
    c2GpreNormalizedCofinalTaggedSynthesis
        verticalRatio family L s =
      c2CrossPrimeCofinalCameraGap p q L s := by
  rw [c2GpreNormalizedCofinalTaggedSynthesis_eq_atomSynthesis
      verticalRatio family hp hq L s,
    c2GpreNormalizedCofinalSynthesis_eq_cameraGap p q L hp hq s]

/-- The tagged synthesis error is identically zero. -/
theorem c2GpreNormalizedCofinalTaggedSynthesis_error_tendsto_zero
    (verticalRatio : ℝ) {p q : ℕ}
    (family : C2GpreActiveCofinalAtlasFamily p q)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (s : ℂ) :
    Tendsto
      (fun L : ℕ =>
        ‖c2GpreNormalizedCofinalTaggedSynthesis
            verticalRatio family L s -
          c2CrossPrimeCofinalCameraGap p q L s‖)
      atTop (nhds 0) := by
  have heq :
      (fun L : ℕ =>
        ‖c2GpreNormalizedCofinalTaggedSynthesis
            verticalRatio family L s -
          c2CrossPrimeCofinalCameraGap p q L s‖) =
        (fun _ : ℕ => (0 : ℝ)) := by
    funext L
    rw [c2GpreNormalizedCofinalTaggedSynthesis_eq_cameraGap
      verticalRatio family hp hq L s]
    simp
  rw [heq]
  exact tendsto_const_nhds

/-- Concrete tagged-carrier instance of the horizontal cofinal intertwiner. -/
theorem c2GpreNormalizedCofinalTaggedSynthesis_intertwinesCameraGap
    (verticalRatio : ℝ) {p q : ℕ}
    (family : C2GpreActiveCofinalAtlasFamily p q)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (s : ℂ) :
    C2GpreNormalizedCofinalIntertwinesCameraGap
      (fun L : ℕ =>
        c2GpreNormalizedCofinalTaggedSynthesis
          verticalRatio family L s) p q s := by
  exact Eventually.of_forall fun L =>
    c2GpreNormalizedCofinalTaggedSynthesis_eq_cameraGap
      verticalRatio family hp hq L s

/-- At a Genuine zero, the actual tagged `G_pre` synthesis tends to zero by
its exact identification with the global horizontal camera gap. -/
theorem c2GpreNormalizedCofinalTaggedSynthesis_tendsto_zero_of_genuine_zero
    (verticalRatio : ℝ) {p q : ℕ}
    (family : C2GpreActiveCofinalAtlasFamily p q)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
      (fun L : ℕ =>
        c2GpreNormalizedCofinalTaggedSynthesis
          verticalRatio family L s)
      atTop (nhds 0) := by
  exact normalizedC2GpreProvenanceGap_tendsto_zero_of_genuine_zero
    (fun L : ℕ =>
      c2GpreNormalizedCofinalTaggedSynthesis
        verticalRatio family L s)
    p q hp hpodd hq hqodd hs hzero
    (c2GpreNormalizedCofinalTaggedSynthesis_intertwinesCameraGap
      verticalRatio family hp hq s)

end

end CPFormal.Analytic.Cp
