import CPFormal.Analytic.CpC2DirichletJetTfvd
import CPFormal.Analytic.CpNativeGpreTfvdAnalysis
import CPFormal.Analytic.CpGenuineFirstMultibaseCutoff

/-!
# Cofinally normalized C2 Dirichlet one-jet in `G_pre` provenance

The local C2 Dirichlet one-jet is already an exact TFVD readout.  This module
places the same four spectral legs in the enriched TFVD--`G_pre` carrier and
recovers them from the native provenance coordinates themselves, rather than
through the TFVD reconstruction map.

An active provenance coordinate carries an edge value multiplied by its native
`G_pre` coefficient.  Dividing by that coefficient is therefore the canonical
coordinate readout on the active locus.  Four tagged coordinates recover the
ordinary and logarithmic lower/upper legs, and the two-cell Leibniz wedge is
exactly the previously validated local spectral gap.

The concrete Richardson numerator is then divided by its own connected C2
mass scale.  The kernel proves that this removes the geometric `1/4` loss
exactly: the normalized local readout is the fixed monomial
`log(p*q) * (p*q)^(-s)`.  Consequently, scale normalization alone cannot make a
single semiprime cell close at a Genuine zero.  A zero-dependent limit requires
one further, genuinely global theorem identifying a cofinal synthesis of such
provenance cells with the existing cross-prime weighted camera-prefix gap.

The final section names precisely that remaining intertwiner and proves that,
once it is supplied, the existing Genuine-zero theorem forces the normalized
provenance gap to tend to zero.  No instance of the global intertwiner is
postulated here.
-/

open scoped Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-! ## Active native provenance readout -/

/-- Native value-role coefficient carried by one tagged provenance coordinate. -/
def c2GpreProvenanceValueCoefficient
    (c : NativeGpreBoundaryContext) : ℂ :=
  (nativeGpreTowerCoordinateCoefficient (c.withRole .value) : ℂ)

/-- Two spectral vertices retained as a finitely supported native edge state. -/
def c2GprePairCore
    (leftCell rightCell : ℕ) (leftValue rightValue : ℂ) :
    NativeGpreComplexEdgeCore :=
  Finsupp.single leftCell leftValue +
    Finsupp.single rightCell rightValue

@[simp] theorem c2GprePairCore_apply_left
    {leftCell rightCell : ℕ} (hneq : leftCell ≠ rightCell)
    (leftValue rightValue : ℂ) :
    c2GprePairCore leftCell rightCell leftValue rightValue leftCell =
      leftValue := by
  classical
  simp [c2GprePairCore, hneq]

@[simp] theorem c2GprePairCore_apply_right
    {leftCell rightCell : ℕ} (hneq : leftCell ≠ rightCell)
    (leftValue rightValue : ℂ) :
    c2GprePairCore leftCell rightCell leftValue rightValue rightCell =
      rightValue := by
  classical
  simp [c2GprePairCore, Ne.symm hneq]

/-- The same two-point edge state after the enriched TFVD--`G_pre` analysis. -/
def c2GprePairEnrichedAnalysis
    (verticalRatio : ℝ) (S : Finset NativeGpreBoundaryContext)
    (leftCell rightCell : ℕ) (leftValue rightValue : ℂ) :
    NativeGpreFiniteTfvdAnalysisCarrier S :=
  nativeGpreFiniteTfvdAnalysis verticalRatio S
    (nativeGpreCanonicalVerticalRealization
      (c2GprePairCore leftCell rightCell leftValue rightValue))

/-- Canonical readout of an active value-role provenance coordinate.  It uses
only the `G_pre` value leg `data.2.1`; no TFVD reconstruction is consulted. -/
def c2GpreNormalizedProvenanceValueReadout
    (S : Finset NativeGpreBoundaryContext) (c : ↥S)
    (data : NativeGpreFiniteTfvdAnalysisCarrier S) : ℂ :=
  data.2.1 c * (c2GpreProvenanceValueCoefficient c.1)⁻¹

/-- An active tagged coordinate on the left vertex recovers the left value. -/
theorem c2GpreNormalizedProvenanceValueReadout_pair_left
    (verticalRatio : ℝ) (S : Finset NativeGpreBoundaryContext) (c : ↥S)
    (leftCell rightCell : ℕ) (leftValue rightValue : ℂ)
    (hneq : leftCell ≠ rightCell)
    (hcell : c.1.cell = leftCell)
    (hactive : c2GpreProvenanceValueCoefficient c.1 ≠ 0) :
    c2GpreNormalizedProvenanceValueReadout S c
        (c2GprePairEnrichedAnalysis verticalRatio S
          leftCell rightCell leftValue rightValue) =
      leftValue := by
  unfold c2GpreNormalizedProvenanceValueReadout
    c2GprePairEnrichedAnalysis
  rw [nativeGpreFiniteTfvdAnalysis_apply]
  change
    (c2GprePairCore leftCell rightCell leftValue rightValue c.1.cell *
        (nativeGpreTowerCoordinateCoefficient
          (c.1.withRole .value) : ℂ)) *
      (c2GpreProvenanceValueCoefficient c.1)⁻¹ = leftValue
  rw [hcell, c2GprePairCore_apply_left hneq]
  unfold c2GpreProvenanceValueCoefficient at hactive ⊢
  field_simp [hactive]

/-- An active tagged coordinate on the right vertex recovers the right value. -/
theorem c2GpreNormalizedProvenanceValueReadout_pair_right
    (verticalRatio : ℝ) (S : Finset NativeGpreBoundaryContext) (c : ↥S)
    (leftCell rightCell : ℕ) (leftValue rightValue : ℂ)
    (hneq : leftCell ≠ rightCell)
    (hcell : c.1.cell = rightCell)
    (hactive : c2GpreProvenanceValueCoefficient c.1 ≠ 0) :
    c2GpreNormalizedProvenanceValueReadout S c
        (c2GprePairEnrichedAnalysis verticalRatio S
          leftCell rightCell leftValue rightValue) =
      rightValue := by
  unfold c2GpreNormalizedProvenanceValueReadout
    c2GprePairEnrichedAnalysis
  rw [nativeGpreFiniteTfvdAnalysis_apply]
  change
    (c2GprePairCore leftCell rightCell leftValue rightValue c.1.cell *
        (nativeGpreTowerCoordinateCoefficient
          (c.1.withRole .value) : ℂ)) *
      (c2GpreProvenanceValueCoefficient c.1)⁻¹ = rightValue
  rw [hcell, c2GprePairCore_apply_right hneq]
  unfold c2GpreProvenanceValueCoefficient at hactive ⊢
  field_simp [hactive]

/-- Pair-valued provenance readout before the local wedge is formed. -/
def c2GpreNormalizedProvenancePairReadout
    (S : Finset NativeGpreBoundaryContext)
    (leftContext rightContext : ↥S)
    (data : NativeGpreFiniteTfvdAnalysisCarrier S) : ℂ × ℂ :=
  (c2GpreNormalizedProvenanceValueReadout S leftContext data,
    c2GpreNormalizedProvenanceValueReadout S rightContext data)

/-- The pair of active tags reconstructs both vertices from the provenance leg. -/
theorem c2GpreNormalizedProvenancePairReadout_analysis
    (verticalRatio : ℝ) (S : Finset NativeGpreBoundaryContext)
    (leftContext rightContext : ↥S)
    (leftCell rightCell : ℕ) (leftValue rightValue : ℂ)
    (hneq : leftCell ≠ rightCell)
    (hleftCell : leftContext.1.cell = leftCell)
    (hrightCell : rightContext.1.cell = rightCell)
    (hleftActive : c2GpreProvenanceValueCoefficient leftContext.1 ≠ 0)
    (hrightActive : c2GpreProvenanceValueCoefficient rightContext.1 ≠ 0) :
    c2GpreNormalizedProvenancePairReadout S leftContext rightContext
        (c2GprePairEnrichedAnalysis verticalRatio S
          leftCell rightCell leftValue rightValue) =
      (leftValue, rightValue) := by
  apply Prod.ext
  · exact c2GpreNormalizedProvenanceValueReadout_pair_left
      verticalRatio S leftContext leftCell rightCell leftValue rightValue
      hneq hleftCell hleftActive
  · exact c2GpreNormalizedProvenanceValueReadout_pair_right
      verticalRatio S rightContext leftCell rightCell leftValue rightValue
      hneq hrightCell hrightActive

/-! ## Four native tags for the multiplicative square -/

/-- A finite enriched atlas containing active native tags for the four vertices
`p`, `p*q`, `1`, and `q`.  All other provenance fields remain literal in the
chosen contexts. -/
structure C2GpreActiveSpectralAtlas
    (S : Finset NativeGpreBoundaryContext) (p q : ℕ) where
  pVertex : ↥S
  pqVertex : ↥S
  oneVertex : ↥S
  qVertex : ↥S
  p_cell : pVertex.1.cell = p
  pq_cell : pqVertex.1.cell = p * q
  one_cell : oneVertex.1.cell = 1
  q_cell : qVertex.1.cell = q
  p_active : c2GpreProvenanceValueCoefficient pVertex.1 ≠ 0
  pq_active : c2GpreProvenanceValueCoefficient pqVertex.1 ≠ 0
  one_active : c2GpreProvenanceValueCoefficient oneVertex.1 ≠ 0
  q_active : c2GpreProvenanceValueCoefficient qVertex.1 ≠ 0

/-- Ordinary lower edge `(p,p*q)` in the enriched analysis. -/
def c2OddCoreDirichletGpreLowerAnalysis
    (verticalRatio : ℝ) (S : Finset NativeGpreBoundaryContext)
    (cutoff p q : ℕ) (s : ℂ) :
    NativeGpreFiniteTfvdAnalysisCarrier S :=
  c2GprePairEnrichedAnalysis verticalRatio S p (p * q)
    (c2OddCoreDirichletMassValue cutoff s p)
    (c2OddCoreDirichletMassValue cutoff s (p * q))

/-- Ordinary upper edge `(1,q)` in the enriched analysis. -/
def c2OddCoreDirichletGpreUpperAnalysis
    (verticalRatio : ℝ) (S : Finset NativeGpreBoundaryContext)
    (cutoff q : ℕ) (s : ℂ) :
    NativeGpreFiniteTfvdAnalysisCarrier S :=
  c2GprePairEnrichedAnalysis verticalRatio S 1 q
    (c2OddCoreDirichletMassValue cutoff s 1)
    (c2OddCoreDirichletMassValue cutoff s q)

/-- Logarithmic lower edge `(p,p*q)` in the enriched analysis. -/
def c2OddCoreLogDirichletGpreLowerAnalysis
    (verticalRatio : ℝ) (S : Finset NativeGpreBoundaryContext)
    (cutoff p q : ℕ) (s : ℂ) :
    NativeGpreFiniteTfvdAnalysisCarrier S :=
  c2GprePairEnrichedAnalysis verticalRatio S p (p * q)
    (c2OddCoreLogDirichletMassValue cutoff s p)
    (c2OddCoreLogDirichletMassValue cutoff s (p * q))

/-- Logarithmic upper edge `(1,q)` in the enriched analysis. -/
def c2OddCoreLogDirichletGpreUpperAnalysis
    (verticalRatio : ℝ) (S : Finset NativeGpreBoundaryContext)
    (cutoff q : ℕ) (s : ℂ) :
    NativeGpreFiniteTfvdAnalysisCarrier S :=
  c2GprePairEnrichedAnalysis verticalRatio S 1 q
    (c2OddCoreLogDirichletMassValue cutoff s 1)
    (c2OddCoreLogDirichletMassValue cutoff s q)

/-- Leibniz readout formed only after the four ordinary/logarithmic legs have
been recovered from active native `G_pre` provenance coordinates. -/
def c2OddCoreDirichletLogGpreReadout
    (verticalRatio : ℝ) (S : Finset NativeGpreBoundaryContext)
    {p q : ℕ} (atlas : C2GpreActiveSpectralAtlas S p q)
    (cutoff : ℕ) (s : ℂ) : ℂ :=
  let lowerD := c2GpreNormalizedProvenancePairReadout S
    atlas.pVertex atlas.pqVertex
      (c2OddCoreDirichletGpreLowerAnalysis
        verticalRatio S cutoff p q s)
  let upperD := c2GpreNormalizedProvenancePairReadout S
    atlas.oneVertex atlas.qVertex
      (c2OddCoreDirichletGpreUpperAnalysis
        verticalRatio S cutoff q s)
  let lowerL := c2GpreNormalizedProvenancePairReadout S
    atlas.pVertex atlas.pqVertex
      (c2OddCoreLogDirichletGpreLowerAnalysis
        verticalRatio S cutoff p q s)
  let upperL := c2GpreNormalizedProvenancePairReadout S
    atlas.oneVertex atlas.qVertex
      (c2OddCoreLogDirichletGpreUpperAnalysis
        verticalRatio S cutoff q s)
  sameSEdgeBoundaryWedge lowerL.1 lowerL.2 upperD.1 upperD.2 +
    sameSEdgeBoundaryWedge lowerD.1 lowerD.2 upperL.1 upperL.2

/-- The enriched provenance readout is exactly the local joint-minus-factorized
Dirichlet/log-Dirichlet spectral gap. -/
theorem c2OddCoreDirichletLogGpreReadout_eq_spectralGap
    (verticalRatio : ℝ) (S : Finset NativeGpreBoundaryContext)
    {p q : ℕ} (atlas : C2GpreActiveSpectralAtlas S p q)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (cutoff : ℕ) (s : ℂ) :
    c2OddCoreDirichletLogGpreReadout
        verticalRatio S atlas cutoff s =
      c2OddCoreDirichletLogSpectralGap cutoff p q s := by
  have hpqnep : p * q ≠ p := by
    intro heq
    have heq' : p * q = p * 1 := by simpa using heq
    exact hq.ne_one (Nat.eq_of_mul_eq_mul_left hp.pos heq')
  have hpnepq : p ≠ p * q := Ne.symm hpqnep
  have honeneq : 1 ≠ q := Ne.symm hq.ne_one
  have hLowerD := c2GpreNormalizedProvenancePairReadout_analysis
    verticalRatio S atlas.pVertex atlas.pqVertex p (p * q)
      (c2OddCoreDirichletMassValue cutoff s p)
      (c2OddCoreDirichletMassValue cutoff s (p * q))
      hpnepq atlas.p_cell atlas.pq_cell atlas.p_active atlas.pq_active
  have hUpperD := c2GpreNormalizedProvenancePairReadout_analysis
    verticalRatio S atlas.oneVertex atlas.qVertex 1 q
      (c2OddCoreDirichletMassValue cutoff s 1)
      (c2OddCoreDirichletMassValue cutoff s q)
      honeneq atlas.one_cell atlas.q_cell atlas.one_active atlas.q_active
  have hLowerL := c2GpreNormalizedProvenancePairReadout_analysis
    verticalRatio S atlas.pVertex atlas.pqVertex p (p * q)
      (c2OddCoreLogDirichletMassValue cutoff s p)
      (c2OddCoreLogDirichletMassValue cutoff s (p * q))
      hpnepq atlas.p_cell atlas.pq_cell atlas.p_active atlas.pq_active
  have hUpperL := c2GpreNormalizedProvenancePairReadout_analysis
    verticalRatio S atlas.oneVertex atlas.qVertex 1 q
      (c2OddCoreLogDirichletMassValue cutoff s 1)
      (c2OddCoreLogDirichletMassValue cutoff s q)
      honeneq atlas.one_cell atlas.q_cell atlas.one_active atlas.q_active
  unfold c2OddCoreDirichletLogGpreReadout
    c2OddCoreDirichletGpreLowerAnalysis
    c2OddCoreDirichletGpreUpperAnalysis
    c2OddCoreLogDirichletGpreLowerAnalysis
    c2OddCoreLogDirichletGpreUpperAnalysis
  rw [hLowerD, hUpperD, hLowerL, hUpperL]
  unfold c2OddCoreDirichletLogSpectralGap
    c2OddCoreJointSpectralPath c2OddCoreFactorizedSpectralPath
    sameSEdgeBoundaryWedge
  ring

/-! ## Normalization by the cofinal connected mass -/

/-- The connected C2 support mass multiplying the `4M/8M` Richardson cell. -/
def c2OddCoreCofinalMassScale (M p q : ℕ) : ℂ :=
  (((1 / 2 : ℝ) *
    c2OddCoreFourScaleDefectReal M p *
      c2OddCoreFourScaleDefectReal M q : ℝ) : ℂ)

/-- Richardson after transport through active `G_pre` provenance retains the
same exact connected spectral cell. -/
theorem c2OddCoreDirichletLogGpreReadout_richardson_exact
    (verticalRatio : ℝ) (S : Finset NativeGpreBoundaryContext)
    {M p q : ℕ} (atlas : C2GpreActiveSpectralAtlas S p q)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    (hpM : p ≤ M) (hqM : q ≤ M) (hpqM : p * q ≤ M)
    (s : ℂ) :
    2 * c2OddCoreDirichletLogGpreReadout
          verticalRatio S atlas (8 * M) s -
        c2OddCoreDirichletLogGpreReadout
          verticalRatio S atlas (4 * M) s =
      c2OddCoreCofinalMassScale M p q *
        natLogDirichletTerm s (p * q) := by
  rw [c2OddCoreDirichletLogGpreReadout_eq_spectralGap
      verticalRatio S atlas hp hq (8 * M) s,
    c2OddCoreDirichletLogGpreReadout_eq_spectralGap
      verticalRatio S atlas hp hq (4 * M) s]
  simpa [c2OddCoreCofinalMassScale] using
    c2OddCoreDirichletLogSpectralGap_richardson_exact
      hp hpodd hq hqodd hpM hqM hpqM s

/-- Cofinally normalized local provenance readout. -/
def c2OddCoreNormalizedCofinalGpreReadout
    (verticalRatio : ℝ) (S : Finset NativeGpreBoundaryContext)
    {p q : ℕ} (atlas : C2GpreActiveSpectralAtlas S p q)
    (M : ℕ) (s : ℂ) : ℂ :=
  (2 * c2OddCoreDirichletLogGpreReadout
        verticalRatio S atlas (8 * M) s -
      c2OddCoreDirichletLogGpreReadout
        verticalRatio S atlas (4 * M) s) /
    c2OddCoreCofinalMassScale M p q

/-- Dividing by the connected support mass removes the geometric decay
exactly.  The normalized local cell is independent of the cutoff. -/
theorem c2OddCoreNormalizedCofinalGpreReadout_eq_natLogDirichletTerm
    (verticalRatio : ℝ) (S : Finset NativeGpreBoundaryContext)
    {M p q : ℕ} (atlas : C2GpreActiveSpectralAtlas S p q)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    (hpM : p ≤ M) (hqM : q ≤ M) (hpqM : p * q ≤ M)
    (hscale : c2OddCoreCofinalMassScale M p q ≠ 0)
    (s : ℂ) :
    c2OddCoreNormalizedCofinalGpreReadout
        verticalRatio S atlas M s =
      natLogDirichletTerm s (p * q) := by
  unfold c2OddCoreNormalizedCofinalGpreReadout
  rw [c2OddCoreDirichletLogGpreReadout_richardson_exact
    verticalRatio S atlas hp hpodd hq hqodd hpM hqM hpqM s]
  field_simp [hscale]

/-- Under eventual nondegeneracy of the connected support mass, the normalized
single-cell sequence converges to its fixed logarithmic Dirichlet frequency,
not to zero merely because the unnormalized area decays. -/
theorem c2OddCoreNormalizedCofinalGpreReadout_tendsto_natLogDirichletTerm
    (verticalRatio : ℝ) (S : Finset NativeGpreBoundaryContext)
    {p q : ℕ} (atlas : C2GpreActiveSpectralAtlas S p q)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    (s : ℂ)
    (hscale : ∀ᶠ M : ℕ in atTop,
      c2OddCoreCofinalMassScale M p q ≠ 0) :
    Tendsto
      (fun M : ℕ =>
        c2OddCoreNormalizedCofinalGpreReadout
          verticalRatio S atlas M s)
      atTop (nhds (natLogDirichletTerm s (p * q))) := by
  have hbound : ∀ᶠ M : ℕ in atTop, p * q ≤ M :=
    eventually_ge_atTop (p * q)
  have heq : ∀ᶠ M : ℕ in atTop,
      c2OddCoreNormalizedCofinalGpreReadout
          verticalRatio S atlas M s =
        natLogDirichletTerm s (p * q) := by
    filter_upwards [hbound, hscale] with M hpqM hscaleM
    have hp_le_pq : p ≤ p * q := by
      calc
        p = p * 1 := by simp
        _ ≤ p * q := Nat.mul_le_mul_left p hq.one_le
    have hq_le_pq : q ≤ p * q := by
      calc
        q = 1 * q := by simp
        _ ≤ p * q := Nat.mul_le_mul_right q hp.one_le
    exact c2OddCoreNormalizedCofinalGpreReadout_eq_natLogDirichletTerm
      verticalRatio S atlas hp hpodd hq hqodd
        (hp_le_pq.trans hpqM) (hq_le_pq.trans hpqM) hpqM hscaleM s
  exact tendsto_const_nhds.congr'
    (heq.mono fun _ h => h.symm)

/-! ## The genuinely global cofinal camera intertwiner -/

/-- Existing cross-prime weighted horizontal prefix gap.  Unlike one local
semiprime cell, this object contains a growing oscillatory family of
frequencies. -/
def c2CrossPrimeCofinalCameraGap
    (p q L : ℕ) (s : ℂ) : ℂ :=
  (p : ℂ) ^ (1 - s) *
      positiveDirichletPrefix s (crossPrimeAlignedCutoff q L) -
    (q : ℂ) ^ (1 - s) *
      positiveDirichletPrefix s (crossPrimeAlignedCutoff p L)

/-- A Genuine zero closes the already constructed global camera gap. -/
theorem c2CrossPrimeCofinalCameraGap_tendsto_zero_of_genuine_zero
    (p q : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto (fun L : ℕ => c2CrossPrimeCofinalCameraGap p q L s)
      atTop (nhds 0) := by
  simpa [c2CrossPrimeCofinalCameraGap] using
    weightedHorizontalPrefixes_cross_prime_aligned_tendsto_zero_of_genuine_zero
      p q hp hpodd hq hqodd hs hzero

/-- Exact remaining global obligation: a cofinal synthesis of normalized
`G_pre` provenance cells must eventually equal the cross-prime camera gap.
This is a relation, not an assumed theorem or a declared instance. -/
def C2GpreNormalizedCofinalIntertwinesCameraGap
    (normalizedProvenanceGap : ℕ → ℂ)
    (p q : ℕ) (s : ℂ) : Prop :=
  ∀ᶠ L : ℕ in atTop,
    normalizedProvenanceGap L =
      c2CrossPrimeCofinalCameraGap p q L s

/-- Once the genuine global cofinal intertwiner is constructed, a Genuine zero
forces the normalized provenance gap to close for the oscillatory camera
reason, not because of the decaying C2 support mass. -/
theorem normalizedC2GpreProvenanceGap_tendsto_zero_of_genuine_zero
    (normalizedProvenanceGap : ℕ → ℂ)
    (p q : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hintertwines :
      C2GpreNormalizedCofinalIntertwinesCameraGap
        normalizedProvenanceGap p q s) :
    Tendsto normalizedProvenanceGap atTop (nhds 0) := by
  have hcamera :=
    c2CrossPrimeCofinalCameraGap_tendsto_zero_of_genuine_zero
      p q hp hpodd hq hqodd hs hzero
  exact hcamera.congr'
    (hintertwines.mono fun _ h => h.symm)

end

end CPFormal.Analytic.Cp
