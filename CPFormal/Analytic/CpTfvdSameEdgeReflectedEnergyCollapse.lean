import CPFormal.Analytic.CpNativeGpreTfvdCommutatorTowerSource
import CPFormal.Analytic.CpTfvdGpreCollapseInterface

/-!
# Same-edge recovery and the reflected-energy TFVD--G_pre collapse

The ordinary Dirichlet gradient and its logarithmic jet are not merely two
parallel readouts.  On every positive edge they form an invertible two-by-two
system whose determinant is

`log(n + 2) - log(n + 1)`.

Consequently the two endpoint values can be recovered before any prime-camera
readout.  The reflected endpoint is then reconstructed from the exact identity

`conj(value_s(n)) * value_(1-conj(s))(n) = (n + 1)^(-1)`.

This produces, from the two same-edge TFVD states alone, the reflected Green
energy stored at the first material level.  The resulting tower state is
independent of the prime observable and realizes every prime Green bulk against
the already-certified reflected first-level profile gap.

The module deliberately stops before replacing that spectral profile family by
the fixed native profiles at arithmetic time `tau = 1`.  The last theorem
identifies that replacement as exactly the remaining firewall in
`IsSeededTfvdGpreMomentCollapseAt`.

No Genuine zero, critical displacement, target-chosen source, `axiom`, `sorry`
or `admit` is used.
-/

open scoped BigOperators ENNReal InnerProduct lp

namespace CPFormal.Analytic.Cp

noncomputable section

/-! ## Exact inversion of one ordinary/log-jet edge -/

/-- Logarithmic determinant of the two endpoint equations on edge `n`. -/
def sameEdgeLogIncrement (n : ℕ) : ℝ :=
  Real.log (((n + 2 : ℕ) : ℝ)) -
    Real.log (((n + 1 : ℕ) : ℝ))

/-- Consecutive positive integers have distinct logarithms. -/
theorem sameEdgeLogIncrement_ne_zero (n : ℕ) :
    sameEdgeLogIncrement n ≠ 0 := by
  intro hzero
  unfold sameEdgeLogIncrement at hzero
  have hlog :
      Real.log (((n + 2 : ℕ) : ℝ)) =
        Real.log (((n + 1 : ℕ) : ℝ)) :=
    sub_eq_zero.mp hzero
  have hexp := congrArg Real.exp hlog
  have hn2 : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
  have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [Real.exp_log hn2, Real.exp_log hn1] at hexp
  have hnat : n + 2 = n + 1 := by
    exact_mod_cast hexp
  omega

/-- Complex form of the preceding nondegeneracy. -/
theorem sameEdgeLogIncrement_complex_ne_zero (n : ℕ) :
    ((sameEdgeLogIncrement n : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast sameEdgeLogIncrement_ne_zero n

/-- Recover the left endpoint from the ordinary difference and log-jet. -/
def sameEdgeRecoverLeft
    (n : ℕ) (ordinary logJet : ℂ) : ℂ :=
  (logJet -
      (Real.log (((n + 2 : ℕ) : ℝ)) : ℂ) * ordinary) /
    (sameEdgeLogIncrement n : ℂ)

/-- Recover the right endpoint from the same two edge coordinates. -/
def sameEdgeRecoverRight
    (n : ℕ) (ordinary logJet : ℂ) : ℂ :=
  (logJet -
      (Real.log (((n + 1 : ℕ) : ℝ)) : ℂ) * ordinary) /
    (sameEdgeLogIncrement n : ℂ)

/-- Algebraic left-endpoint inversion for arbitrary complex endpoint values. -/
theorem sameEdgeRecoverLeft_of_values
    (n : ℕ) (left right : ℂ) :
    sameEdgeRecoverLeft n
        (right - left)
        ((Real.log (((n + 2 : ℕ) : ℝ)) : ℂ) * right -
          (Real.log (((n + 1 : ℕ) : ℝ)) : ℂ) * left) =
      left := by
  unfold sameEdgeRecoverLeft
  rw [div_eq_iff (sameEdgeLogIncrement_complex_ne_zero n)]
  unfold sameEdgeLogIncrement
  push_cast
  ring

/-- Algebraic right-endpoint inversion for arbitrary complex endpoint values. -/
theorem sameEdgeRecoverRight_of_values
    (n : ℕ) (left right : ℂ) :
    sameEdgeRecoverRight n
        (right - left)
        ((Real.log (((n + 2 : ℕ) : ℝ)) : ℂ) * right -
          (Real.log (((n + 1 : ℕ) : ℝ)) : ℂ) * left) =
      right := by
  unfold sameEdgeRecoverRight
  rw [div_eq_iff (sameEdgeLogIncrement_complex_ne_zero n)]
  unfold sameEdgeLogIncrement
  push_cast
  ring

/-- The canonical log-jet is exactly the weighted endpoint difference used by
`sameEdgeRecoverLeft` and `sameEdgeRecoverRight`. -/
theorem positiveLogDirichletGradient_eq_weighted_value_sub_value
    (s : ℂ) (n : ℕ) :
    positiveLogDirichletGradient s n =
      (Real.log (((n + 2 : ℕ) : ℝ)) : ℂ) *
          positiveDirichletValue s (n + 1) -
        (Real.log (((n + 1 : ℕ) : ℝ)) : ℂ) *
          positiveDirichletValue s n := by
  simp [positiveLogDirichletGradient, positiveLogDirichletValue,
    Nat.add_assoc]

/-- The ordinary/log-jet pair recovers the left Dirichlet vertex exactly. -/
theorem sameEdgeRecoverLeft_canonical
    (s : ℂ) (n : ℕ) :
    sameEdgeRecoverLeft n
        (positiveDirichletGradient s n)
        (positiveLogDirichletGradient s n) =
      positiveDirichletValue s n := by
  rw [positiveDirichletGradient_eq_value_sub_value,
    positiveLogDirichletGradient_eq_weighted_value_sub_value]
  exact sameEdgeRecoverLeft_of_values n
    (positiveDirichletValue s n)
    (positiveDirichletValue s (n + 1))

/-- The same pair recovers the right Dirichlet vertex exactly. -/
theorem sameEdgeRecoverRight_canonical
    (s : ℂ) (n : ℕ) :
    sameEdgeRecoverRight n
        (positiveDirichletGradient s n)
        (positiveLogDirichletGradient s n) =
      positiveDirichletValue s (n + 1) := by
  rw [positiveDirichletGradient_eq_value_sub_value,
    positiveLogDirichletGradient_eq_weighted_value_sub_value]
  exact sameEdgeRecoverRight_of_values n
    (positiveDirichletValue s n)
    (positiveDirichletValue s (n + 1))

/-! ## Reflected endpoint and reflected edge recovery -/

/-- Every positive Dirichlet vertex is nonzero. -/
theorem positiveDirichletValue_ne_zero (s : ℂ) (n : ℕ) :
    positiveDirichletValue s n ≠ 0 := by
  unfold positiveDirichletValue
  apply (Complex.cpow_ne_zero_iff).2
  left
  exact_mod_cast Nat.succ_ne_zero n

/-- Recover the reflected endpoint from one ordinary endpoint. -/
def sameEdgeReflectedVertex (n : ℕ) (value : ℂ) : ℂ :=
  (((n + 1 : ℕ) : ℂ))⁻¹ *
    ((starRingEnd ℂ) value)⁻¹

/-- On canonical data, endpoint recovery agrees with the spectral reflection
`s ↦ 1 - conj(s)`. -/
theorem sameEdgeReflectedVertex_canonical
    (s : ℂ) (n : ℕ) :
    sameEdgeReflectedVertex n (positiveDirichletValue s n) =
      positiveDirichletValue (reflectedParameter s) n := by
  have hprod := finiteReflectedOuterEndpoint_eq_inv n s
  have hconj :
      (starRingEnd ℂ) (positiveDirichletValue s n) ≠ 0 := by
    intro hzero
    apply positiveDirichletValue_ne_zero s n
    have h := congrArg (starRingEnd ℂ) hzero
    simpa using h
  unfold sameEdgeReflectedVertex
  unfold finiteReflectedOuterEndpoint at hprod
  rw [← hprod]
  calc
    ((starRingEnd ℂ) (positiveDirichletValue s n) *
          positiveDirichletValue (reflectedParameter s) n) *
        ((starRingEnd ℂ) (positiveDirichletValue s n))⁻¹ =
      positiveDirichletValue (reflectedParameter s) n *
        ((starRingEnd ℂ) (positiveDirichletValue s n) *
          ((starRingEnd ℂ) (positiveDirichletValue s n))⁻¹) := by
        ring
    _ = positiveDirichletValue (reflectedParameter s) n := by
      simp [hconj]

/-- Reconstruct the reflected gradient from the recovered left and right
ordinary endpoints. -/
def sameEdgeRecoveredReflectedGradient
    (n : ℕ) (ordinary logJet : ℂ) : ℂ :=
  sameEdgeReflectedVertex (n + 1)
      (sameEdgeRecoverRight n ordinary logJet) -
    sameEdgeReflectedVertex n
      (sameEdgeRecoverLeft n ordinary logJet)

/-- Canonical ordinary/log-jet coordinates reconstruct the reflected gradient
exactly. -/
theorem sameEdgeRecoveredReflectedGradient_canonical
    (s : ℂ) (n : ℕ) :
    sameEdgeRecoveredReflectedGradient n
        (positiveDirichletGradient s n)
        (positiveLogDirichletGradient s n) =
      positiveDirichletGradient (reflectedParameter s) n := by
  unfold sameEdgeRecoveredReflectedGradient
  rw [sameEdgeRecoverRight_canonical,
    sameEdgeRecoverLeft_canonical,
    sameEdgeReflectedVertex_canonical,
    sameEdgeReflectedVertex_canonical,
    positiveDirichletGradient_eq_value_sub_value]

/-- Real reflected-energy contribution recovered from one same-edge pair. -/
def sameEdgeRecoveredReflectedEnergyEdge
    (n : ℕ) (ordinary logJet : ℂ) : ℝ :=
  ((starRingEnd ℂ) ordinary *
    sameEdgeRecoveredReflectedGradient n ordinary logJet).re

/-- On canonical data this is the existing reflected Green edge energy. -/
theorem sameEdgeRecoveredReflectedEnergyEdge_canonical
    (s : ℂ) (n : ℕ) :
    sameEdgeRecoveredReflectedEnergyEdge n
        (positiveDirichletGradient s n)
        (positiveLogDirichletGradient s n) =
      (finiteReflectedGradientEdge n s).re := by
  unfold sameEdgeRecoveredReflectedEnergyEdge finiteReflectedGradientEdge
  rw [sameEdgeRecoveredReflectedGradient_canonical]

/-! ## One prime-independent first-level source from the two TFVD states -/

/-- Finite reflected energy read directly from the two provenance edge cores of
same-edge TFVD product states. -/
def nativeGpreTfvdSameEdgeRecoveredReflectedEnergyAt
    (N : ℕ)
    (ordinary logJet : NativeGpreTfvdProductState) : ℝ :=
  ∑ n ∈ Finset.range N,
    sameEdgeRecoveredReflectedEnergyEdge n
      (ordinary.2 n) (logJet.2 n)

/-- A fixed-cutoff collapse into the common native tower.  The cutoff is chosen
before the inputs; the output contains no prime label. -/
noncomputable def nativeGpreTfvdSameEdgeReflectedEnergyCollapseAt
    (N : ℕ) : NativeGpreTfvdCollapse :=
  fun ordinary logJet =>
    lp.single 2 1
      (nativeGpreTfvdSameEdgeRecoveredReflectedEnergyAt
        N ordinary logJet)

/-- On the canonical ordinary/log-jet prefixes, the recovered energy is exactly
the existing reflected Green pairing. -/
theorem nativeGpreTfvdSameEdgeRecoveredReflectedEnergyAt_canonical
    (N : ℕ) (s : ℂ) :
    nativeGpreTfvdSameEdgeRecoveredReflectedEnergyAt N
        (nativeGpreTfvdSameEdgeGlue nativeGpreCanonicalVerticalRealization
          (c2DirichletGradientPrefixCore s N))
        (nativeGpreTfvdSameEdgeGlue nativeGpreCanonicalVerticalRealization
          (c2LogJetPrefixCore s N)) =
      (finiteReflectedGradientPairing N s).re := by
  unfold nativeGpreTfvdSameEdgeRecoveredReflectedEnergyAt
  calc
    (∑ n ∈ Finset.range N,
      sameEdgeRecoveredReflectedEnergyEdge n
        ((nativeGpreTfvdSameEdgeGlue nativeGpreCanonicalVerticalRealization
          (c2DirichletGradientPrefixCore s N)).2 n)
        ((nativeGpreTfvdSameEdgeGlue nativeGpreCanonicalVerticalRealization
          (c2LogJetPrefixCore s N)).2 n)) =
      ∑ n ∈ Finset.range N, (finiteReflectedGradientEdge n s).re := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnlt : n < N := Finset.mem_range.mp hn
        simp only [nativeGpreTfvdSameEdgeGlue_apply]
        change
          sameEdgeRecoveredReflectedEnergyEdge n
              (c2DirichletGradientPrefixCore s N n)
              (c2LogJetPrefixCore s N n) =
            (finiteReflectedGradientEdge n s).re
        rw [c2DirichletGradientPrefixCore_apply,
          c2LogJetPrefixCore_apply, if_pos hnlt, if_pos hnlt]
        exact sameEdgeRecoveredReflectedEnergyEdge_canonical s n
    _ = (∑ n ∈ Finset.range N,
          finiteReflectedGradientEdge n s).re := by
      exact (complex_re_sum_range
        (fun n => finiteReflectedGradientEdge n s) N).symm
    _ = (finiteReflectedGradientPairing N s).re := by
      rfl

/-- The abstract collapsed source is the prime-independent reflected-energy
state already used by the universal prime-moment crosswalk. -/
theorem seededTfvdGpreCollapsedSource_sameEdgeReflectedEnergy
    (M : ℕ) (s : ℂ) :
    seededTfvdGpreCollapsedSource
        (nativeGpreTfvdSameEdgeReflectedEnergyCollapseAt (3 * M)) M s =
      nativeGpreGreenEnergyFirstLevelState (3 * M) s := by
  change
    lp.single 2 1
        (nativeGpreTfvdSameEdgeRecoveredReflectedEnergyAt (3 * M)
          (nativeGpreTfvdSameEdgeGlue nativeGpreCanonicalVerticalRealization
            (c2DirichletGradientPrefixCore s (3 * M)))
          (nativeGpreTfvdSameEdgeGlue nativeGpreCanonicalVerticalRealization
            (c2LogJetPrefixCore s (3 * M)))) =
      lp.single 2 1 (finiteReflectedGradientPairing (3 * M) s).re
  rw [nativeGpreTfvdSameEdgeRecoveredReflectedEnergyAt_canonical]

/-- Every prime Green bulk is a moment of this single same-edge state against
its reflected first-level profile gap. -/
theorem
    inner_nativeGpreReflectedFirstLevelGapProfile_seededSameEdgeCollapsedSource
    (M : ℕ) (s : ℂ) (p : Nat.Primes) :
    inner ℝ (nativeGpreReflectedFirstLevelGapProfile p s)
        (seededTfvdGpreCollapsedSource
          (nativeGpreTfvdSameEdgeReflectedEnergyCollapseAt (3 * M)) M s) =
      primeCarryGreenBulkCutoffProfile (3 * M) s p := by
  rw [seededTfvdGpreCollapsedSource_sameEdgeReflectedEnergy]
  exact inner_nativeGpreReflectedFirstLevelGapProfile_eq_greenBulk
    (3 * M) s p

/-! ## The exact remaining fixed-time firewall -/

/-- The remaining step after the explicit same-edge collapse: the fixed native
profile and the reflected spectral profile must read the same common source. -/
def SameEdgeReflectedEnergyTransportsToFixedTimeAt
    (M : ℕ) (s : ℂ) : Prop :=
  ∀ p : Nat.Primes,
    inner ℝ (nativeGpreTowerProfileVector (p : ℕ) 1)
        (seededTfvdGpreCollapsedSource
          (nativeGpreTfvdSameEdgeReflectedEnergyCollapseAt (3 * M)) M s) =
      inner ℝ (nativeGpreReflectedFirstLevelGapProfile p s)
        (seededTfvdGpreCollapsedSource
          (nativeGpreTfvdSameEdgeReflectedEnergyCollapseAt (3 * M)) M s)

/-- For the explicit same-edge collapse, the abstract fixed-time moment gate is
exactly the reflected-to-fixed profile transport and nothing else. -/
theorem isSeededTfvdGpreMomentCollapseAt_sameEdgeReflectedEnergy_iff
    (M : ℕ) (s : ℂ) :
    IsSeededTfvdGpreMomentCollapseAt
        (nativeGpreTfvdSameEdgeReflectedEnergyCollapseAt (3 * M)) M s ↔
      SameEdgeReflectedEnergyTransportsToFixedTimeAt M s := by
  constructor
  · intro hcollapse p
    rw [hcollapse p,
      finiteEnrichedNativeGpreLogJetGreenBulkReadout_eq
        p M (by norm_num) (fun _ => 1) (by intro m; norm_num) s,
      inner_nativeGpreReflectedFirstLevelGapProfile_seededSameEdgeCollapsedSource]
  · intro htransport p
    rw [htransport p,
      inner_nativeGpreReflectedFirstLevelGapProfile_seededSameEdgeCollapsedSource,
      finiteEnrichedNativeGpreLogJetGreenBulkReadout_eq
        p M (by norm_num) (fun _ => 1) (by intro m; norm_num) s]

end

end CPFormal.Analytic.Cp
