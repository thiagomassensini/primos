import CPFormal.Analytic.CpNativeCarryLogWaveBoundaryEquivalence

/-!
# Reflected log-boundary symmetry for the native carry wave

A first-order logarithmic channel with only one orientation has a definite
boundary form.  Consequently, every isotropic complex subspace is trivial; a
nonzero native wave cannot belong to a symmetric one-channel realization.

The existing Green reflection supplies the missing opposite orientation.  In
complex carry time,

`reflectedParameter (1/2 + z I) = 1/2 + conj(z) I`.

The doubled boundary carrier therefore has the indefinite form

`omega(y,x) = conj(y.direct) * x.direct - conj(y.reflected) * x.reflected`.

Its diagonal subspace is equal to its own `omega`-orthogonal, hence is the
maximal isotropic boundary condition expected from a self-adjoint doubled
first-order realization.  The characteristic flux of the direct/reflected
native wave is `(z, conj z)`; it belongs to the diagonal exactly when `Im z = 0`.

No Genuine or zeta value is inserted into the boundary form.  The final scalar
gate is reduced to proving that bracket closure places the reflected
characteristic flux in this fixed diagonal boundary condition.
-/

open scoped ComplexConjugate

namespace CPFormal.Analytic.Cp

noncomputable section

/-- The definite one-channel boundary form, after removing its irrelevant
nonzero imaginary orientation factor. -/
def nativeCarrySingleLogBoundaryForm (y x : ℂ) : ℂ :=
  (starRingEnd ℂ) y * x

/-- Isotropy for the one-channel logarithmic boundary form. -/
def NativeCarrySingleLogBoundaryIsotropic (D : Submodule ℂ ℂ) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, nativeCarrySingleLogBoundaryForm y x = 0

/-- A one-orientation first-order log boundary has no nontrivial isotropic
complex subspace.  This excludes the naive single-half-line self-adjoint
realization before any spectral claim is made. -/
theorem nativeCarrySingleLogBoundaryIsotropic_eq_bot
    {D : Submodule ℂ ℂ}
    (hD : NativeCarrySingleLogBoundaryIsotropic D) :
    D = ⊥ := by
  apply le_antisymm
  · intro x hx
    have hxx := hD x hx x hx
    unfold nativeCarrySingleLogBoundaryForm at hxx
    have hx0 : x = 0 := by
      rcases mul_eq_zero.mp hxx with hconj | hxzero
      · have hback := congrArg (starRingEnd ℂ) hconj
        simpa using hback
      · exact hxzero
    simpa [hx0]
  · exact bot_le

/-- Direct and reflected endpoint channels. -/
abbrev NativeCarryReflectedLogBoundary := ℂ × ℂ

/-- The oriented Green form of the doubled logarithmic boundary. -/
def nativeCarryReflectedLogBoundaryForm
    (y x : NativeCarryReflectedLogBoundary) : ℂ :=
  (starRingEnd ℂ) y.1 * x.1 - (starRingEnd ℂ) y.2 * x.2

theorem nativeCarryReflectedLogBoundaryForm_add_right
    (y x w : NativeCarryReflectedLogBoundary) :
    nativeCarryReflectedLogBoundaryForm y (x + w) =
      nativeCarryReflectedLogBoundaryForm y x +
        nativeCarryReflectedLogBoundaryForm y w := by
  unfold nativeCarryReflectedLogBoundaryForm
  simp only [Prod.fst_add, Prod.snd_add, mul_add]
  ring

theorem nativeCarryReflectedLogBoundaryForm_smul_right
    (c : ℂ) (y x : NativeCarryReflectedLogBoundary) :
    nativeCarryReflectedLogBoundaryForm y (c • x) =
      c * nativeCarryReflectedLogBoundaryForm y x := by
  unfold nativeCarryReflectedLogBoundaryForm
  simp only [Prod.smul_fst, Prod.smul_snd]
  ring

/-- Orthogonal complement for the oriented reflected Green form. -/
def nativeCarryReflectedLogBoundaryOrthogonal
    (D : Submodule ℂ NativeCarryReflectedLogBoundary) :
    Submodule ℂ NativeCarryReflectedLogBoundary where
  carrier := {x | ∀ y, y ∈ D → nativeCarryReflectedLogBoundaryForm y x = 0}
  zero_mem' := by
    intro y hy
    simp [nativeCarryReflectedLogBoundaryForm]
  add_mem' := by
    intro x w hx hw y hy
    rw [nativeCarryReflectedLogBoundaryForm_add_right,
      hx y hy, hw y hy, add_zero]
  smul_mem' := by
    intro c x hx y hy
    rw [nativeCarryReflectedLogBoundaryForm_smul_right,
      hx y hy, mul_zero]

/-- Equal direct/reflected boundary data. -/
def nativeCarryReflectedLogDiagonal :
    Submodule ℂ NativeCarryReflectedLogBoundary where
  carrier := {x | x.1 = x.2}
  zero_mem' := rfl
  add_mem' := by
    intro x y hx hy
    change x.1 + y.1 = x.2 + y.2
    rw [hx, hy]
  smul_mem' := by
    intro c x hx
    change c * x.1 = c * x.2
    rw [hx]

@[simp] theorem mem_nativeCarryReflectedLogDiagonal
    (x : NativeCarryReflectedLogBoundary) :
    x ∈ nativeCarryReflectedLogDiagonal ↔ x.1 = x.2 :=
  Iff.rfl

/-- The diagonal boundary condition is isotropic for the direct/reflected Green
form. -/
theorem nativeCarryReflectedLogDiagonal_le_orthogonal :
    nativeCarryReflectedLogDiagonal ≤
      nativeCarryReflectedLogBoundaryOrthogonal
        nativeCarryReflectedLogDiagonal := by
  intro x hx
  change ∀ y, y ∈ nativeCarryReflectedLogDiagonal →
    nativeCarryReflectedLogBoundaryForm y x = 0
  intro y hy
  rw [mem_nativeCarryReflectedLogDiagonal] at hx hy
  unfold nativeCarryReflectedLogBoundaryForm
  rw [hx, hy]
  ring

/-- Any vector Green-orthogonal to all diagonal boundary data is itself
diagonal. -/
theorem nativeCarryReflectedLogBoundaryOrthogonal_le_diagonal :
    nativeCarryReflectedLogBoundaryOrthogonal
        nativeCarryReflectedLogDiagonal ≤
      nativeCarryReflectedLogDiagonal := by
  intro x hx
  rw [mem_nativeCarryReflectedLogDiagonal]
  change ∀ y, y ∈ nativeCarryReflectedLogDiagonal →
    nativeCarryReflectedLogBoundaryForm y x = 0 at hx
  have hone : ((1 : ℂ), (1 : ℂ)) ∈ nativeCarryReflectedLogDiagonal := by
    rfl
  have h := hx ((1 : ℂ), (1 : ℂ)) hone
  unfold nativeCarryReflectedLogBoundaryForm at h
  have hsub : x.1 - x.2 = 0 := by simpa using h
  exact sub_eq_zero.mp hsub

/-- The diagonal is maximal isotropic: it equals its oriented Green orthogonal.
This is the boundary-level self-adjointness condition for the doubled channel. -/
theorem nativeCarryReflectedLogDiagonal_orthogonal_eq :
    nativeCarryReflectedLogBoundaryOrthogonal
        nativeCarryReflectedLogDiagonal =
      nativeCarryReflectedLogDiagonal := by
  apply le_antisymm
  · exact nativeCarryReflectedLogBoundaryOrthogonal_le_diagonal
  · exact nativeCarryReflectedLogDiagonal_le_orthogonal

/-- Green reflection is complex conjugation of carry time. -/
theorem reflectedParameter_carryComplexTimeParameter
    (z : ℂ) :
    reflectedParameter (carryComplexTimeParameter z) =
      carryComplexTimeParameter ((starRingEnd ℂ) z) := by
  unfold reflectedParameter carryComplexTimeParameter
  simp
  ring

/-- Direct/reflected native log-wave values at the common inner endpoint. -/
def nativeCarryReflectedLogBoundaryValue
    (z : ℂ) : NativeCarryReflectedLogBoundary :=
  (nativeCarryLogWave z 0,
    nativeCarryLogWave ((starRingEnd ℂ) z) 0)

@[simp] theorem nativeCarryReflectedLogBoundaryValue_eq
    (z : ℂ) :
    nativeCarryReflectedLogBoundaryValue z = (1, 1) := by
  ext <;> simp [nativeCarryReflectedLogBoundaryValue, nativeCarryLogWave]

/-- Characteristic outputs of the direct and reflected log-wave equations at
the inner endpoint. -/
def nativeCarryReflectedLogBoundaryFlux
    (z : ℂ) : NativeCarryReflectedLogBoundary :=
  (z * nativeCarryLogWave z 0,
    (starRingEnd ℂ) z * nativeCarryLogWave ((starRingEnd ℂ) z) 0)

@[simp] theorem nativeCarryReflectedLogBoundaryFlux_eq
    (z : ℂ) :
    nativeCarryReflectedLogBoundaryFlux z =
      (z, (starRingEnd ℂ) z) := by
  ext <;> simp [nativeCarryReflectedLogBoundaryFlux, nativeCarryLogWave]

/-- The fixed reflected diagonal boundary condition accepts the characteristic
flux exactly at real complex time. -/
theorem nativeCarryReflectedLogBoundaryFlux_mem_diagonal_iff
    (z : ℂ) :
    nativeCarryReflectedLogBoundaryFlux z ∈
        nativeCarryReflectedLogDiagonal ↔
      z.im = 0 := by
  rw [mem_nativeCarryReflectedLogDiagonal]
  simp only [nativeCarryReflectedLogBoundaryFlux_eq, Prod.fst, Prod.snd]
  constructor
  · intro hz
    have him := congrArg Complex.im hz
    simp only [Complex.conj_im] at him
    linarith
  · intro him
    apply Complex.ext
    · simp
    · simp [him]

/-- Named form of the fixed reflected-flux matching condition. -/
def NativeCarryReflectedLogFluxMatches (z : ℂ) : Prop :=
  nativeCarryReflectedLogBoundaryFlux z ∈
    nativeCarryReflectedLogDiagonal

/-- Reflected-flux matching is exactly reality of the characteristic time. -/
theorem nativeCarryReflectedLogFluxMatches_iff_im_eq_zero
    (z : ℂ) :
    NativeCarryReflectedLogFluxMatches z ↔ z.im = 0 :=
  nativeCarryReflectedLogBoundaryFlux_mem_diagonal_iff z

/-- The remaining bracket-to-symmetric-boundary transport, stated without a
Genuine coefficient. -/
def NativeCarryBracketClosureForcesReflectedLogFluxMatching : Prop :=
  ∀ {z : ℂ}, carryComplexTimeParameter z ∈ genuineCriticalStrip →
    NativeCarryLogWaveBoundaryCloses z →
      NativeCarryReflectedLogFluxMatches z

/-- The bracket-to-reflected-boundary transport is exactly the existing complex
time zero-rigidity target, now expressed through a fixed maximal isotropic
boundary condition. -/
theorem nativeCarryBracketClosureForcesReflectedLogFluxMatching_iff_zeroRigidity :
    NativeCarryBracketClosureForcesReflectedLogFluxMatching ↔
      NativeCarryComplexTimeZeroRigidity := by
  constructor
  · intro hbridge z hz hres
    have hboundary :=
      (nativeCarryLogWaveBoundaryCloses_iff_resonance hz).2 hres
    exact
      (nativeCarryReflectedLogFluxMatches_iff_im_eq_zero z).1
        (hbridge hz hboundary)
  · intro hrigid z hz hboundary
    have hres :=
      (nativeCarryLogWaveBoundaryCloses_iff_resonance hz).1 hboundary
    exact
      (nativeCarryReflectedLogFluxMatches_iff_im_eq_zero z).2
        (hrigid hz hres)

/-- Once the fixed bracket boundary is transported to the reflected maximal
isotropic boundary, strong off-critical nonvanishing follows from the already
audited native carry chain. -/
theorem genuineStrongNonvanishingInStrip_of_reflectedLogFluxMatching
    (hbridge : NativeCarryBracketClosureForcesReflectedLogFluxMatching) :
    GenuineStrongNonvanishingInStrip :=
  (nativeCarryComplexTimeZeroRigidity_iff_strongNonvanishing).1
    ((nativeCarryBracketClosureForcesReflectedLogFluxMatching_iff_zeroRigidity).1
      hbridge)

end

end CPFormal.Analytic.Cp
