import CPFormal.Analytic.CpC2OddCorePushforwardTfvd
import CPFormal.Analytic.CpFiniteLogJetCommutator

/-!
# Dirichlet pushforward of the connected C2 cell

The concrete C2 port previously encoded only the static mass square

`(a_T(p), a_T(pq); 1, a_T(q))`.

This module lifts every vertex of that square to its Dirichlet one-jet

`(a_T(m) m^(-s), a_T(m) log(m) m^(-s))`.

The ordinary determinant is the connected mass cumulant dressed by the
Dirichlet carrier at `pq`.  Differentiating that determinant uses the Leibniz
rule, hence two existing `sameSEdgeBoundaryWedge` cells.  Their sum is exactly
the logarithmic spectral gap between the joint `pq` path and the factorized
`p,q` path.  At distinct odd primes it is also exactly the finite extracted
coefficient `b_T(pq)` times `(pq)^(-s)`.

This closes the missing phase injection in the finite C2 readout.  It does not
identify the local semiprime gap with the already existing global cross-prime
aligned prefix gap; that remains a separate camera-level intertwiner.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-! ## Seed-normalized Dirichlet one-jet -/

/-- Seed-normalized C2 mass dressed by the ordinary Dirichlet monomial. -/
def c2OddCoreDirichletMassValue
    (cutoff : ℕ) (s : ℂ) (m : ℕ) : ℂ :=
  (c2OddCoreNormalizedMassArithmetic cutoff m : ℂ) *
    natDirichletTerm s m

/-- The same mass dressed by the native logarithmic Dirichlet monomial. -/
def c2OddCoreLogDirichletMassValue
    (cutoff : ℕ) (s : ℂ) (m : ℕ) : ℂ :=
  (c2OddCoreNormalizedMassArithmetic cutoff m : ℂ) *
    natLogDirichletTerm s m

@[simp] theorem c2OddCoreDirichletMassValue_one
    (cutoff : ℕ) (s : ℂ) :
    c2OddCoreDirichletMassValue cutoff s 1 = 1 := by
  simp [c2OddCoreDirichletMassValue, natDirichletTerm, dirichletTerm]

@[simp] theorem c2OddCoreLogDirichletMassValue_one
    (cutoff : ℕ) (s : ℂ) :
    c2OddCoreLogDirichletMassValue cutoff s 1 = 0 := by
  simp [c2OddCoreLogDirichletMassValue, natLogDirichletTerm]

/-- Symmetric Leibniz form of the logarithmic Dirichlet product rule. -/
theorem natLogDirichletTerm_mul_leibniz
    (p q : ℕ) (hp : p ≠ 0) (hq : q ≠ 0) (s : ℂ) :
    natLogDirichletTerm s (p * q) =
      natLogDirichletTerm s p * natDirichletTerm s q +
        natDirichletTerm s p * natLogDirichletTerm s q := by
  rw [natLogDirichletTerm_mul p q hp hq]
  unfold natLogDirichletTerm
  ring

/-! ## Ordinary Dirichlet pushforward of the mass square -/

/-- The static connected square after every vertex has been dressed by its
ordinary Dirichlet carrier. -/
def c2OddCoreDirichletSpectralGap
    (cutoff p q : ℕ) (s : ℂ) : ℂ :=
  sameSEdgeBoundaryWedge
    (c2OddCoreDirichletMassValue cutoff s p)
    (c2OddCoreDirichletMassValue cutoff s (p * q))
    (c2OddCoreDirichletMassValue cutoff s 1)
    (c2OddCoreDirichletMassValue cutoff s q)

/-- Multiplicativity of the Dirichlet carrier leaves exactly the connected
mass coefficient at the common frequency `(p*q)^(-s)`. -/
theorem c2OddCoreDirichletSpectralGap_eq_normalizedConnected_mul
    (cutoff p q : ℕ) (s : ℂ) :
    c2OddCoreDirichletSpectralGap cutoff p q s =
      (((c2OddCoreNormalizedMassArithmetic cutoff (p * q) -
          c2OddCoreNormalizedMassArithmetic cutoff p *
            c2OddCoreNormalizedMassArithmetic cutoff q : ℝ) : ℂ)) *
        natDirichletTerm s (p * q) := by
  unfold c2OddCoreDirichletSpectralGap sameSEdgeBoundaryWedge
  rw [c2OddCoreDirichletMassValue_one]
  unfold c2OddCoreDirichletMassValue
  rw [natDirichletTerm_mul p q s]
  push_cast
  ring

/-- At odd prime vertices, the ordinary spectral cell is the concrete C2
cumulant dressed by the frequency at `pq`. -/
theorem c2OddCoreDirichletSpectralGap_eq_connectedCumulant_mul
    (cutoff : ℕ) {p q : ℕ}
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q) (s : ℂ) :
    c2OddCoreDirichletSpectralGap cutoff p q s =
      (c2OddCoreConnectedCumulantReal cutoff p q : ℂ) *
        natDirichletTerm s (p * q) := by
  rw [c2OddCoreDirichletSpectralGap_eq_normalizedConnected_mul]
  have hpqneone : p * q ≠ 1 := by
    have hfour : 4 ≤ p * q := by
      have hmul := Nat.mul_le_mul hp.two_le hq.two_le
      norm_num at hmul ⊢
      exact hmul
    omega
  rw [c2OddCoreNormalizedMassArithmetic_eq_mass
      cutoff (Nat.mul_ne_zero hp.ne_zero hq.ne_zero) hpqneone
        (hpodd.mul hqodd),
    c2OddCoreNormalizedMassArithmetic_eq_mass
      cutoff hp.ne_zero hp.ne_one hpodd,
    c2OddCoreNormalizedMassArithmetic_eq_mass
      cutoff hq.ne_zero hq.ne_one hqodd]
  unfold c2OddCoreConnectedCumulantReal
    c2OddCoreConnectedCumulant
  push_cast
  ring

/-! ## The two logarithmic spectral paths and their gap -/

/-- Logarithmic product-rule contribution carried by the joint vertex `pq`. -/
def c2OddCoreJointSpectralPath
    (cutoff p q : ℕ) (s : ℂ) : ℂ :=
  c2OddCoreLogDirichletMassValue cutoff s (p * q) *
      c2OddCoreDirichletMassValue cutoff s 1 +
    c2OddCoreDirichletMassValue cutoff s (p * q) *
      c2OddCoreLogDirichletMassValue cutoff s 1

/-- Logarithmic product-rule contribution carried by the separate vertices
`p` and `q`. -/
def c2OddCoreFactorizedSpectralPath
    (cutoff p q : ℕ) (s : ℂ) : ℂ :=
  c2OddCoreLogDirichletMassValue cutoff s p *
      c2OddCoreDirichletMassValue cutoff s q +
    c2OddCoreDirichletMassValue cutoff s p *
      c2OddCoreLogDirichletMassValue cutoff s q

/-- Spectral gap obtained by differentiating the connected Dirichlet
square: joint path minus factorized path. -/
def c2OddCoreDirichletLogSpectralGap
    (cutoff p q : ℕ) (s : ℂ) : ℂ :=
  c2OddCoreJointSpectralPath cutoff p q s -
    c2OddCoreFactorizedSpectralPath cutoff p q s

/-- The spectral gap is the normalized connected mass coefficient times the
native log-Dirichlet vertex at `pq`. -/
theorem c2OddCoreDirichletLogSpectralGap_eq_normalizedConnected_mul
    (cutoff p q : ℕ) (hp : p ≠ 0) (hq : q ≠ 0) (s : ℂ) :
    c2OddCoreDirichletLogSpectralGap cutoff p q s =
      (((c2OddCoreNormalizedMassArithmetic cutoff (p * q) -
          c2OddCoreNormalizedMassArithmetic cutoff p *
            c2OddCoreNormalizedMassArithmetic cutoff q : ℝ) : ℂ)) *
        natLogDirichletTerm s (p * q) := by
  unfold c2OddCoreDirichletLogSpectralGap
    c2OddCoreJointSpectralPath c2OddCoreFactorizedSpectralPath
  rw [c2OddCoreDirichletMassValue_one,
    c2OddCoreLogDirichletMassValue_one]
  simp only [mul_one, mul_zero, add_zero]
  unfold c2OddCoreDirichletMassValue
    c2OddCoreLogDirichletMassValue
  rw [natLogDirichletTerm_mul_leibniz p q hp hq s]
  push_cast
  ring

/-- At distinct odd primes, the normalized connected coefficient is the
concrete odd-core cumulant already formalized in the static port. -/
theorem c2OddCoreDirichletLogSpectralGap_eq_connectedCumulant_mul
    (cutoff : ℕ) {p q : ℕ}
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q) (s : ℂ) :
    c2OddCoreDirichletLogSpectralGap cutoff p q s =
      (c2OddCoreConnectedCumulantReal cutoff p q : ℂ) *
        natLogDirichletTerm s (p * q) := by
  rw [c2OddCoreDirichletLogSpectralGap_eq_normalizedConnected_mul
    cutoff p q hp.ne_zero hq.ne_zero s]
  have hpqneone : p * q ≠ 1 := by
    have hfour : 4 ≤ p * q := by
      have hmul := Nat.mul_le_mul hp.two_le hq.two_le
      norm_num at hmul ⊢
      exact hmul
    omega
  rw [c2OddCoreNormalizedMassArithmetic_eq_mass
      cutoff (Nat.mul_ne_zero hp.ne_zero hq.ne_zero) hpqneone
        (hpodd.mul hqodd),
    c2OddCoreNormalizedMassArithmetic_eq_mass
      cutoff hp.ne_zero hp.ne_one hpodd,
    c2OddCoreNormalizedMassArithmetic_eq_mass
      cutoff hq.ne_zero hq.ne_one hqodd]
  unfold c2OddCoreConnectedCumulantReal
    c2OddCoreConnectedCumulant
  push_cast
  ring

/-- The exact `4M/8M` Richardson correction survives the Dirichlet
one-jet injection and is dressed only by the common log-frequency at `pq`. -/
theorem c2OddCoreDirichletLogSpectralGap_richardson_exact
    {M p q : ℕ}
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    (hpM : p ≤ M) (hqM : q ≤ M) (hpqM : p * q ≤ M)
    (s : ℂ) :
    2 * c2OddCoreDirichletLogSpectralGap (8 * M) p q s -
        c2OddCoreDirichletLogSpectralGap (4 * M) p q s =
      (((1 / 2 : ℝ) *
        c2OddCoreFourScaleDefectReal M p *
          c2OddCoreFourScaleDefectReal M q : ℝ) : ℂ) *
        natLogDirichletTerm s (p * q) := by
  rw [c2OddCoreDirichletLogSpectralGap_eq_connectedCumulant_mul
      (8 * M) hp hpodd hq hqodd s,
    c2OddCoreDirichletLogSpectralGap_eq_connectedCumulant_mul
      (4 * M) hp hpodd hq hqodd s]
  have hConnected :=
    c2OddCoreConnectedCumulantReal_richardson_exact
      hp.pos hq.pos hpM hqM hpqM
  calc
    2 *
          ((c2OddCoreConnectedCumulantReal (8 * M) p q : ℂ) *
            natLogDirichletTerm s (p * q)) -
        (c2OddCoreConnectedCumulantReal (4 * M) p q : ℂ) *
          natLogDirichletTerm s (p * q) =
      ((2 * c2OddCoreConnectedCumulantReal (8 * M) p q -
          c2OddCoreConnectedCumulantReal (4 * M) p q : ℝ) : ℂ) *
        natLogDirichletTerm s (p * q) := by
          push_cast
          ring
    _ = (((1 / 2 : ℝ) *
          c2OddCoreFourScaleDefectReal M p *
            c2OddCoreFourScaleDefectReal M q : ℝ) : ℂ) *
        natLogDirichletTerm s (p * q) := by
          rw [hConnected]

/-- For distinct odd primes the injected spectral gap is exactly the finite
logarithmic coefficient `b_T(pq)` acting on the Dirichlet vertex `(pq)^(-s)`. -/
theorem c2OddCoreDirichletLogSpectralGap_eq_logCoefficient_mul
    (cutoff : ℕ) {p q : ℕ}
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q) (hpq : p ≠ q)
    (s : ℂ) :
    c2OddCoreDirichletLogSpectralGap cutoff p q s =
      (c2OddCoreLogCoefficient cutoff (p * q) : ℂ) *
        natDirichletTerm s (p * q) := by
  rw [c2OddCoreDirichletLogSpectralGap_eq_connectedCumulant_mul
    cutoff hp hpodd hq hqodd s]
  have hpqsub : p * q - 1 + 1 = p * q := by
    have hpqpos := Nat.mul_pos hp.pos hq.pos
    omega
  have hcoefficient :=
    c2OddCoreLogCoefficient_mul_positiveDirichletValue
      cutoff hp hpodd hq hqodd hpq s
  rw [positiveDirichletValue_eq_natDirichletTerm,
    positiveLogDirichletValue_eq_natLogDirichletTerm,
    hpqsub] at hcoefficient
  exact hcoefficient.symm

/-! ## Injection into the existing enriched TFVD readout -/

/-- Ordinary Dirichlet leg on the lower edge `(p,pq)` of the multiplicative
square. -/
def c2OddCoreDirichletTfvdLowerCoordinate
    (block : ℕ) (kappa omega : ℂ)
    (cutoff p q : ℕ) (s : ℂ) :
    EnrichedAngularTfvdCoordinate :=
  enrichedAngularTfvdEncode block kappa omega
    (c2OddCoreDirichletMassValue cutoff s p)
    (c2OddCoreDirichletMassValue cutoff s (p * q))
    0

/-- Ordinary Dirichlet leg on the upper edge `(1,q)`. -/
def c2OddCoreDirichletTfvdUpperCoordinate
    (block : ℕ) (kappa omega : ℂ)
    (cutoff q : ℕ) (s : ℂ) :
    EnrichedAngularTfvdCoordinate :=
  enrichedAngularTfvdEncode block kappa omega
    (c2OddCoreDirichletMassValue cutoff s 1)
    (c2OddCoreDirichletMassValue cutoff s q)
    0

/-- Log-Dirichlet leg on the lower edge `(p,pq)`. -/
def c2OddCoreLogDirichletTfvdLowerCoordinate
    (block : ℕ) (kappa omega : ℂ)
    (cutoff p q : ℕ) (s : ℂ) :
    EnrichedAngularTfvdCoordinate :=
  enrichedAngularTfvdEncode block kappa omega
    (c2OddCoreLogDirichletMassValue cutoff s p)
    (c2OddCoreLogDirichletMassValue cutoff s (p * q))
    0

/-- Log-Dirichlet leg on the upper edge `(1,q)`. -/
def c2OddCoreLogDirichletTfvdUpperCoordinate
    (block : ℕ) (kappa omega : ℂ)
    (cutoff q : ℕ) (s : ℂ) :
    EnrichedAngularTfvdCoordinate :=
  enrichedAngularTfvdEncode block kappa omega
    (c2OddCoreLogDirichletMassValue cutoff s 1)
    (c2OddCoreLogDirichletMassValue cutoff s q)
    0

/-- Decoding the four ordinary Dirichlet coordinates through the existing
valve gives exactly the Dirichlet-dressed connected spectral cell. -/
theorem c2OddCoreDirichletTfvdBoundaryCells_visible_eq_spectralGap
    (block : ℕ) {kappa omega : ℂ}
    (hkappa : kappa ≠ 0) (homega : omega ≠ 0)
    (cutoff p q : ℕ) (s : ℂ) :
    (enrichedTfvdSameSBoundaryCells kappa omega
      (c2OddCoreDirichletTfvdLowerCoordinate
        block kappa omega cutoff p q s)
      (c2OddCoreDirichletTfvdUpperCoordinate
        block kappa omega cutoff q s)).visibleCell =
      c2OddCoreDirichletSpectralGap cutoff p q s := by
  unfold c2OddCoreDirichletTfvdLowerCoordinate
    c2OddCoreDirichletTfvdUpperCoordinate
  rw [enrichedTfvdSameSBoundaryCells_encode block hkappa homega]
  rfl

/-- Leibniz readout of the pushed-forward one-jet.  The first cell pairs the
logarithmic lower leg with the ordinary upper leg; the second pairs the
ordinary lower leg with the logarithmic upper leg. -/
def c2OddCoreDirichletLogTfvdReadout
    (block : ℕ) (kappa omega : ℂ)
    (cutoff p q : ℕ) (s : ℂ) : ℂ :=
  (enrichedTfvdSameSBoundaryCells kappa omega
      (c2OddCoreLogDirichletTfvdLowerCoordinate
        block kappa omega cutoff p q s)
      (c2OddCoreDirichletTfvdUpperCoordinate
        block kappa omega cutoff q s)).visibleCell +
    (enrichedTfvdSameSBoundaryCells kappa omega
      (c2OddCoreDirichletTfvdLowerCoordinate
        block kappa omega cutoff p q s)
      (c2OddCoreLogDirichletTfvdUpperCoordinate
        block kappa omega cutoff q s)).visibleCell

/-- Decoding the four pushed-forward legs through the existing valve gives
exactly the joint-minus-factorized spectral gap. -/
theorem c2OddCoreDirichletLogTfvdReadout_eq_spectralGap
    (block : ℕ) {kappa omega : ℂ}
    (hkappa : kappa ≠ 0) (homega : omega ≠ 0)
    (cutoff p q : ℕ) (s : ℂ) :
    c2OddCoreDirichletLogTfvdReadout
        block kappa omega cutoff p q s =
      c2OddCoreDirichletLogSpectralGap cutoff p q s := by
  unfold c2OddCoreDirichletLogTfvdReadout
    c2OddCoreLogDirichletTfvdLowerCoordinate
    c2OddCoreDirichletTfvdUpperCoordinate
    c2OddCoreDirichletTfvdLowerCoordinate
    c2OddCoreLogDirichletTfvdUpperCoordinate
  rw [enrichedTfvdSameSBoundaryCells_encode block hkappa homega,
    enrichedTfvdSameSBoundaryCells_encode block hkappa homega]
  unfold c2OddCoreDirichletLogSpectralGap
    c2OddCoreJointSpectralPath c2OddCoreFactorizedSpectralPath
    sameSEdgeBoundaryWedge
  ring

/-- Richardson can be performed after TFVD encoding: the visible one-jet
readout returns the exact connected dyadic defect at the common spectral
frequency. -/
theorem c2OddCoreDirichletLogTfvdReadout_richardson_exact
    (block : ℕ) {kappa omega : ℂ}
    (hkappa : kappa ≠ 0) (homega : omega ≠ 0)
    {M p q : ℕ}
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    (hpM : p ≤ M) (hqM : q ≤ M) (hpqM : p * q ≤ M)
    (s : ℂ) :
    2 * c2OddCoreDirichletLogTfvdReadout
          block kappa omega (8 * M) p q s -
        c2OddCoreDirichletLogTfvdReadout
          block kappa omega (4 * M) p q s =
      (((1 / 2 : ℝ) *
        c2OddCoreFourScaleDefectReal M p *
          c2OddCoreFourScaleDefectReal M q : ℝ) : ℂ) *
        natLogDirichletTerm s (p * q) := by
  rw [c2OddCoreDirichletLogTfvdReadout_eq_spectralGap
      block hkappa homega (8 * M) p q s,
    c2OddCoreDirichletLogTfvdReadout_eq_spectralGap
      block hkappa homega (4 * M) p q s,
    c2OddCoreDirichletLogSpectralGap_richardson_exact
      hp hpodd hq hqodd hpM hqM hpqM s]

/-- Final finite crosswalk: the TFVD readout of the Dirichlet/log-Dirichlet
pushforward is the extracted semiprime coefficient times its frequency. -/
theorem c2OddCoreDirichletLogTfvdReadout_eq_logCoefficient_mul
    (block : ℕ) {kappa omega : ℂ}
    (hkappa : kappa ≠ 0) (homega : omega ≠ 0)
    (cutoff : ℕ) {p q : ℕ}
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q) (hpq : p ≠ q)
    (s : ℂ) :
    c2OddCoreDirichletLogTfvdReadout
        block kappa omega cutoff p q s =
      (c2OddCoreLogCoefficient cutoff (p * q) : ℂ) *
        natDirichletTerm s (p * q) := by
  rw [c2OddCoreDirichletLogTfvdReadout_eq_spectralGap
      block hkappa homega cutoff p q s,
    c2OddCoreDirichletLogSpectralGap_eq_logCoefficient_mul
      cutoff hp hpodd hq hqodd hpq s]

end

end CPFormal.Analytic.Cp
