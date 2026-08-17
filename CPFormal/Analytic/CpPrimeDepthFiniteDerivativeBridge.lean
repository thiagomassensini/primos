import CPFormal.Analytic.CpPrimeDepthLogWaveBridge
import CPFormal.Analytic.CpFiniteLogJetCommutator
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Finite native-camera derivative through the Mangoldt carry ledger

The prime-depth bridge reconstructs `log n` exactly from active prime-camera
carry depths and from the classical divisor-sum von Mangoldt ledger.  This file
puts that reconstruction inside the spectral derivative of the finite camera.

The order of construction is deliberately denominator-free:

1. differentiate the positive Dirichlet sample `n^(-s)` pointwise;
2. transport the derivative through the finite seed/bracket camera by
   linearity of finite sums;
3. replace `log n` by `sum_{d|n} Lambda(d)`, or by the fully expanded atomic
   prime-camera ledger.

Thus, for every finite odd-prime camera,

`-d/ds finiteChart(p,M,n^(-s))`

is exactly the same finite camera applied to the Mangoldt-weighted field.  No
zero, quotient, analytic continuation, asymptotic estimate, or nonvanishing
hypothesis occurs in this identity.  Logarithmic-derivative formulas may be
formed only afterwards, on domains where their denominators are nonzero.
-/

open scoped BigOperators

namespace CPFormal.Analytic.Cp

open CPFormal.Genuine.Cp
open CPFormal.Carry.Positional

noncomputable section

/-- Dirichlet sample on the positive integer lattice, extended by zero away
from the positive indices actually consumed by a finite camera. -/
def positiveIntegerDirichletSample (s : ℂ) (n : ℤ) : ℂ :=
  if 0 < n then natDirichletTerm s n.natAbs else 0

/-- The same positive sample after applying the logarithmic generator. -/
def positiveIntegerLogDirichletSample (s : ℂ) (n : ℤ) : ℂ :=
  if 0 < n then natLogDirichletTerm s n.natAbs else 0

/-- Divisor-sum von Mangoldt realization of the logarithm, multiplied by the
same Dirichlet carrier. -/
def positiveIntegerMangoldtDirichletSample (s : ℂ) (n : ℤ) : ℂ :=
  if 0 < n then
    ((((∑ d ∈ n.natAbs.divisors,
        ArithmeticFunction.vonMangoldt d) : ℝ) : ℂ) *
      natDirichletTerm s n.natAbs)
  else
    0

/-- Fully expanded prime-camera realization: one von Mangoldt atom for every
positive level reached in every active prime tower. -/
def positiveIntegerAtomicPrimeCameraDirichletSample
    (s : ℂ) (n : ℤ) : ℂ :=
  if 0 < n then
    ((((∑ p ∈ n.natAbs.primeFactors,
        ∑ j ∈ Finset.range (positionalDepth p n.natAbs),
          ArithmeticFunction.vonMangoldt (p ^ (j + 1))) : ℝ) : ℂ) *
      natDirichletTerm s n.natAbs)
  else
    0

@[simp] theorem positiveIntegerDirichletSample_of_pos
    (s : ℂ) {n : ℤ} (hn : 0 < n) :
    positiveIntegerDirichletSample s n = dirichletTerm s n := by
  have hcast : (n.natAbs : ℤ) = n := by
    rw [Int.natCast_natAbs, abs_of_pos hn]
  simp [positiveIntegerDirichletSample, hn, natDirichletTerm, hcast]

@[simp] theorem positiveIntegerDirichletSample_of_nonpos
    (s : ℂ) {n : ℤ} (hn : ¬ 0 < n) :
    positiveIntegerDirichletSample s n = 0 := by
  simp [positiveIntegerDirichletSample, hn]

/-- The derivative of one positive natural Dirichlet monomial is the negative
log-weighted monomial already used by the finite log-jet API. -/
theorem hasDerivAt_natDirichletTerm_eq_neg_log
    (n : ℕ) (hn : n ≠ 0) (s : ℂ) :
    HasDerivAt (fun z : ℂ ↦ natDirichletTerm z n)
      (-natLogDirichletTerm s n) s := by
  have hinner : HasDerivAt (fun z : ℂ ↦ -z) (-1) s :=
    hasDerivAt_neg' s
  have hpower :=
    hinner.const_cpow (Or.inl (Nat.cast_ne_zero.mpr hn))
  rw [show (fun z : ℂ ↦ natDirichletTerm z n) =
      (fun z : ℂ ↦ (n : ℂ) ^ (-z)) by
    funext z
    simp [natDirichletTerm, dirichletTerm]]
  convert hpower using 1
  rw [← Complex.natCast_log]
  simp only [natLogDirichletTerm, natDirichletTerm, dirichletTerm,
    Int.cast_natCast]
  ring

/-- Pointwise derivative on the zero-extended positive lattice. -/
theorem hasDerivAt_positiveIntegerDirichletSample
    (n : ℤ) (s : ℂ) :
    HasDerivAt (fun z : ℂ ↦ positiveIntegerDirichletSample z n)
      (-positiveIntegerLogDirichletSample s n) s := by
  by_cases hn : 0 < n
  · have hnatPos : 0 < n.natAbs := by
      have hcast : (0 : ℤ) < (n.natAbs : ℤ) := by
        rw [Int.natCast_natAbs, abs_of_pos hn]
        exact hn
      exact_mod_cast hcast
    simp only [positiveIntegerDirichletSample,
      positiveIntegerLogDirichletSample, if_pos hn]
    exact hasDerivAt_natDirichletTerm_eq_neg_log
      n.natAbs hnatPos.ne' s
  · simp only [positiveIntegerDirichletSample,
      positiveIntegerLogDirichletSample, if_neg hn, neg_zero]
    exact hasDerivAt_const (x := s) (c := (0 : ℂ))

/-- Any pointwise derivative transports through the finite seed/bracket camera.
This is a purely finite linearity theorem. -/
theorem hasDerivAt_finiteChart_of_pointwise
    (p M : ℕ) (field : ℂ → ℤ → ℂ) (field' : ℤ → ℂ) (s : ℂ)
    (hfield : ∀ n : ℤ,
      HasDerivAt (fun z : ℂ ↦ field z n) (field' n) s) :
    HasDerivAt
      (fun z : ℂ ↦ finiteChart p M (field z))
      (finiteChart p M field') s := by
  classical
  have hseed :
      HasDerivAt
        (fun z : ℂ ↦
          ∑ n ∈ Finset.Icc (1 : ℤ) (halfRange p : ℤ), field z n)
        (∑ n ∈ Finset.Icc (1 : ℤ) (halfRange p : ℤ), field' n) s := by
    apply HasDerivAt.fun_sum
    intro n _hn
    exact hfield n
  have hblocks :
      HasDerivAt
        (fun z : ℂ ↦
          ∑ k ∈ Finset.range M,
            ((∑ a ∈ balancedOffsets p,
                field z (alignedCenter p k + a)) -
              ((p - 1 : ℕ) : ℂ) * field z (alignedCenter p k)))
        (∑ k ∈ Finset.range M,
          ((∑ a ∈ balancedOffsets p,
              field' (alignedCenter p k + a)) -
            ((p - 1 : ℕ) : ℂ) * field' (alignedCenter p k))) s := by
    apply HasDerivAt.fun_sum
    intro k _hk
    have hlegs :
        HasDerivAt
          (fun z : ℂ ↦
            ∑ a ∈ balancedOffsets p,
              field z (alignedCenter p k + a))
          (∑ a ∈ balancedOffsets p,
            field' (alignedCenter p k + a)) s := by
      apply HasDerivAt.fun_sum
      intro a _ha
      exact hfield (alignedCenter p k + a)
    exact hlegs.sub
      ((hfield (alignedCenter p k)).const_mul ((p - 1 : ℕ) : ℂ))
  simpa [finiteChart, seedSum, bracket, legSum] using hseed.add hblocks

/-- Negating every integer sample negates the finite camera resultant. -/
theorem finiteChart_neg (p M : ℕ) (f : ℤ → ℂ) :
    finiteChart p M (fun n ↦ -f n) = -finiteChart p M f := by
  classical
  simp [finiteChart, seedSum, bracket, legSum]
  ring

/-- Replacing the zero-extended positive field by the ordinary Dirichlet field
changes no coordinate consumed by an odd-prime finite camera. -/
theorem finiteChart_positiveIntegerDirichletSample_eq_dirichlet
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) (s : ℂ) :
    finiteChart p M (positiveIntegerDirichletSample s) =
      finiteChart p M (dirichletTerm s) := by
  have hprefix :
      (∑ n ∈ Finset.Icc (1 : ℤ)
          ((p : ℤ) * (M : ℤ) + (halfRange p : ℤ)),
          positiveIntegerDirichletSample s n) =
        ∑ n ∈ Finset.Icc (1 : ℤ)
          ((p : ℤ) * (M : ℤ) + (halfRange p : ℤ)),
          dirichletTerm s n := by
    apply Finset.sum_congr rfl
    intro n hnMem
    exact positiveIntegerDirichletSample_of_pos s
      (Finset.mem_Icc.mp hnMem).1
  have hcenters :
      (∑ k ∈ Finset.range M,
          positiveIntegerDirichletSample s (alignedCenter p k)) =
        ∑ k ∈ Finset.range M,
          dirichletTerm s (alignedCenter p k) := by
    apply Finset.sum_congr rfl
    intro k _hk
    apply positiveIntegerDirichletSample_of_pos
    unfold alignedCenter
    have hpZ : (0 : ℤ) < (p : ℤ) := by
      exact_mod_cast hp.pos
    have hkZ : (0 : ℤ) < ((k + 1 : ℕ) : ℤ) := by
      exact_mod_cast Nat.succ_pos k
    exact mul_pos hpZ hkZ
  calc
    finiteChart p M (positiveIntegerDirichletSample s) =
        (∑ n ∈ Finset.Icc (1 : ℤ)
          ((p : ℤ) * (M : ℤ) + (halfRange p : ℤ)),
          positiveIntegerDirichletSample s n) -
          (p : ℂ) * ∑ k ∈ Finset.range M,
            positiveIntegerDirichletSample s (alignedCenter p k) :=
      finiteChart_eq_positiveIntervalSum_sub_p_mul_centerSum
        p hp hpodd M (positiveIntegerDirichletSample s)
    _ = (∑ n ∈ Finset.Icc (1 : ℤ)
          ((p : ℤ) * (M : ℤ) + (halfRange p : ℤ)),
          dirichletTerm s n) -
          (p : ℂ) * ∑ k ∈ Finset.range M,
            dirichletTerm s (alignedCenter p k) := by
      rw [hprefix, hcenters]
    _ = finiteChart p M (dirichletTerm s) :=
      (finiteChart_eq_positiveIntervalSum_sub_p_mul_centerSum
        p hp hpodd M (dirichletTerm s)).symm

/-- The logarithmic sample is exactly the divisor-sum Mangoldt sample. -/
theorem positiveIntegerLogDirichletSample_eq_mangoldt
    (s : ℂ) (n : ℤ) :
    positiveIntegerLogDirichletSample s n =
      positiveIntegerMangoldtDirichletSample s n := by
  by_cases hn : 0 < n
  · simp only [positiveIntegerLogDirichletSample,
      positiveIntegerMangoldtDirichletSample, if_pos hn]
    rw [primePowerSignal_divisorSum_eq_integerLog]
  · simp [positiveIntegerLogDirichletSample,
      positiveIntegerMangoldtDirichletSample, hn]

/-- The divisor-sum Mangoldt sample is also the fully expanded atomic
prime-camera sample. -/
theorem positiveIntegerMangoldtDirichletSample_eq_atomicPrimeCamera
    (s : ℂ) (n : ℤ) :
    positiveIntegerMangoldtDirichletSample s n =
      positiveIntegerAtomicPrimeCameraDirichletSample s n := by
  by_cases hn : 0 < n
  · have hnatPos : 0 < n.natAbs := by
      have hcast : (0 : ℤ) < (n.natAbs : ℤ) := by
        rw [Int.natCast_natAbs, abs_of_pos hn]
        exact hn
      exact_mod_cast hcast
    simp only [positiveIntegerMangoldtDirichletSample,
      positiveIntegerAtomicPrimeCameraDirichletSample, if_pos hn]
    rw [allPrimeCameraAtomicLedger_eq_divisorMangoldtLedger hnatPos.ne']
  · simp [positiveIntegerMangoldtDirichletSample,
      positiveIntegerAtomicPrimeCameraDirichletSample, hn]

/-- Denominator-free finite bridge: the spectral derivative of the finite
camera is the negative camera readout of the divisor-sum Mangoldt field. -/
theorem hasDerivAt_finiteChart_dirichlet_eq_neg_mangoldt
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) (s : ℂ) :
    HasDerivAt
      (fun z : ℂ ↦ finiteChart p M (dirichletTerm z))
      (-finiteChart p M (positiveIntegerMangoldtDirichletSample s)) s := by
  have hraw :=
    hasDerivAt_finiteChart_of_pointwise
      p M positiveIntegerDirichletSample
      (fun n ↦ -positiveIntegerLogDirichletSample s n) s
      (fun n ↦ hasDerivAt_positiveIntegerDirichletSample n s)
  have hfun :
      (fun z : ℂ ↦ finiteChart p M (positiveIntegerDirichletSample z)) =
        (fun z : ℂ ↦ finiteChart p M (dirichletTerm z)) := by
    funext z
    exact finiteChart_positiveIntegerDirichletSample_eq_dirichlet
      p M hp hpodd z
  have hsamples :
      positiveIntegerLogDirichletSample s =
        positiveIntegerMangoldtDirichletSample s := by
    funext n
    exact positiveIntegerLogDirichletSample_eq_mangoldt s n
  have hderiv :
      finiteChart p M (fun n ↦ -positiveIntegerLogDirichletSample s n) =
        -finiteChart p M (positiveIntegerMangoldtDirichletSample s) := by
    rw [finiteChart_neg, hsamples]
  rw [hfun, hderiv] at hraw
  exact hraw

/-- Equivalent readout form of the same bridge. -/
theorem neg_deriv_finiteChart_dirichlet_eq_mangoldt
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) (s : ℂ) :
    -deriv (fun z : ℂ ↦ finiteChart p M (dirichletTerm z)) s =
      finiteChart p M (positiveIntegerMangoldtDirichletSample s) := by
  have h := hasDerivAt_finiteChart_dirichlet_eq_neg_mangoldt
    p M hp hpodd s
  rw [h.deriv]
  simp

/-- Fully expanded prime-camera version: one Mangoldt atom per positive carry
level gives exactly the negative spectral derivative of the finite chart. -/
theorem neg_deriv_finiteChart_dirichlet_eq_atomicPrimeCamera
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) (s : ℂ) :
    -deriv (fun z : ℂ ↦ finiteChart p M (dirichletTerm z)) s =
      finiteChart p M
        (positiveIntegerAtomicPrimeCameraDirichletSample s) := by
  rw [neg_deriv_finiteChart_dirichlet_eq_mangoldt p M hp hpodd s]
  have hsamples :
      positiveIntegerMangoldtDirichletSample s =
        positiveIntegerAtomicPrimeCameraDirichletSample s := by
    funext n
    exact positiveIntegerMangoldtDirichletSample_eq_atomicPrimeCamera s n
  rw [hsamples]

/-- Kernel checkpoint collecting the pointwise, divisor-sum, and fully atomic
finite-camera forms without introducing a quotient. -/
theorem finiteChart_mangoldtDerivative_checkpoint
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) (s : ℂ) :
    HasDerivAt
        (fun z : ℂ ↦ finiteChart p M (dirichletTerm z))
        (-finiteChart p M (positiveIntegerMangoldtDirichletSample s)) s ∧
      -deriv (fun z : ℂ ↦ finiteChart p M (dirichletTerm z)) s =
        finiteChart p M (positiveIntegerMangoldtDirichletSample s) ∧
      -deriv (fun z : ℂ ↦ finiteChart p M (dirichletTerm z)) s =
        finiteChart p M
          (positiveIntegerAtomicPrimeCameraDirichletSample s) := by
  exact ⟨
    hasDerivAt_finiteChart_dirichlet_eq_neg_mangoldt p M hp hpodd s,
    neg_deriv_finiteChart_dirichlet_eq_mangoldt p M hp hpodd s,
    neg_deriv_finiteChart_dirichlet_eq_atomicPrimeCamera
      p M hp hpodd s⟩

end

end CPFormal.Analytic.Cp
