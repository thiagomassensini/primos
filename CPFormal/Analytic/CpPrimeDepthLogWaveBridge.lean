import CPFormal.Analytic.CpPrimeTowerCarryMangoldtBridge
import CPFormal.Analytic.CpNativeCarryLogWaveBoundaryEquivalence

/-!
# Prime-depth coordinates inside the native log wave

The previous prime-tower bridge proves that, for every nonzero natural number,
the sum of the logarithmic vertical charges of its active prime cameras is
exactly `log n`:

`sum_{p | n} positionalDepth(p,n) * log p = log n`.

This module substitutes that identity directly into the native logarithmic
wave.  Thus the positive-integer sample consumed by the finite bracket camera
can be written without taking `log n` as a primitive coordinate: its wave
coordinate is reconstructed from the carry depths of the active prime cameras.

The chain formalized here is:

`prime-camera depths -> logarithmic coordinate -> native log wave ->
 finite bracket camera -> boundary closure / resonance`.

The result is an exact crosswalk of already-defined objects.  It does not claim
that the prime subatlas generates the all-bases carry geometry, nor that von
Mangoldt alone contains the Green / endpoint / bulk state.
-/

open scoped BigOperators Topology

namespace CPFormal.Analytic.Cp

open Filter

noncomputable section

/-- The logarithmic coordinate reconstructed from all active prime-camera
vertical charges of `n`. -/
def primeDepthLogCoordinate (n : ℕ) : ℝ :=
  ∑ p ∈ n.primeFactors, primeVerticalScale p n

/-- For every nonzero integer index, the prime-depth coordinate is exactly the
ordinary logarithmic coordinate. -/
theorem primeDepthLogCoordinate_eq_log
    {n : ℕ} (hn : n ≠ 0) :
    primeDepthLogCoordinate n = Real.log n := by
  exact sum_primeVerticalScale_primeFactors_eq_log hn

/-- The same coordinate written completely atomically: one von Mangoldt atom
for every positive level reached in every active prime camera. -/
theorem primeDepthLogCoordinate_eq_atomicPrimeCameraLedger
    (n : ℕ) :
    primeDepthLogCoordinate n =
      ∑ p ∈ n.primeFactors,
        ∑ j ∈ Finset.range (CPFormal.Carry.Positional.positionalDepth p n),
          ArithmeticFunction.vonMangoldt (p ^ (j + 1)) := by
  unfold primeDepthLogCoordinate
  apply Finset.sum_congr rfl
  intro p hpMem
  exact
    (sum_vonMangoldt_primeTower_to_positionalDepth_eq_verticalScale
      (Nat.prime_of_mem_primeFactors hpMem)).symm

/-- Evaluating the native log wave at the reconstructed prime-depth coordinate
is exactly the usual Dirichlet monomial. -/
theorem nativeCarryLogWave_primeDepthLogCoordinate_eq_dirichletTerm
    (z : ℂ) {n : ℕ} (hn : 0 < n) :
    nativeCarryLogWave z (primeDepthLogCoordinate n : ℂ) =
      dirichletTerm (carryComplexTimeParameter z) (n : ℤ) := by
  rw [primeDepthLogCoordinate_eq_log hn.ne']
  exact nativeCarryLogWave_log_nat_eq_dirichletTerm z n hn

/-- Fully expanded version of the previous theorem: the argument of the native
wave is literally the all-prime-camera atomic ledger.  The ledger is first
summed in `ℝ`, then injected faithfully into `ℂ`. -/
theorem nativeCarryLogWave_atomicPrimeCameraLedger_eq_dirichletTerm
    (z : ℂ) {n : ℕ} (hn : 0 < n) :
    nativeCarryLogWave z
        (((∑ p ∈ n.primeFactors,
            ∑ j ∈ Finset.range
                (CPFormal.Carry.Positional.positionalDepth p n),
              ArithmeticFunction.vonMangoldt (p ^ (j + 1))) : ℝ) : ℂ) =
      dirichletTerm (carryComplexTimeParameter z) (n : ℤ) := by
  have hcoord :
      (((∑ p ∈ n.primeFactors,
          ∑ j ∈ Finset.range
              (CPFormal.Carry.Positional.positionalDepth p n),
            ArithmeticFunction.vonMangoldt (p ^ (j + 1))) : ℝ) : ℂ) =
        (primeDepthLogCoordinate n : ℂ) := by
    exact congrArg (fun x : ℝ => (x : ℂ))
      (primeDepthLogCoordinate_eq_atomicPrimeCameraLedger n).symm
  rw [hcoord]
  exact nativeCarryLogWave_primeDepthLogCoordinate_eq_dirichletTerm z hn

/-- Integer-indexed field obtained by feeding the native wave the prime-depth
coordinate on positive integers.  The nonpositive branch is zero because the
finite arithmetic camera below only samples the positive integer lattice. -/
def primeDepthWaveIntegerSample (z : ℂ) (n : ℤ) : ℂ :=
  if 0 < n then
    nativeCarryLogWave z (primeDepthLogCoordinate n.natAbs : ℂ)
  else
    0

/-- On every positive integer, the prime-depth wave field is exactly the
Dirichlet sample used by the existing bracket camera. -/
@[simp] theorem primeDepthWaveIntegerSample_of_pos
    (z : ℂ) {n : ℤ} (hn : 0 < n) :
    primeDepthWaveIntegerSample z n =
      dirichletTerm (carryComplexTimeParameter z) n := by
  rw [primeDepthWaveIntegerSample, if_pos hn]
  have hnatPos : 0 < n.natAbs := by
    have hcast : (0 : ℤ) < (n.natAbs : ℤ) := by
      rw [Int.natCast_natAbs, abs_of_pos hn]
      exact hn
    exact_mod_cast hcast
  have hsample :=
    nativeCarryLogWave_primeDepthLogCoordinate_eq_dirichletTerm z hnatPos
  have hcast : (n.natAbs : ℤ) = n := by
    rw [Int.natCast_natAbs, abs_of_pos hn]
  simpa [hcast] using hsample

/-- Every finite odd-prime bracket camera sees exactly the same resultant when
its positive integer field is generated from prime-depth coordinates instead
of from `log n` directly. -/
theorem finiteChart_primeDepthWave_eq_dirichlet
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) (z : ℂ) :
    CPFormal.Genuine.Cp.finiteChart p M (primeDepthWaveIntegerSample z) =
      CPFormal.Genuine.Cp.finiteChart p M
        (dirichletTerm (carryComplexTimeParameter z)) := by
  have hprefix :
      (∑ n ∈ Finset.Icc (1 : ℤ)
          ((p : ℤ) * (M : ℤ) +
            (CPFormal.Genuine.Cp.halfRange p : ℤ)),
          primeDepthWaveIntegerSample z n) =
        ∑ n ∈ Finset.Icc (1 : ℤ)
          ((p : ℤ) * (M : ℤ) +
            (CPFormal.Genuine.Cp.halfRange p : ℤ)),
          dirichletTerm (carryComplexTimeParameter z) n := by
    apply Finset.sum_congr rfl
    intro n hnMem
    have hnpos : 0 < n := by
      have hnleft := (Finset.mem_Icc.mp hnMem).1
      omega
    exact primeDepthWaveIntegerSample_of_pos z hnpos
  have hcenters :
      (∑ k ∈ Finset.range M,
          primeDepthWaveIntegerSample z
            (CPFormal.Genuine.Cp.alignedCenter p k)) =
        ∑ k ∈ Finset.range M,
          dirichletTerm (carryComplexTimeParameter z)
            (CPFormal.Genuine.Cp.alignedCenter p k) := by
    apply Finset.sum_congr rfl
    intro k _hk
    apply primeDepthWaveIntegerSample_of_pos
    unfold CPFormal.Genuine.Cp.alignedCenter
    have hpZ : (0 : ℤ) < (p : ℤ) := by
      exact_mod_cast hp.pos
    have hkZ : (0 : ℤ) < ((k + 1 : ℕ) : ℤ) := by
      exact_mod_cast Nat.succ_pos k
    exact mul_pos hpZ hkZ
  rw [
    CPFormal.Genuine.Cp.finiteChart_eq_positiveIntervalSum_sub_p_mul_centerSum
      p hp hpodd M (primeDepthWaveIntegerSample z),
    CPFormal.Genuine.Cp.finiteChart_eq_positiveIntervalSum_sub_p_mul_centerSum
      p hp hpodd M (dirichletTerm (carryComplexTimeParameter z)),
    hprefix, hcenters]

/-- Boundary closure of the fixed camera when its positive integer samples are
constructed from prime-camera carry depths. -/
def PrimeDepthWaveBoundaryCloses (z : ℂ) : Prop :=
  Tendsto
    (fun M : ℕ =>
      CPFormal.Genuine.Cp.finiteChart 3 M (primeDepthWaveIntegerSample z))
    atTop (nhds 0)

/-- Replacing `log n` by the reconstructed prime-depth coordinate changes
nothing in the boundary problem. -/
theorem primeDepthWaveBoundaryCloses_iff_nativeCarryLogWaveBoundaryCloses
    (z : ℂ) :
    PrimeDepthWaveBoundaryCloses z ↔ NativeCarryLogWaveBoundaryCloses z := by
  have hfun :
      (fun M : ℕ =>
        CPFormal.Genuine.Cp.finiteChart 3 M
          (primeDepthWaveIntegerSample z)) =
        (fun M : ℕ =>
          CPFormal.Genuine.Cp.finiteChart 3 M
            (dirichletTerm (carryComplexTimeParameter z))) := by
    funext M
    exact finiteChart_primeDepthWave_eq_dirichlet
      3 M (by norm_num) (by norm_num) z
  unfold PrimeDepthWaveBoundaryCloses NativeCarryLogWaveBoundaryCloses
  rw [hfun]
  rfl

/-- Consequently, in the existing Genuine strip, closing the bracket boundary
of the prime-depth-generated wave is exactly the already defined native
complex-time resonance. -/
theorem primeDepthWaveBoundaryCloses_iff_resonance
    {z : ℂ} (hz : carryComplexTimeParameter z ∈ genuineCriticalStrip) :
    PrimeDepthWaveBoundaryCloses z ↔
      IsNativeCarryComplexTimeResonance z := by
  rw [primeDepthWaveBoundaryCloses_iff_nativeCarryLogWaveBoundaryCloses]
  exact nativeCarryLogWaveBoundaryCloses_iff_resonance hz

/-- Full characteristic problem with the unchanged native interior equation and
the prime-depth-generated arithmetic boundary. -/
def PrimeDepthWaveCharacteristic (z : ℂ) : Prop :=
  (∀ u : ℂ,
    nativeCarryLogDilationExpression
        (nativeCarryLogWave z u)
        (-(carryComplexTimeParameter z) * nativeCarryLogWave z u) =
      z * nativeCarryLogWave z u) ∧
  PrimeDepthWaveBoundaryCloses z

/-- The characteristic problem survives the coordinate replacement exactly:
prime-depth wave characteristic iff native complex-time resonance. -/
theorem primeDepthWaveCharacteristic_iff_resonance
    {z : ℂ} (hz : carryComplexTimeParameter z ∈ genuineCriticalStrip) :
    PrimeDepthWaveCharacteristic z ↔
      IsNativeCarryComplexTimeResonance z := by
  constructor
  · rintro ⟨_hinterior, hboundary⟩
    exact (primeDepthWaveBoundaryCloses_iff_resonance hz).1 hboundary
  · intro hres
    refine ⟨nativeCarryLogDilationExpression_wave_eq z, ?_⟩
    exact (primeDepthWaveBoundaryCloses_iff_resonance hz).2 hres

end

end CPFormal.Analytic.Cp
