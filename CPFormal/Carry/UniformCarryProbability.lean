import CPFormal.Carry.PositionalDecomposition
import CPFormal.Carry.CpBranchWeight
import Mathlib

/-!
# Uniform probability of a positional carry event

At depth `k`, the residue space of a base-`b` camera has exactly `b^k`
equiprobable classes.  A specified carry condition is one congruence class,
so its finite uniform probability is `1 / b^k`.

This module proves that statement as a cardinality calculation and then
identifies it with the already formalized carry mass `b^(-k)`.  The proof uses
only `0 < b`; no primality assumption enters.
-/

namespace CPFormal.Carry.Positional

open CPFormal.Carry.Cp

noncomputable section

/-- Probability of an event in a finite uniform residue space. -/
def uniformFiniteProbability
    {N : ℕ} (event : Finset (Fin N)) : ℝ :=
  (event.card : ℝ) / (N : ℝ)

/--
The distinguished congruence class in a nonempty residue space.  Translating
the singleton would give the analogous event for another congruence class;
this module formalizes only the residual-zero carry event used below.
-/
def uniformCarryEvent
    (N : ℕ) (hN : 0 < N) : Finset (Fin N) :=
  {⟨0, hN⟩}

/--
The residue of `n` at depth `k`, regarded as an element of the finite
base-`b` residue space.

This is the explicit seam between the Euclidean positional decomposition and
the finite probability space used by the carry law.
-/
def residueClassAtDepth
    (b k n : ℕ) (hb : 0 < b) : Fin (b ^ k) :=
  ⟨residueAtDepth b k n,
    (positionalDecompositionAtDepth b k n hb).2⟩

/--
The distinguished uniform carry event is exactly the event that the canonical
depth-`k` residue vanishes.
-/
@[simp] theorem residueClassAtDepth_mem_uniformCarryEvent_iff
    (b k n : ℕ) (hb : 0 < b) :
    residueClassAtDepth b k n hb ∈
        uniformCarryEvent (b ^ k) (pow_pos hb k) ↔
      residueAtDepth b k n = 0 := by
  simp [residueClassAtDepth, uniformCarryEvent]

/--
Arithmetic form of the same carry event: membership of the zero-residue class
is equivalent to divisibility by the complete depth modulus.
-/
theorem residueClassAtDepth_mem_uniformCarryEvent_iff_pow_dvd
    (b k n : ℕ) (hb : 0 < b) :
    residueClassAtDepth b k n hb ∈
        uniformCarryEvent (b ^ k) (pow_pos hb k) ↔
      b ^ k ∣ n := by
  rw [residueClassAtDepth_mem_uniformCarryEvent_iff,
    residueAtDepth_eq_zero_iff_pow_dvd]

/-- A carry event occupies exactly one residue class. -/
@[simp] theorem card_uniformCarryEvent
    (N : ℕ) (hN : 0 < N) :
    (uniformCarryEvent N hN).card = 1 := by
  simp [uniformCarryEvent]

/--
Uniform Carry Probability Law.

For every positive positional base and every depth, the probability of a
specified carry congruence class is exactly the carry mass `b^(-k)`.
-/
theorem uniformCarryEvent_probability
    (b k : ℕ) (hb : 0 < b) :
    uniformFiniteProbability
        (uniformCarryEvent (b ^ k) (pow_pos hb k)) =
      criticalMass b k := by
  simp [uniformFiniteProbability, uniformCarryEvent, criticalMass,
    Real.rpow_neg_natCast, Nat.cast_pow, div_eq_mul_inv]

end

end CPFormal.Carry.Positional
