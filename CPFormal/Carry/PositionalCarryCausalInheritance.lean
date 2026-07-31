import CPFormal.Logic.CausalCompression
import CPFormal.Carry.PositionalDecomposition
import CPFormal.Carry.UniformCarryProbability
import CPFormal.Analytic.CpPositionalCarryQuadraticRigidity

/-!
# Causal inheritance of positional carry through arithmetic

This module gives a concrete, certificate-bearing realization of the tower

```text
positional carry -> addition -> multiplication -> natural power.
```

The first edge is not declared by name alone.  It stores the Euclidean
decomposition proving that a positional sum is exactly its output digit plus
the base times its carry coordinate.  The next edges store the recursive laws
that multiplication packages iterated addition and natural power packages
iterated multiplication.

The module also separates three claims that must not be conflated:

1. a carry normalization changes positional coordinates while preserving
   represented value;
2. higher arithmetic carriers inherit the carry pattern through certified
   operational compression;
3. the uniform carry event has mass `b^(-k)`, whose quadratic amplitude is
   rigidly realized at exponent `1/2`.

No primality, oddness, distinguished camera, complex parameter, or external
postulate is used.  The final result concerns the explicitly certified positional
arithmetic tower; it does not quantify over every possible mathematical
structure.
-/

namespace CPFormal.Carry.Causal

open CPFormal.Logic
open CPFormal.Carry.Positional
open CPFormal.Carry.Cp
open CPFormal.Analytic.Cp

noncomputable section

/-! ## Carry as a value-preserving change of positional scale -/

/--
A raw positional configuration.  A coefficient equal to the base represents
a saturated pre-normalization state rather than a canonical digit.
-/
structure PositionalConfiguration where
  base : ℕ
  coefficient : ℕ
  depth : ℕ
  deriving DecidableEq, Repr

/-- Numerical value represented by a coefficient at a positional depth. -/
def positionalValue (state : PositionalConfiguration) : ℕ :=
  state.coefficient * state.base ^ state.depth

/-- `b` lower-scale units immediately before one unit of carry is emitted. -/
def saturatedCarryConfiguration
    (b k : ℕ) : PositionalConfiguration :=
  ⟨b, b, k⟩

/-- The normalized single unit at the next positional depth. -/
def normalizedCarryConfiguration
    (b k : ℕ) : PositionalConfiguration :=
  ⟨b, 1, k + 1⟩

/--
One unit of carry changes coordinates but preserves represented value:
`b * b^k = b^(k+1)`.
-/
theorem positionalUnitCarry_preserves_value
    (b k : ℕ) :
    positionalValue (saturatedCarryConfiguration b k) =
      positionalValue (normalizedCarryConfiguration b k) := by
  simp [positionalValue, saturatedCarryConfiguration,
    normalizedCarryConfiguration, pow_succ, Nat.mul_comm]

/-- Carry normalization is a genuine, non-identity coordinate transition. -/
theorem positionalUnitCarry_changes_configuration
    (b k : ℕ) :
    saturatedCarryConfiguration b k ≠
      normalizedCarryConfiguration b k := by
  intro h
  have hdepth :
      k = k + 1 :=
    congrArg PositionalConfiguration.depth h
  omega

/-! ## Certified carry in positional addition -/

/-- Common observable type for binary arithmetic carriers. -/
abbrev NatBinaryOperation := ℕ × ℕ → ℕ

/-- Quotient emitted from the units column of a base-`b` sum. -/
def positionalAdditionCarry
    (b : ℕ) : NatBinaryOperation :=
  fun input =>
    quotientAtDepth b 1 (input.1 + input.2)

/-- Canonical output digit left in the units column of a base-`b` sum. -/
def positionalAdditionDigit
    (b : ℕ) : NatBinaryOperation :=
  fun input =>
    residueAtDepth b 1 (input.1 + input.2)

/-- Ordinary addition viewed as a binary natural-number observable. -/
def additionEval : NatBinaryOperation :=
  fun input => input.1 + input.2

/-- Ordinary multiplication viewed as a binary natural-number observable. -/
def multiplicationEval : NatBinaryOperation :=
  fun input => input.1 * input.2

/-- Natural exponentiation viewed as a binary natural-number observable. -/
def naturalPowerEval : NatBinaryOperation :=
  fun input => input.1 ^ input.2

/--
Exact units-column reconstruction of positional addition.

The carry coordinate transports value; it does not add a new value to the
sum.
-/
theorem positionalAddition_reconstruction
    (b : ℕ) (hb : 0 < b) (input : ℕ × ℕ) :
    additionEval input =
      positionalAdditionDigit b input +
        b * positionalAdditionCarry b input := by
  have hdecomposition :=
    (positionalDecompositionAtDepth
      b 1 (input.1 + input.2) hb).1
  simpa [additionEval, positionalAdditionDigit,
    positionalAdditionCarry] using hdecomposition.symm

/--
The quotient carry is positive exactly when the units-column sum saturates
the base.
-/
theorem positionalAdditionCarry_pos_iff_saturated
    (b : ℕ) (hb : 0 < b) (input : ℕ × ℕ) :
    0 < positionalAdditionCarry b input ↔
      b ≤ input.1 + input.2 := by
  constructor
  · intro hcarry
    by_contra hnot
    have hlt : input.1 + input.2 < b :=
      Nat.lt_of_not_ge hnot
    have hzero :
        positionalAdditionCarry b input = 0 := by
      simp [positionalAdditionCarry, quotientAtDepth,
        Nat.div_eq_of_lt hlt]
    exact (Nat.ne_of_gt hcarry) hzero
  · intro hsaturated
    simpa [positionalAdditionCarry, quotientAtDepth] using
      Nat.div_pos hsaturated hb

/--
Semantic certificate that a target addition observable is reconstructed from
a positional digit and a carry observable.
-/
structure PositionalCarryCompression
    (b : ℕ)
    (addition carry : NatBinaryOperation) where
  digit : NatBinaryOperation
  digit_lt_base :
    ∀ input, digit input < b
  reconstruction :
    ∀ input,
      addition input = digit input + b * carry input

/-- Concrete carry-to-addition certificate in every nondegenerate base. -/
def carryToAdditionCertificate
    (b : ℕ) (hb : 1 < b) :
    PositionalCarryCompression
      b additionEval (positionalAdditionCarry b) where
  digit := positionalAdditionDigit b
  digit_lt_base := by
    intro input
    have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
    have hbound :=
      (positionalDecompositionAtDepth
        b 1 (input.1 + input.2) hb0).2
    simpa [positionalAdditionDigit] using hbound
  reconstruction := by
    intro input
    exact positionalAddition_reconstruction
      b (lt_trans Nat.zero_lt_one hb) input

/-! ## Multiplication and power as certified operational compressions -/

/--
An operation `higher` packages iteration of `lower`, starting at `seed`.
-/
structure IterationCompression
    (lower higher : NatBinaryOperation)
    (seed : ℕ) : Type where
  zero :
    ∀ a, higher (a, 0) = seed
  succ :
    ∀ a n,
      higher (a, n + 1) =
        lower (higher (a, n), a)

/-- Multiplication packages iteration of addition. -/
def additionToMultiplicationCertificate :
    IterationCompression additionEval multiplicationEval 0 where
  zero := by
    intro a
    simp [multiplicationEval]
  succ := by
    intro a n
    simp [multiplicationEval, additionEval, Nat.mul_succ]

/-- Natural power packages iteration of multiplication. -/
def multiplicationToPowerCertificate :
    IterationCompression multiplicationEval naturalPowerEval 1 where
  zero := by
    intro a
    simp [naturalPowerEval]
  succ := by
    intro a n
    simp [naturalPowerEval, multiplicationEval, pow_succ]

/-! ## Concrete causal-compression system -/

/-- The single causal pattern tracked in this arithmetic model. -/
inductive CarryPattern where
  | positionalCarry
  deriving DecidableEq, Repr

/-- Successive carriers of the positional arithmetic tower. -/
inductive ArithmeticCarrier where
  | carryNormalization
  | positionalAddition
  | multiplication
  | naturalPower
  deriving DecidableEq, Repr

/-- The carry pattern is directly instantiated only at its primitive carrier. -/
def ArithmeticPrimitiveWitness :
    ArithmeticCarrier → CarryPattern → Type
  | .carryNormalization, .positionalCarry => PUnit
  | _, _ => Empty

/--
Every direct arithmetic edge contains its semantic certificate.  All other
edges are empty rather than being silently postulated.
-/
def ArithmeticCompressionWitness
    (b : ℕ) :
    ArithmeticCarrier → ArithmeticCarrier → Type
  | .carryNormalization, .positionalAddition =>
      PositionalCarryCompression
        b additionEval (positionalAdditionCarry b)
  | .positionalAddition, .multiplication =>
      IterationCompression
        additionEval multiplicationEval 0
  | .multiplication, .naturalPower =>
      IterationCompression
        multiplicationEval naturalPowerEval 1
  | _, _ => Empty

/--
Carry is visible in normalization and schoolbook positional addition.  It is
hidden by the compressed multiplication and power notation.
-/
def arithmeticExplicitlyDisplays :
    ArithmeticCarrier → CarryPattern → Prop
  | .carryNormalization, .positionalCarry => True
  | .positionalAddition, .positionalCarry => True
  | _, _ => False

/-- Evaluation of every carrier in the arithmetic tower. -/
def arithmeticEval
    (b : ℕ) :
    ArithmeticCarrier → NatBinaryOperation
  | .carryNormalization => positionalAdditionCarry b
  | .positionalAddition => additionEval
  | .multiplication => multiplicationEval
  | .naturalPower => naturalPowerEval

/-- Certificate-bearing positional arithmetic as a causal compression system. -/
def positionalArithmeticSystem
    (b : ℕ) : CausalCompressionSystem where
  Pattern := CarryPattern
  Carrier := ArithmeticCarrier
  Input := ℕ × ℕ
  Output := ℕ
  eval := arithmeticEval b
  PrimitiveWitness := ArithmeticPrimitiveWitness
  CompressionWitness := ArithmeticCompressionWitness b
  ExplicitlyDisplays := arithmeticExplicitlyDisplays

/-- Certified path from carry normalization to positional addition. -/
def carryToAdditionPath
    (b : ℕ) (hb : 1 < b) :
    (positionalArithmeticSystem b).CompressionPath
      ArithmeticCarrier.carryNormalization
      ArithmeticCarrier.positionalAddition := by
  apply CausalCompressionSystem.CompressionPath.tail
  · exact
      CausalCompressionSystem.CompressionPath.refl
        ArithmeticCarrier.carryNormalization
  · exact ⟨carryToAdditionCertificate b hb⟩

/-- Certified path from carry normalization to multiplication. -/
def carryToMultiplicationPath
    (b : ℕ) (hb : 1 < b) :
    (positionalArithmeticSystem b).CompressionPath
      ArithmeticCarrier.carryNormalization
      ArithmeticCarrier.multiplication := by
  apply CausalCompressionSystem.CompressionPath.tail
  · exact carryToAdditionPath b hb
  · exact ⟨additionToMultiplicationCertificate⟩

/-- Certified path from carry normalization to natural power. -/
def carryToNaturalPowerPath
    (b : ℕ) (hb : 1 < b) :
    (positionalArithmeticSystem b).CompressionPath
      ArithmeticCarrier.carryNormalization
      ArithmeticCarrier.naturalPower := by
  apply CausalCompressionSystem.CompressionPath.tail
  · exact carryToMultiplicationPath b hb
  · exact ⟨multiplicationToPowerCertificate⟩

/-- Primitive carry is inherited by the addition carrier. -/
theorem carry_reinstantiated_in_addition
    (b : ℕ) (hb : 1 < b) :
    (positionalArithmeticSystem b).Reinstantiates
      CarryPattern.positionalCarry
      ArithmeticCarrier.positionalAddition := by
  exact
    ⟨ArithmeticCarrier.carryNormalization, ⟨PUnit.unit⟩,
      carryToAdditionPath b hb⟩

/-- Primitive carry is inherited by the multiplication carrier. -/
theorem carry_reinstantiated_in_multiplication
    (b : ℕ) (hb : 1 < b) :
    (positionalArithmeticSystem b).Reinstantiates
      CarryPattern.positionalCarry
      ArithmeticCarrier.multiplication := by
  exact
    ⟨ArithmeticCarrier.carryNormalization, ⟨PUnit.unit⟩,
      carryToMultiplicationPath b hb⟩

/-- Primitive carry is inherited by the natural-power carrier. -/
theorem carry_reinstantiated_in_naturalPower
    (b : ℕ) (hb : 1 < b) :
    (positionalArithmeticSystem b).Reinstantiates
      CarryPattern.positionalCarry
      ArithmeticCarrier.naturalPower := by
  exact
    ⟨ArithmeticCarrier.carryNormalization, ⟨PUnit.unit⟩,
      carryToNaturalPowerPath b hb⟩

/-- Carry normalization has a nonconstant quotient observable. -/
theorem carryNormalization_operationallyNontrivial
    (b : ℕ) (hb : 1 < b) :
    (positionalArithmeticSystem b).OperationallyNontrivial
      ArithmeticCarrier.carryNormalization := by
  refine ⟨(0, 0), (b, 0), ?_⟩
  change
    positionalAdditionCarry b (0, 0) ≠
      positionalAdditionCarry b (b, 0)
  have hzero :
      positionalAdditionCarry b (0, 0) = 0 := by
    simp [positionalAdditionCarry, quotientAtDepth]
  rw [hzero]
  exact ne_of_lt
    ((positionalAdditionCarry_pos_iff_saturated
      b (lt_trans Nat.zero_lt_one hb) (b, 0)).2 (by simp))

/-- Addition has a nonconstant observable action. -/
theorem addition_operationallyNontrivial
    (b : ℕ) :
    (positionalArithmeticSystem b).OperationallyNontrivial
      ArithmeticCarrier.positionalAddition := by
  refine ⟨(0, 0), (1, 0), ?_⟩
  change additionEval (0, 0) ≠ additionEval (1, 0)
  norm_num [additionEval]

/-- Multiplication has a nonconstant observable action. -/
theorem multiplication_operationallyNontrivial
    (b : ℕ) :
    (positionalArithmeticSystem b).OperationallyNontrivial
      ArithmeticCarrier.multiplication := by
  refine ⟨(0, 1), (1, 1), ?_⟩
  change multiplicationEval (0, 1) ≠ multiplicationEval (1, 1)
  norm_num [multiplicationEval]

/-- Natural power has a nonconstant observable action. -/
theorem naturalPower_operationallyNontrivial
    (b : ℕ) :
    (positionalArithmeticSystem b).OperationallyNontrivial
      ArithmeticCarrier.naturalPower := by
  refine ⟨(0, 1), (1, 1), ?_⟩
  change naturalPowerEval (0, 1) ≠ naturalPowerEval (1, 1)
  norm_num [naturalPowerEval]

/-- Every carrier in the certified tower inherits the positional-carry pattern. -/
theorem positionalArithmetic_generatedByCarry
    (b : ℕ) (hb : 1 < b) :
    (positionalArithmeticSystem b).GeneratedBy
      CarryPattern.positionalCarry := by
  intro carrier
  cases carrier with
  | carryNormalization =>
      exact
        ⟨ArithmeticCarrier.carryNormalization, ⟨PUnit.unit⟩,
          CausalCompressionSystem.CompressionPath.refl
            ArithmeticCarrier.carryNormalization⟩
  | positionalAddition =>
      exact carry_reinstantiated_in_addition b hb
  | multiplication =>
      exact carry_reinstantiated_in_multiplication b hb
  | naturalPower =>
      exact carry_reinstantiated_in_naturalPower b hb

/-- Every carrier in the certified tower is observably nonconstant. -/
theorem positionalArithmetic_operationallyNontrivial
    (b : ℕ) (hb : 1 < b) :
    ∀ carrier,
      (positionalArithmeticSystem b).OperationallyNontrivial carrier := by
  intro carrier
  cases carrier with
  | carryNormalization =>
      exact carryNormalization_operationallyNontrivial b hb
  | positionalAddition =>
      exact addition_operationallyNontrivial b
  | multiplication =>
      exact multiplication_operationallyNontrivial b
  | naturalPower =>
      exact naturalPower_operationallyNontrivial b

/--
Main causal-inheritance theorem.

In every nondegenerate base, carry is causally present throughout the
explicitly certified arithmetic tower.
-/
theorem positionalCarry_causallyPresent_through_arithmeticTower
    (b : ℕ) (hb : 1 < b) :
    ∀ carrier,
      (positionalArithmeticSystem b).CausallyPresentIn
        CarryPattern.positionalCarry carrier :=
  (positionalArithmeticSystem b).causallyPresentIn_all_of_generatedBy
    (positionalArithmetic_generatedByCarry b hb)
    (positionalArithmetic_operationallyNontrivial b hb)

/-- Multiplication hides the carry symbol but retains its causal ancestry. -/
theorem positionalCarry_hiddenButCausallyPresent_in_multiplication
    (b : ℕ) (hb : 1 < b) :
    (positionalArithmeticSystem b).HiddenButCausallyPresentIn
      CarryPattern.positionalCarry
      ArithmeticCarrier.multiplication := by
  refine
    ⟨positionalCarry_causallyPresent_through_arithmeticTower
      b hb ArithmeticCarrier.multiplication, ?_⟩
  simp [positionalArithmeticSystem, arithmeticExplicitlyDisplays]

/-- Natural power hides the carry symbol but retains its causal ancestry. -/
theorem positionalCarry_hiddenButCausallyPresent_in_naturalPower
    (b : ℕ) (hb : 1 < b) :
    (positionalArithmeticSystem b).HiddenButCausallyPresentIn
      CarryPattern.positionalCarry
      ArithmeticCarrier.naturalPower := by
  refine
    ⟨positionalCarry_causallyPresent_through_arithmeticTower
      b hb ArithmeticCarrier.naturalPower, ?_⟩
  simp [positionalArithmeticSystem, arithmeticExplicitlyDisplays]

/-! ## Existing mass and quadratic rigidity carried by the same geometry -/

/--
The carry event already owns its mass, and the critical amplitude already
realizes that mass quadratically.  Neither quantity is introduced by a later
operator.
-/
theorem positionalCarry_mass_and_quadraticAmplitude
    (b k : ℕ) (hb : 1 < b) :
    uniformFiniteProbability
        (uniformCarryEvent
          (b ^ k)
          (pow_pos (lt_trans Nat.zero_lt_one hb) k)) =
        criticalMass b k ∧
      (criticalAmplitude b k) ^ 2 = criticalMass b k := by
  exact
    ⟨uniformCarryEvent_probability
      b k (lt_trans Nat.zero_lt_one hb),
      criticalAmplitude_sq_eq_mass b k⟩

/--
Consolidated certificate for the user's structural observation:

* carry changes scale without changing represented value;
* its pattern remains causally present through natural power;
* its finite event mass is the already defined `b^(-k)`;
* quadratic realization selects the unique exponent `1/2`.
-/
theorem positionalCarry_causalInheritance_mass_and_rigidity
    (b k : ℕ) (hb : 1 < b) (hk : 0 < k) (sigma : ℝ) :
    (positionalArithmeticSystem b).HiddenButCausallyPresentIn
        CarryPattern.positionalCarry
        ArithmeticCarrier.naturalPower ∧
      positionalValue (saturatedCarryConfiguration b k) =
        positionalValue (normalizedCarryConfiguration b k) ∧
      uniformFiniteProbability
          (uniformCarryEvent
            (b ^ k)
            (pow_pos (lt_trans Nat.zero_lt_one hb) k)) =
        criticalMass b k ∧
      (criticalAmplitude b k) ^ 2 = criticalMass b k ∧
      ((branchAmplitude b sigma k) ^ 2 = criticalMass b k ↔
        sigma = (1 : ℝ) / 2) := by
  refine
    ⟨positionalCarry_hiddenButCausallyPresent_in_naturalPower b hb,
      positionalUnitCarry_preserves_value b k, ?_, ?_, ?_⟩
  · exact
      (positionalCarry_mass_and_quadraticAmplitude b k hb).1
  · exact
      (positionalCarry_mass_and_quadraticAmplitude b k hb).2
  · exact
      branchAmplitude_sq_eq_criticalMass_iff_of_one_lt
        b k hb hk sigma

end

end CPFormal.Carry.Causal
