import CPFormal.Carry.PositionalCarryCausalInheritance

/-!
# Restricted inverse certificates for positional carry arithmetic

This module formalizes the inverse-facing arithmetic surrounding positional
carry without reversing the causal-compression graph from
`PositionalCarryCausalInheritance`.

There is no global inverse tower.  Instead, every round trip states the domain
on which it is valid and retains the data needed for reconstruction:

* carry and borrow are reverse positional relations preserving the same value;
* translation by `y` and subtraction of `y` are mutual inverses over `ℤ`;
* Euclidean splitting retains both quotient and remainder;
* multiplication by `d` is inverted by division only on multiples of `d`;
* degree-`e` power is inverted by `Nat.nthRoot e` only on perfect `e`-th
  powers, with `e ≠ 0`;
* base-`b` power is inverted by `Nat.log b` only on exact powers, with
  `b > 1`.

For arbitrary positive inputs, `Nat.log b` is a floor-logarithmic magnitude
coordinate.  Its recursive division law is recorded, but it is not identified
with `positionalDepth b n`.  The latter counts repeated *exact* divisions and
is a divisibility valuation.

No directed causal path or new causal-system instance is constructed here.
The certificates below are a second direct formal layer rooted in the
carry/borrow geometry, not arrows obtained by running the forward graph
backwards.
-/

namespace CPFormal.Carry.InverseCausal

open CPFormal.Carry.Positional
open CPFormal.Carry.Causal

noncomputable section

/-! ## Generic restricted inverse interface -/

/--
Two maps are mutual inverses on explicitly stated source and target domains.

The domain-preservation fields prevent a round trip from silently leaving the
region in which the inverse statement was certified.
-/
structure RestrictedInverseCertificate
    {Source Target : Type}
    (forward : Source → Target)
    (backward : Target → Source)
    (SourceDomain : Source → Prop)
    (TargetDomain : Target → Prop) : Type where
  forward_maps_domain :
    ∀ {source}, SourceDomain source →
      TargetDomain (forward source)
  backward_maps_domain :
    ∀ {target}, TargetDomain target →
      SourceDomain (backward target)
  left_roundTrip :
    ∀ {source}, SourceDomain source →
      backward (forward source) = source
  right_roundTrip :
    ∀ {target}, TargetDomain target →
      forward (backward target) = target

/-! ## Carry and borrow as reverse value-preserving relations -/

/-- One carry step at the fixed base and depth. -/
def PositionalCarryStep
    (b k : ℕ)
    (source target : PositionalConfiguration) : Prop :=
  source = saturatedCarryConfiguration b k ∧
    target = normalizedCarryConfiguration b k

/-- One borrow step reverses the endpoints of the corresponding carry step. -/
def PositionalBorrowStep
    (b k : ℕ)
    (source target : PositionalConfiguration) : Prop :=
  source = normalizedCarryConfiguration b k ∧
    target = saturatedCarryConfiguration b k

/--
Certificate that borrow is the reverse relation of carry at one positional
scale and that both directions preserve represented value.
-/
structure CarryBorrowReverseCertificate
    (b k : ℕ) : Type where
  reverse_relation :
    ∀ source target,
      PositionalBorrowStep b k source target ↔
        PositionalCarryStep b k target source
  carry_preserves_value :
    ∀ {source target},
      PositionalCarryStep b k source target →
        positionalValue source = positionalValue target
  borrow_preserves_value :
    ∀ {source target},
      PositionalBorrowStep b k source target →
        positionalValue source = positionalValue target
  carry_changes_configuration :
    saturatedCarryConfiguration b k ≠
      normalizedCarryConfiguration b k

/-- Concrete reverse-relation and conservation certificate for carry/borrow. -/
def carryBorrowReverseCertificate
    (b k : ℕ) :
    CarryBorrowReverseCertificate b k where
  reverse_relation := by
    intro source target
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
  carry_preserves_value := by
    rintro source target ⟨rfl, rfl⟩
    exact positionalUnitCarry_preserves_value b k
  borrow_preserves_value := by
    rintro source target ⟨rfl, rfl⟩
    exact (positionalUnitCarry_preserves_value b k).symm
  carry_changes_configuration :=
    positionalUnitCarry_changes_configuration b k

/-! ## The schoolbook borrow step in one subtraction column -/

/--
When the lower digit `x` is smaller than the subtrahend digit `y`, borrowing
one higher-scale unit replaces `x` by `x + b` before subtraction.
-/
def borrowedDigit (b x y : ℤ) : ℤ :=
  x + b - y

/--
Decrementing the high column and adding one base to the lower column preserves
the complete integer subtraction result.
-/
theorem positionalBorrow_reconstruction
    (b high x y : ℤ) :
    (high - 1) * b + borrowedDigit b x y =
      high * b + x - y := by
  simp [borrowedDigit]
  ring

/--
Under the schoolbook digit hypotheses, the borrowed subtraction digit returns
to the canonical window `[0,b)`.
-/
theorem borrowedDigit_mem_window
    (b x y : ℤ)
    (_hb : 0 < b)
    (hx0 : 0 ≤ x)
    (_hy0 : 0 ≤ y)
    (_hxb : x < b)
    (hyb : y < b)
    (hxy : x < y) :
    0 ≤ borrowedDigit b x y ∧
      borrowedDigit b x y < b := by
  constructor <;> simp [borrowedDigit] <;> omega

/--
Certificate for the concrete one-column borrow used by positional
subtraction.
-/
structure BorrowSubtractionCertificate
    (b : ℕ) : Type where
  base_nontrivial : 1 < b
  reconstruction :
    ∀ high x y : ℤ,
      (high - 1) * (b : ℤ) +
          borrowedDigit (b : ℤ) x y =
        high * (b : ℤ) + x - y
  digit_mem_window :
    ∀ x y : ℤ,
      0 ≤ x →
      0 ≤ y →
      x < (b : ℤ) →
      y < (b : ℤ) →
      x < y →
      0 ≤ borrowedDigit (b : ℤ) x y ∧
        borrowedDigit (b : ℤ) x y < (b : ℤ)

/-- Concrete schoolbook borrow certificate for every base `b > 1`. -/
def borrowSubtractionCertificate
    (b : ℕ) (hb : 1 < b) :
    BorrowSubtractionCertificate b where
  base_nontrivial := hb
  reconstruction := fun high x y =>
    positionalBorrow_reconstruction (b : ℤ) high x y
  digit_mem_window := by
    intro x y hx0 hy0 hxb hyb hxy
    have hbInt : (0 : ℤ) < (b : ℤ) := by
      exact_mod_cast (lt_trans Nat.zero_lt_one hb)
    exact
      borrowedDigit_mem_window
        (b : ℤ) x y hbInt hx0 hy0 hxb hyb hxy

/-! ## Addition and subtraction translations over the integers -/

/-- Translation by `y` over `ℤ`. -/
def addTranslation (y : ℤ) (x : ℤ) : ℤ :=
  x + y

/-- Translation by the additive inverse of `y`. -/
def subTranslation (y : ℤ) (x : ℤ) : ℤ :=
  x - y

/-- Integer subtraction is addition of the additive inverse. -/
theorem subTranslation_eq_add_inverse
    (x y : ℤ) :
    subTranslation y x = x + (-y) := by
  simp [subTranslation, sub_eq_add_neg]

/-- The type of the unrestricted translation round-trip certificate. -/
abbrev AddSubTranslationCertificate (y : ℤ) :=
  RestrictedInverseCertificate
    (addTranslation y)
    (subTranslation y)
    (fun _ => True)
    (fun _ => True)

/-- Translation by `y` and subtraction of `y` are mutual inverses over `ℤ`. -/
def addSubTranslationCertificate
    (y : ℤ) :
    AddSubTranslationCertificate y where
  forward_maps_domain := by
    intro source hsource
    trivial
  backward_maps_domain := by
    intro target htarget
    trivial
  left_roundTrip := by
    intro source hsource
    simp [addTranslation, subTranslation]
  right_roundTrip := by
    intro target htarget
    simp [addTranslation, subTranslation]

/-! ## Euclidean split with quotient and remainder retained -/

/-- Canonical Euclidean quotient. -/
def euclideanQuotient (d n : ℕ) : ℕ :=
  n / d

/-- Canonical Euclidean remainder. -/
def euclideanRemainder (d n : ℕ) : ℕ :=
  n % d

/-- Split a dividend into quotient and remainder. -/
def euclideanSplit (d n : ℕ) : ℕ × ℕ :=
  (euclideanQuotient d n, euclideanRemainder d n)

/-- Reconstruct a dividend from a quotient-remainder pair. -/
def euclideanReconstruct (d : ℕ) (qr : ℕ × ℕ) : ℕ :=
  qr.2 + d * qr.1

/-- The canonical target domain for a quotient-remainder pair. -/
def IsCanonicalEuclideanPair
    (d : ℕ) (qr : ℕ × ℕ) : Prop :=
  qr.2 < d

/-- Quotient and remainder reconstruct every dividend for a positive divisor. -/
theorem euclideanSplit_reconstruction
    (d n : ℕ) (hd : 0 < d) :
    euclideanReconstruct d (euclideanSplit d n) = n := by
  exact ((Nat.div_mod_unique hd).1 ⟨rfl, rfl⟩).1

/-- The Euclidean split always lands in the canonical remainder window. -/
theorem euclideanSplit_remainder_lt
    (d n : ℕ) (hd : 0 < d) :
    IsCanonicalEuclideanPair d (euclideanSplit d n) := by
  exact ((Nat.div_mod_unique hd).1 ⟨rfl, rfl⟩).2

/--
A canonical quotient-remainder pair is recovered exactly after
reconstruction.
-/
theorem euclideanSplit_recovers_canonicalPair
    (d : ℕ) (hd : 0 < d) (qr : ℕ × ℕ)
    (hqr : IsCanonicalEuclideanPair d qr) :
    euclideanSplit d (euclideanReconstruct d qr) = qr := by
  have hcanonical :
      euclideanReconstruct d qr / d = qr.1 ∧
        euclideanReconstruct d qr % d = qr.2 :=
    (Nat.div_mod_unique hd).2 ⟨rfl, hqr⟩
  exact Prod.ext hcanonical.1 hcanonical.2

/-- The retained-data round-trip type for Euclidean division by `d`. -/
abbrev EuclideanSplitCertificate (d : ℕ) :=
  RestrictedInverseCertificate
    (euclideanSplit d)
    (euclideanReconstruct d)
    (fun _ => True)
    (IsCanonicalEuclideanPair d)

/-- Euclidean division is invertible when quotient and remainder are retained. -/
def euclideanSplitCertificate
    (d : ℕ) (hd : 0 < d) :
    EuclideanSplitCertificate d where
  forward_maps_domain := by
    intro source hsource
    exact euclideanSplit_remainder_lt d source hd
  backward_maps_domain := by
    intro target htarget
    trivial
  left_roundTrip := by
    intro source hsource
    exact euclideanSplit_reconstruction d source hd
  right_roundTrip := by
    intro target htarget
    exact euclideanSplit_recovers_canonicalPair d hd target htarget

/-! ## Multiplication and exact division on the image of multiples -/

/-- Multiplication by a fixed natural divisor. -/
def mulBy (d q : ℕ) : ℕ :=
  d * q

/-- Natural division by a fixed positive divisor. -/
def divBy (d n : ℕ) : ℕ :=
  n / d

/-- The explicit image predicate for multiplication by `d`. -/
def IsMultipleImage (d n : ℕ) : Prop :=
  ∃ q, n = d * q

/-- Exact division recovers the factor when the divisor is positive. -/
theorem exactDivision_recovers_factor
    (d q : ℕ) (hd : 0 < d) :
    divBy d (mulBy d q) = q := by
  have hcanonical :
      (d * q) / d = q ∧
        (d * q) % d = 0 :=
    (Nat.div_mod_unique hd).2 ⟨by simp, hd⟩
  exact hcanonical.1

/-- Restricted inverse type for multiplication and exact division. -/
abbrev MulDivOnMultiplesCertificate (d : ℕ) :=
  RestrictedInverseCertificate
    (mulBy d)
    (divBy d)
    (fun _ => True)
    (IsMultipleImage d)

/-- Division by `d` inverts multiplication by `d` only on its image. -/
def mulDivOnMultiplesCertificate
    (d : ℕ) (hd : 0 < d) :
    MulDivOnMultiplesCertificate d where
  forward_maps_domain := by
    intro source hsource
    exact ⟨source, rfl⟩
  backward_maps_domain := by
    intro target htarget
    trivial
  left_roundTrip := by
    intro source hsource
    exact exactDivision_recovers_factor d source hd
  right_roundTrip := by
    rintro target ⟨factor, rfl⟩
    change d * ((d * factor) / d) = d * factor
    rw [show (d * factor) / d = factor from
      exactDivision_recovers_factor d factor hd]

/-! ## Degree power and natural nth root on perfect powers -/

/-- Raise a natural number to a fixed degree. -/
def powerByDegree (degree value : ℕ) : ℕ :=
  value ^ degree

/-- Natural floor `degree`-th root. -/
def nthRootByDegree (degree value : ℕ) : ℕ :=
  Nat.nthRoot degree value

/-- The explicit image predicate for fixed-degree powers. -/
def IsPerfectPowerImage (degree value : ℕ) : Prop :=
  ∃ root, root ^ degree = value

/-- `Nat.nthRoot` exactly recovers the source of a nonzero-degree power. -/
theorem nthRoot_exact_on_powers
    (degree value : ℕ) (hdegree : degree ≠ 0) :
    nthRootByDegree degree (powerByDegree degree value) =
      value := by
  simpa [nthRootByDegree, powerByDegree] using
    Nat.nthRoot_pow hdegree value

/--
A perfect-power witness is equivalent to exact reconstruction by
`Nat.nthRoot`.
-/
theorem nthRoot_reconstructs_iff_perfectPower
    (degree value : ℕ) (hdegree : degree ≠ 0) :
    IsPerfectPowerImage degree value ↔
      powerByDegree degree (nthRootByDegree degree value) = value := by
  constructor
  · rintro ⟨root, rfl⟩
    simp [powerByDegree, nthRootByDegree,
      Nat.nthRoot_pow hdegree]
  · intro hreconstruct
    exact
      ⟨nthRootByDegree degree value,
        by simpa [powerByDegree] using hreconstruct⟩

/-- Restricted inverse type for a nonzero-degree power and natural nth root. -/
abbrev PowerNthRootOnPerfectPowersCertificate
    (degree : ℕ) :=
  RestrictedInverseCertificate
    (powerByDegree degree)
    (nthRootByDegree degree)
    (fun _ => True)
    (IsPerfectPowerImage degree)

/-- Power and `Nat.nthRoot` are mutual inverses on perfect powers only. -/
def powerNthRootOnPerfectPowersCertificate
    (degree : ℕ) (hdegree : degree ≠ 0) :
    PowerNthRootOnPerfectPowersCertificate degree where
  forward_maps_domain := by
    intro source hsource
    exact ⟨source, rfl⟩
  backward_maps_domain := by
    intro target htarget
    trivial
  left_roundTrip := by
    intro source hsource
    exact nthRoot_exact_on_powers degree source hdegree
  right_roundTrip := by
    intro target htarget
    exact
      (nthRoot_reconstructs_iff_perfectPower
        degree target hdegree).mp htarget

/-! ## Base power and natural logarithm on exact powers -/

/-- Raise a fixed positional base to a natural exponent. -/
def powerByBase (b exponent : ℕ) : ℕ :=
  b ^ exponent

/-- Natural floor logarithm in a fixed base. -/
def floorLogByBase (b value : ℕ) : ℕ :=
  Nat.log b value

/-- The explicit image predicate for powers of the fixed base. -/
def IsExactBasePower (b value : ℕ) : Prop :=
  ∃ exponent, b ^ exponent = value

/-- Natural floor logarithm recovers the exponent on exact base powers. -/
theorem floorLog_exact_on_basePowers
    (b exponent : ℕ) (hb : 1 < b) :
    floorLogByBase b (powerByBase b exponent) =
      exponent := by
  simpa [floorLogByBase, powerByBase] using
    Nat.log_pow hb exponent

/-- Restricted inverse type for fixed-base power and logarithm. -/
abbrev BasePowerLogOnExactPowersCertificate
    (b : ℕ) :=
  RestrictedInverseCertificate
    (powerByBase b)
    (floorLogByBase b)
    (fun _ => True)
    (IsExactBasePower b)

/-- Base power and `Nat.log` are mutual inverses on exact powers only. -/
def basePowerLogOnExactPowersCertificate
    (b : ℕ) (hb : 1 < b) :
    BasePowerLogOnExactPowersCertificate b where
  forward_maps_domain := by
    intro source hsource
    exact ⟨source, rfl⟩
  backward_maps_domain := by
    intro target htarget
    trivial
  left_roundTrip := by
    intro source hsource
    exact floorLog_exact_on_basePowers b source hb
  right_roundTrip := by
    rintro target ⟨exponent, rfl⟩
    change b ^ Nat.log b (b ^ exponent) = b ^ exponent
    rw [Nat.log_pow hb exponent]

/-! ## Floor logarithm as a semantic count of floor divisions -/

/--
For an arbitrary positive input, `Nat.log b` records the base-power magnitude
window rather than a general inverse of exponentiation.
-/
theorem floorLog_power_window
    (b value : ℕ) (hb : 1 < b) (hvalue : value ≠ 0) :
    b ^ floorLogByBase b value ≤ value ∧
      value < b ^ (floorLogByBase b value + 1) := by
  constructor
  · simpa [floorLogByBase] using
      Nat.pow_log_le_self b hvalue
  · simpa [floorLogByBase, Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self hb value

/--
Whenever `b ≤ value`, one floor division by `b` removes exactly one unit from
the floor-logarithmic coordinate.
-/
theorem floorLog_division_step
    (b value : ℕ) (hb : 1 < b) (hbv : b ≤ value) :
    floorLogByBase b value =
      floorLogByBase b (value / b) + 1 := by
  simpa [floorLogByBase] using
    Nat.log_of_one_lt_of_le hb hbv

/-! ## Repeated exact division remains a distinct valuation coordinate -/

/-- Maximal count of repeated exact divisions by the positional base. -/
def repeatedExactDivisionDepth (b value : ℕ) : ℕ :=
  positionalDepth b value

/-- Exact-division depth records maximal power divisibility. -/
theorem repeatedExactDivisionDepth_spec
    (b value : ℕ) (hb : 1 < b) (hvalue : 0 < value) :
    b ^ repeatedExactDivisionDepth b value ∣ value ∧
      ¬b ^ (repeatedExactDivisionDepth b value + 1) ∣ value := by
  simpa [repeatedExactDivisionDepth] using
    positionalDepth_spec b value hb hvalue

/--
The core remaining after all exact base divisions exists uniquely and is not
divisible by the base.
-/
theorem repeatedExactDivisionDepth_factorization_existsUnique
    (b value : ℕ) (hb : 1 < b) (hvalue : 0 < value) :
    ∃! core : ℕ,
      value =
          b ^ repeatedExactDivisionDepth b value * core ∧
        ¬b ∣ core := by
  simpa [repeatedExactDivisionDepth] using
    positionalDepth_factorization_existsUnique
      b value hb hvalue

/-! ## Consolidated certificate bundle -/

/--
All restricted inverse certificates attached to one nondegenerate positional
base.

The bundle exposes constructors for divisor- and degree-dependent certificates
instead of pretending that division, roots, or logarithms are total global
inverses.
-/
structure PositionalInverseArithmeticCertificates
    (b : ℕ) : Type where
  base_nontrivial : 1 < b
  carry_borrow :
    ∀ k,
      CarryBorrowReverseCertificate b k
  borrow_subtraction :
    BorrowSubtractionCertificate b
  addition_subtraction :
    ∀ y : ℤ,
      AddSubTranslationCertificate y
  euclidean_split :
    ∀ d, 0 < d →
      EuclideanSplitCertificate d
  multiplication_division :
    ∀ d, 0 < d →
      MulDivOnMultiplesCertificate d
  power_nthRoot :
    ∀ degree, degree ≠ 0 →
      PowerNthRootOnPerfectPowersCertificate degree
  power_log :
    BasePowerLogOnExactPowersCertificate b
  log_power_window :
    ∀ value, value ≠ 0 →
      b ^ floorLogByBase b value ≤ value ∧
        value < b ^ (floorLogByBase b value + 1)
  log_division_step :
    ∀ value, b ≤ value →
      floorLogByBase b value =
        floorLogByBase b (value / b) + 1
  exact_division_depth :
    ∀ value, 0 < value →
      b ^ repeatedExactDivisionDepth b value ∣ value ∧
        ¬b ^ (repeatedExactDivisionDepth b value + 1) ∣ value

/-- Concrete bundle of every restricted inverse certificate in this module. -/
def positionalInverseArithmeticCertificates
    (b : ℕ) (hb : 1 < b) :
    PositionalInverseArithmeticCertificates b where
  base_nontrivial := hb
  carry_borrow := carryBorrowReverseCertificate b
  borrow_subtraction := borrowSubtractionCertificate b hb
  addition_subtraction := addSubTranslationCertificate
  euclidean_split := euclideanSplitCertificate
  multiplication_division := mulDivOnMultiplesCertificate
  power_nthRoot := powerNthRootOnPerfectPowersCertificate
  power_log := basePowerLogOnExactPowersCertificate b hb
  log_power_window := fun value hvalue =>
    floorLog_power_window b value hb hvalue
  log_division_step := fun value hbv =>
    floorLog_division_step b value hb hbv
  exact_division_depth := fun value hvalue =>
    repeatedExactDivisionDepth_spec b value hb hvalue

end

end CPFormal.Carry.InverseCausal
