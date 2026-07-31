# CPFormal v0.54.0 — Restricted inverse certificates for positional carry

## Release status

- integrated pull request:
  [#29](https://github.com/thiagomassensini/primos/pull/29);
- audited mathematical-source commit:
  [`8a351323c7476d70e701bed6ab4137d2c5137f2d`](https://github.com/thiagomassensini/primos/commit/8a351323c7476d70e701bed6ab4137d2c5137f2d);
- Lean kernel workflow:
  [30607820730](https://github.com/thiagomassensini/primos/actions/runs/30607820730);
- Lean kernel job: `91083828864`;
- planned annotated tag: `v0.54.0`.

The audited source head completed both the static audit and
`lake build --wfail`. The release workflow after merge remains the
authoritative validation of the exact `main` commit that may be tagged as
`v0.54.0`.

## Parent checkpoint

The parent release is:

```text
v0.53.0
b27f5cfd915a47d49eb6833b259e9f3d47a0fc03
```

That immutable checkpoint certifies the direct causal family:

```text
positional carry
  -> positional addition
  -> multiplication
  -> natural power.
```

It also retains the positional mass `criticalMass b k = b^(-k)`, the
quadratic-amplitude identity, and rigidity at `sigma = 1/2`.

## Scope of v0.54.0

This release adds a separate restricted-inverse layer:

```text
carry <-> borrow

translation by y <-> subtraction of y over Z

dividend <-> quotient-remainder pair

multiplication by d <-> division by d on multiples of d

degree-e power <-> Nat.nthRoot e on perfect powers

base-b power <-> Nat.log b on exact base powers.
```

These relations are paired and branched. They are not a reversed arithmetic
tower.

No new `CausalCompressionSystem` or `CompressionPath` is constructed.
Instead, the release introduces `RestrictedInverseCertificate`, a formal
interface for mutual inverses on explicit source and target domains.

## Restricted inverse interface

For maps

```text
forward : Source -> Target
backward : Target -> Source
```

and predicates

```text
SourceDomain : Source -> Prop
TargetDomain : Target -> Prop,
```

`RestrictedInverseCertificate` stores:

```text
forward_maps_domain
backward_maps_domain
left_roundTrip
right_roundTrip.
```

The domain-preservation obligations prevent either round trip from silently
leaving the region on which it was certified.

This interface is intentionally separate from causal inheritance:

- `CausalCompressionSystem` records directed semantic ancestry;
- `RestrictedInverseCertificate` records a domain-restricted round trip.

Neither structure implies the other.

## Carry and borrow

The release defines:

```text
PositionalCarryStep
PositionalBorrowStep
CarryBorrowReverseCertificate
carryBorrowReverseCertificate.
```

The concrete certificate proves:

- borrow reverses the endpoints of one carry relation;
- carry preserves represented value;
- borrow preserves represented value;
- the positional configurations are distinct.

The common value identity remains:

```text
b * b^k = 1 * b^(k+1).
```

This is a local reverse relation at one scale, not recovery of an arbitrary
normalization history.

## Concrete schoolbook borrow

For lower digits with `x < y`, borrowing one higher unit defines:

```text
borrowedDigit b x y = x + b - y.
```

The release proves the full-column reconstruction:

```text
(high - 1)*b + borrowedDigit b x y
  =
high*b + x - y.
```

Under the canonical digit hypotheses

```text
0 <= x < b
0 <= y < b
x < y,
```

the borrowed result returns to the digit window:

```text
0 <= borrowedDigit b x y < b.
```

The declarations are:

```text
borrowedDigit
positionalBorrow_reconstruction
borrowedDigit_mem_window
BorrowSubtractionCertificate
borrowSubtractionCertificate.
```

This certificate is the explicit bridge between positional borrow and one
schoolbook subtraction column.

## Addition and subtraction with a fixed translation

For fixed `y : ℤ`, the maps are:

```text
addTranslation y x = x + y
subTranslation y x = x - y.
```

The release exposes:

```text
subTranslation_eq_add_inverse
AddSubTranslationCertificate
addSubTranslationCertificate.
```

The certificate proves both unrestricted integer round trips:

```text
(x + y) - y = x
(x - y) + y = x.
```

The retained parameter `y` is essential. A sum alone does not identify its two
original operands.

## Lossless Euclidean split

For a positive divisor `d`:

```text
euclideanSplit d n = (n / d, n % d)
euclideanReconstruct d (q,r) = r + d*q.
```

The canonical target domain is:

```text
IsCanonicalEuclideanPair d (q,r) := r < d.
```

The exact statements are:

```text
euclideanSplit_reconstruction
euclideanSplit_remainder_lt
euclideanSplit_recovers_canonicalPair
EuclideanSplitCertificate
euclideanSplitCertificate.
```

The pair `(q,r)`, together with `d`, reconstructs `n`, and every canonical pair
is recovered after reconstruction. Quotient alone is not a lossless inverse.

## Multiplication and exact division

For a fixed positive `d`:

```text
mulBy d q = d*q
divBy d n = n/d.
```

The exact target domain is:

```text
IsMultipleImage d n := exists q, n = d*q.
```

The release proves and packages:

```text
exactDivision_recovers_factor
MulDivOnMultiplesCertificate
mulDivOnMultiplesCertificate.
```

Division by `d` inverts multiplication by `d` only on the image of multiples.
For arbitrary dividends, the quotient-remainder certificate is the lossless
object.

## Power and `Nat.nthRoot` on perfect powers

For fixed degree:

```text
powerByDegree degree value = value^degree
nthRootByDegree degree value = Nat.nthRoot degree value.
```

The target domain is:

```text
IsPerfectPowerImage degree value.
```

For nonzero degree, the release proves:

```text
nthRoot_exact_on_powers
nthRoot_reconstructs_iff_perfectPower.
```

The restricted inverse is:

```text
PowerNthRootOnPerfectPowersCertificate
powerNthRootOnPerfectPowersCertificate.
```

No exact inverse is asserted outside the perfect-power image, and degree zero
is excluded.

## Base power and `Nat.log` on exact powers

For fixed base:

```text
powerByBase b exponent = b^exponent
floorLogByBase b value = Nat.log b value.
```

The target domain is:

```text
IsExactBasePower b value.
```

For `b > 1`, the release proves and packages:

```text
floorLog_exact_on_basePowers
BasePowerLogOnExactPowersCertificate
basePowerLogOnExactPowersCertificate.
```

Thus:

```text
Nat.log b (b^k) = k,
```

and the opposite round trip is required only for exact powers of `b`.

## Floor logarithm and floor division

For arbitrary positive input, `Nat.log b` is a magnitude coordinate:

```text
b^(Nat.log b n) <= n
n < b^(Nat.log b n + 1).
```

The theorem is:

```text
floorLog_power_window.
```

Whenever `b <= n`, one floor division by the base removes one logarithmic
unit:

```text
Nat.log b n = Nat.log b (n / b) + 1.
```

The theorem is:

```text
floorLog_division_step.
```

This is the precise sense in which `Nat.log` counts floor divisions. It is not
the real analytic logarithm.

## Exact-division depth remains distinct

The release keeps:

```text
repeatedExactDivisionDepth b n = positionalDepth b n.
```

This coordinate measures maximal exact divisibility:

```text
b^k divides n
b^(k+1) does not divide n.
```

The exact statements are:

```text
repeatedExactDivisionDepth_spec
repeatedExactDivisionDepth_factorization_existsUnique.
```

No equality between `Nat.log b n` and `positionalDepth b n` is asserted for a
general natural number. They agree on pure powers `n = b^k` but encode
different information elsewhere.

## Consolidated bundle

The release introduces:

```text
PositionalInverseArithmeticCertificates
positionalInverseArithmeticCertificates.
```

For one base `b > 1`, the bundle exposes:

```text
carry_borrow
borrow_subtraction
addition_subtraction
euclidean_split
multiplication_division
power_nthRoot
power_log
log_power_window
log_division_step
exact_division_depth.
```

Divisor- and degree-dependent constructors retain their assumptions:

- positive divisor;
- nonzero degree;
- nondegenerate base.

The bundle does not turn them into one global inverse operation.

## Carry mass and quadratic rigidity

This release introduces no new mass law.

The following remain inherited results from v0.53.0:

```text
criticalMass b k = b^(-k)
(criticalAmplitude b k)^2 = criticalMass b k
(branchAmplitude b sigma k)^2 = criticalMass b k
  <->
sigma = 1/2.
```

Restricted recovery and scale descent do not alter the uniform carry-event
mass and do not provide an independent derivation of quadratic rigidity.

## Base independence

The consolidated certificate bundle requires only:

```text
1 < b.
```

No primality, oddness, distinguished camera, base `3`, complex parameter,
zeta function, or analytic continuation is used.

## Interpretation boundary

This release does not:

- construct a global inverse tower;
- reverse `CompressionPath`;
- construct a new `CausalCompressionSystem`;
- make subtraction recover two operands from their sum;
- make quotient alone a lossless inverse of multiplication;
- permit exact division by zero;
- make `Nat.nthRoot` exact outside perfect powers;
- permit degree zero in the root round trip;
- make `Nat.log` exact outside powers of the fixed base;
- identify `Nat.log` with the real logarithm;
- identify `Nat.log b n` with `positionalDepth b n` in general;
- assert backward physical or temporal causation;
- prove that every mathematical system has these certificates;
- introduce a new probability, mass, amplitude, or rigidity law;
- add an `axiom`, `sorry`, or `admit` as mathematical evidence.

## Source and documentation

New formal source:

- `CPFormal/Carry/PositionalCarryInverseCausalInheritance.lean`.

Active import surface:

- `CPFormal.lean`.

New documentation:

- `docs/CARRY_INVERSE_CAUSAL_INHERITANCE.md`;
- `docs/RELEASE_0.54.0.md`.

Updated documentation:

- `docs/RESUMO_GERAL_HERANCA_CAUSAL_DO_CARRY.md`;
- `docs/AUDIT.md`;
- `docs/CLAIM_LEDGER.md`;
- `README.md`.

Release automation:

- `.github/workflows/release-v0.54.0.yml`.

The historical files `docs/RELEASE_0.53.0.md` and
`.github/workflows/release-v0.53.0.yml` remain unchanged.

## Integration provenance

| Integrated PR | Audited head | Lean kernel workflow | Lean kernel job | Parent |
|---|---|---|---|---|
| [#29](https://github.com/thiagomassensini/primos/pull/29) | [`8a351323c7476d70e701bed6ab4137d2c5137f2d`](https://github.com/thiagomassensini/primos/commit/8a351323c7476d70e701bed6ab4137d2c5137f2d) | [30607820730](https://github.com/thiagomassensini/primos/actions/runs/30607820730) | `91083828864` | `v0.53.0` |

That run is the source-level kernel certificate. The release workflow after
merge is the authoritative validation of the exact `main` commit tagged as
`v0.54.0`.

## Release verification

Before publishing the annotated tag and GitHub Release, the v0.54.0 release
workflow must execute:

```bash
bash scripts/static_audit.sh

python -m unittest -v \
  experiments/test_c2_real_rotation_operator.py \
  experiments/test_c2_real_rotation_minimal.py

lake build --wfail
```

The Python programs are inherited regression tests. They are not proof
premises of the restricted-inverse Lean certificates.

The workflow must additionally verify that:

- it runs on `refs/heads/main`;
- the checked-out commit equals `GITHUB_SHA`;
- that commit is still the remote `main` head after validation;
- an existing `v0.54.0` reference is an annotated tag;
- an existing tag points exactly to the verified commit;
- an existing GitHub Release is neither draft nor prerelease.

Only after all validations succeed may the workflow create the annotated tag
and publish the GitHub Release.

## Archival and Zenodo

The published, non-draft, non-prerelease `v0.54.0` GitHub Release is the event
consumed by the repository's Zenodo integration.

Zenodo assigns the version DOI after ingesting the immutable release. The
stable concept DOI remains:

```text
10.5281/zenodo.21483474
```
