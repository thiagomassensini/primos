# Nota de correção semântica

> Este documento registra historicamente a `v0.52.0`. A API atual não exige
> compatibilidade de massa para que um fechamento seja chamado de zero nativo.
> Consulte `docs/NATIVE_ZERO_SEMANTICS_CORRECTION.md`.

## CPFormal v0.52.0 — registro histórico

## Scope

This release consolidates four independently audited layers:

1. canonical positional decomposition, uniform carry probability, and the
   quadratic-domain crosswalk for arbitrary positional bases;
2. the exact raw-boundary crosswalk between the primitive real camera and the
   scalar Genuine continuation;
3. concrete C2 support nondegeneracy, the finite-atlas Pythagorean ledger, and
   the strictly contractive native `G_pre` lift;
4. the finite empirical operator implemented entirely with real rotation
   matrices over `R^2`.

The Lean modules and the numerical programs have different evidentiary roles.
The former are kernel-checked theorems. The latter are finite reproducible
experiments and are not used as proof premises.

## Canonical positional decomposition

For every positive base `b`, depth `k`, and natural number `n`, the kernel
records the canonical quotient and residue

```text
quotientAtDepth b k n = n / b^k
residueAtDepth  b k n = n % b^k
```

and proves

```text
residueAtDepth b k n + b^k * quotientAtDepth b k n = n
residueAtDepth b k n < b^k.
```

The pair is unique in the canonical residue window.

For every `b > 1` and `n > 0`, `positionalDepth b n` is the maximal
exponent whose base power divides `n`, and there is a unique remaining core
`m` such that

```text
n = b^(positionalDepth b n) * m
not (b divides m).
```

These statements remain valid for composite bases and introduce no primality
hypothesis.

## Uniform Carry Probability Law

At depth `k`, the residue space contains exactly `b^k` equiprobable
classes. The residual-zero carry event is a singleton, so the kernel proves

```text
uniformFiniteProbability (uniformCarryEvent (b^k)) =
  criticalMass b k.
```

Thus the finite uniform probability of that event is exactly `b^(-k)`.

## Quadratic Domain Crosswalk

For every nondegenerate positional base `b > 1`, every real exponent
`sigma`, and every real rotation time `time`, the kernel proves

```text
PositionalCarryMassCompatible b sigma
  <->
NativeCarryRealPlaneMassCompatible sigma time.
```

This is equality of admissible quadratic exponent domains. Both sides select
`sigma = 1/2`.

It does not assert the false pointwise identity

```text
b^(-k) = n^(-1).
```

Carry mass by positional depth and inverse-integer state energy remain
different pointwise quantities.

## Primitive real camera and scalar continuation

For a positive integer sample, packaging the two real rotating coordinates
into one complex coordinate gives the literal Dirichlet monomial at

```text
nativeCarryRealPlaneParameter sigma time = sigma + time * I.
```

The same identity holds for every finite chart of every odd prime camera.

Passing through the audited finite-chart limit gives, for every parameter
`s` in the open Genuine strip,

```text
NativeCarryRealOperatorBoundaryClosesAt 3 s.re s.im
  <->
genuineContinuation s = 0.
```

Complex notation therefore packages two real coordinates without changing the
raw camera-three boundary-closing set.

This theorem concerns raw boundary closure. It does not replace the native
operator predicate

```text
IsNativeCarryRealOperatorZero camera sigma time,
```

which also retains the quadratic mass-domain condition.

## Deduplicated reconstruction guardrails

Historical PR #12 overlapped with the canonical sample, finite-chart, and
raw-boundary crosswalk integrated by PR #19. Those declarations were not
duplicated.

Only the two logically distinct conditional guardrails were retained by
PR #21:

```text
genuineContinuation_ne_zero_off_critical_of_quadratic_mass_reconstruction

genuineContinuation_ne_zero_off_critical_of_precompression_reconstruction
```

They state that off-critical scalar nonvanishing follows when a closing raw
boundary is known to reconstruct, respectively,

1. the native quadratic mass domain; or
2. a retained pre-compression witness.

Neither theorem derives that reconstruction premise from scalar closure alone.

## Concrete C2 support nondegeneracy

Every finite odd-core branch mass is strictly below its geometric limit:

```text
oddCoreBranchMass K < 1/2.
```

Consequently, the sum of the two finite branches is strictly below one:

```text
oddCoreTruncatedMass cutoff m < 1.
```

The concrete four-scale defect is therefore strictly positive, in both
rational and real form, and the connected cofinal mass scale never vanishes:

```text
0 < c2OddCoreFourScaleDefect M m
0 < c2OddCoreFourScaleDefectReal M m
c2OddCoreCofinalMassScale M p q != 0.
```

This removes the former manual nondegeneracy premise from the normalized C2
`G_pre` readout, its cofinal limit, and the semiprime log-atom crosswalk.

It does not identify the concrete odd-core defect with `cpRadialDifference`
and does not supply a scalar-zero-to-Hilbert-energy implication.

## Pythagorean camera ledger and strict contraction

For any common realization of the active finite camera readouts, the canonical
provenance state is its orthogonal projection onto the active centered-carry
directions. The release proves the exact ledger

```text
total energy =
  active canonical camera energy +
  unused orthogonal residual energy.
```

The residual is retained explicitly. The theorem does not construct a common
global realization merely from a scalar zero.

A native `G_pre` tower state `x` is mapped to one global centered-carry
state whose prime-camera coordinates read back the first native tower moments
exactly. The prime-index majorant has total mass

```text
sum majorant = 11/12,
```

and the constructed global state satisfies

```text
‖nativeGprePrimeCarryDefectState x‖^2
  <= (11/12) * ‖x‖^2.
```

The construction remains conditional on the source state having the required
moments. It does not construct such a source state at every scalar Genuine
zero. The existing guardrail remains explicit:

```text
GenuineZerosAdmitGlobalCenteredCarryReadoutState
  <->
GenuineStrongNonvanishingInStrip.
```

## Finite real-rotation empirical operator

The release includes two executable NumPy programs:

- `experiments/c2_real_rotation_operator.py`;
- `experiments/c2_real_rotation_minimal.py`.

The empirical state is stored only in `R^2`:

```text
psi_t(n) = (1 / sqrt(n)) * R(-t log n) * e1.
```

The complete scanner provides exact decimal grids, selectable cameras, CPU
multiprocessing, optional CuPy/CUDA execution, energy and visibility
diagnostics, and the finite Green-boundary-return ledger.

The minimal scanner exposes only four controls:

```text
--tmax
--camera
--cutoff
--grid
```

and prints only indexed grid heights.

The score measures visibility of the resultant relative to retained coordinate
energy. A vanishing or tiny resultant does not assert that the underlying
energy vanished. The release tests certify the CPU/NumPy `float64` path; the
optional CUDA path is included but is not certified by the GitHub-hosted
runner.

No finite scan, cutoff observation, or grid candidate is promoted to a theorem
about an infinite operator.

## Interpretation boundary

This release does not:

- introduce primality into the arbitrary-base positional laws;
- identify `b^(-k)` pointwise with `n^(-1)`;
- identify raw boundary closure with a native operator zero lacking its mass
  domain;
- infer pre-compression reconstruction from a scalar zero;
- construct the remaining global moment state at every Genuine zero;
- identify the concrete C2 support defect with a radial analytic defect;
- treat numerical output as a Lean proof;
- introduce a local `axiom`, `sorry`, or `admit`.

## New and consolidated source

Arbitrary-base foundations:

- `CPFormal/Carry/PositionalDecomposition.lean`;
- `CPFormal/Carry/UniformCarryProbability.lean`;
- `CPFormal/Analytic/CpQuadraticDomainCrosswalk.lean`.

Real/scalar crosswalk and deduplicated guardrails:

- `CPFormal/Analytic/CpGenuineNativeRealBoundaryCrosswalk.lean`;
- `CPFormal/Analytic/CpGenuineRealPlaneReconstruction.lean`.

Contractive lift and extended C2/Hilbert ledger:

- `CPFormal/Analytic/CpNativeGprePrimeCarryContraction.lean`;
- `CPFormal/Carry/C2OddCorePushforward.lean`;
- `CPFormal/Analytic/CpC2OddCorePushforwardTfvd.lean`;
- `CPFormal/Analytic/CpC2DirichletJetGpre.lean`;
- `CPFormal/Analytic/CpC2GpreCofinalSynthesis.lean`;
- `CPFormal/Analytic/CpGenuinePrimeCarryDefectUniformBound.lean`.

Empirical files:

- `docs/REAL_ROTATION_EMPIRICAL_OPERATOR.md`;
- `experiments/c2_real_rotation_operator.py`;
- `experiments/c2_real_rotation_minimal.py`;
- `experiments/test_c2_real_rotation_operator.py`;
- `experiments/test_c2_real_rotation_minimal.py`.

## Integration provenance

| Integrated PR | Audited head | Lean kernel audit | Main commit |
|---|---|---|---|
| #18 | `5da5f724b4cb3378976d134b2c468e8ec1d43e22` | run #707 (`30460481600`) | `d8d905b3653a03e5a0d3ed09b2c096e351c060b2` |
| #19 | `a3fbe010cceddfad4dc2b6ba42db35757fbd2a9d` | run #709 (`30461603119`) | `8cee49af8fefc4baef61c1dc27ee5eabcf071878` |
| #20 | `f5dea0668d430e9398280b8bfc7e441056433ab1` | run #711 (`30462287468`) | `f46b48b4aa72c00a9f7803a9662f30eef70cb613` |
| #21 | `6d2ba5a3fc7980f5d7b9d6a426dedeba934dca91` | run #713 (`30462872491`) | `bf13b6f42dbeea28644aeb0d7e5a23638cbe293b` |
| #22 | `daa6fd92cdd8d519e8ff78a10192dc852f3a34a6` | run #715 (`30463662198`) | `7c0655d840ff1bae3b4759e691a4c37a28df7627` |

Historical PRs #16, #17, #12, and #4 were closed as superseded after their
nonoverlapping content was integrated and re-audited in #19 through #22.

The consolidated source checkpoint before adding the publisher is
`7c0655d840ff1bae3b4759e691a4c37a28df7627`.

## Release verification

Before publishing the tag and GitHub Release, the release workflow executes:

```bash
bash scripts/static_audit.sh

python -m unittest -v \
  experiments/test_c2_real_rotation_operator.py \
  experiments/test_c2_real_rotation_minimal.py

lake build --wfail
```

The workflow also verifies that it is running on `refs/heads/main`, that the
checked-out commit is still the remote `main` head, and that any pre-existing
`v0.52.0` tag is annotated and points to exactly the same commit.

Only after every check succeeds does the workflow create the annotated tag and
publish the GitHub Release.

## Archival and Zenodo

The GitHub Release is published as a non-draft, non-prerelease immutable
snapshot. This published release is the event consumed by the repository's
Zenodo integration.

Zenodo assigns a version DOI after ingesting `v0.52.0`. The stable concept
DOI remains `10.5281/zenodo.21483474`.
