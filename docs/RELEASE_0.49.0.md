# CPFormal v0.49.0 — Real carry geometry and precompression Green boundary witness

## Scope

This release freezes the kernel-audited extension integrated by pull request #11
after `v0.48.0`.

The checkpoint separates three layers that had previously shared complex
notation:

1. positional carry fixes the quadratic amplitude exponent `1/2` in every
   nondegenerate natural base;
2. the primitive finite camera, its energy and its zero predicate live
   autonomously in a real plane;
3. Green rigidity eliminates the transverse amplitude deformation in a real
   spectral boundary carrier.

Complex numbers remain available as an optional packaging of two real
coordinates, but the kernel now proves that this packaging preserves the finite
camera, quadratic energy and zeros exactly. Primality is also absent from the
quadratic rigidity theorem: it enters only when one chooses a minimal,
nonredundant family of positional cameras.

The release then retains a vector-valued precompression boundary witness. That
witness carries the physical mass law, the complete real orbit and every finite
camera result before scalar synthesis discards information.

This release does **not** claim that an arbitrary scalar boundary limit
automatically lifts to that physical witness. The kernel proves that such a
universal lift is equivalent to the remaining strong zero-rigidity theorem, so
it is kept explicit rather than hidden inside a domain hypothesis.

## Kernel-checked additions

### Positional quadratic rigidity without primes

For every natural base `b > 1`, every positive depth `k` and every real
deformation exponent `sigma`, the kernel proves

```text
(b^(-k sigma))^2 = b^(-k)
  <->
sigma = 1/2.
```

Equivalently, compatibility of a branch amplitude with carry mass at every
positive depth has the unique solution `sigma = 1/2`.

The same result is realized in `R x R`. For an arbitrary rotation angle
`theta`,

```text
u_(sigma,theta)(b,k)
  = b^(-k sigma) * (cos theta, sin theta),
```

and

```text
Energy(u_(sigma,theta)(b,k)) = b^(-2 k sigma).
```

The energy is independent of `theta` and matches carry mass exactly at
`sigma = 1/2`.

At the global branch level, all bases `b > 1` have the same normalized
quadratic saturation locus. This proves that the exponent is a positional
carry invariant, not a prime-specific phenomenon.

### Primitive real camera and optional complex packaging

The saturated finite chart is defined for any additive commutative group:

```text
nativeCarryFiniteSaturatedChart
  {A : Type*} [AddCommGroup A].
```

Its native rotating realization is defined in `R x R`, with finite bracket,
energy and zero predicates that do not mention `C`.

The optional map

```text
(x,y) |-> x + i y
```

is proved additive and injective. It commutes with every finite saturated
camera and preserves quadratic energy and zeros in both directions, for prime
and composite camera widths.

Thus complex notation does not create, remove or move a primitive camera zero.
It packages the same two real coordinates.

### Real Green rigidity

On the real amplitude plane, let

```text
J(x,y) = (-y,x)
```

be the quarter-turn and let a conformal slope act by

```text
u |-> t u + tau J u.
```

The kernel proves that a Green-symmetric real boundary relation containing a
nonzero direction of this form forces

```text
tau = 0.
```

For native carry parameters,

```text
tau = 1/2 - sigma,
```

so Green symmetry removes the transverse deformation while leaving the real
phase time `t` unrestricted.

The proof retains both the Euclidean pairing and oriented area. The latter is
the real geometric datum often hidden in the imaginary component of a complex
inner product.

### Spectral carrier with one real plane per time

A single `R x R` boundary plane cannot carry two distinct nonzero
Green-symmetric characteristic times. This dimensional obstruction is proved
as a no-go theorem.

The corrected global carrier is therefore

```text
u : R -> (R x R),
```

with one real plane for each spectral label. The fixed multiplication operator

```text
(A u)(r) = r * u(r)
```

is Green-symmetric, and every real `t` has a nonzero characteristic direction.
The transverse rigidity theorem remains local in each real plane.

This gives a fixed, entirely real spectral pencil that accommodates all phase
times without reintroducing complex scalars.

### Precompression boundary witness

The release defines a physical witness retaining:

- the complete critical real state;
- its exact inverse carry mass at every positive integer;
- each finite camera result before scalar compression;
- convergence of those finite resultants;
- a concrete nonzero direction in the real spectral carrier.

From the witness itself, the kernel proves

```text
state energy at n = n^(-1)
```

and constructs the corresponding characteristic direction of the fixed
real-time multiplication pencil.

For a radially deformed scalar readout, promotion to this witness requires
equality of the whole sample function, not merely equality of a final scalar
limit. That equality forces `sigma = 1/2` before the finite camera is applied.

### Fixed symmetric boundary-condition domains

For an arbitrary value--flux pencil `P = (Gamma_0,Gamma_1)` and one fixed
boundary operator `T`, the release defines

```text
D_T = ker (Gamma_1 - T Gamma_0).
```

If `T` is symmetric, the restricted pencil satisfies the exact two-state Green
identity, its value--flux range is a symmetric linear relation and the
corresponding completed TFVD--`G_pre` domain is pairwise
Wronskian-isotropic.

Real scalar Robin operators give a concrete one-parameter family of such fixed
domains.

### Native log-phase orbit and generator channel

Without any zero or resonance hypothesis, the real spectral state is proved to
be the unitary log-phase orbit of its critical seed:

```text
psi_N(t) = U_N(t) psi_N(0).
```

The independently defined log-weighted Dirichlet field is exactly the
logarithmic generator channel:

```text
LogJet_N(t) = L_N psi_N(t).
```

The kernel proves that `L_N` commutes with `U_N(t)` and that both the finite
state norm and finite log-jet norm are constant along real time.

For `0 <= q < 1`, the cutoff-free vertically dressed state

```text
x_(q,t)(n) = q^n * psi_t(n)
```

belongs to the complete carry Hilbert space. Its initial trace and dressed
centered bracket are computed exactly.

The undamped critical orbit has quadratic mass `(n+1)^(-1)`, so its squared
norms form the nonsummable harmonic series. It is therefore a generalized
continuous-spectrum state, while the vertical carry dressing gives an honest
Hilbert-space state.

### Reflected boundary and Cayley guardrails

The reflected log boundary is made Green-symmetric by retaining both reflected
components. Its diagonal relation is shown to be self-adjoint.

The Cayley datum belongs to the fixed zero-flux relation exactly when the
reflected log flux matches. However, that raw zero-flux relation has
characteristic slope `z` only for `z = 0`. It is a boundary condition, not by
itself the full spectral pencil carrying arbitrary `z`.

Consequently, asserting that every scalar bracket closure enters the Cayley
relation is proved equivalent to the remaining zero-rigidity theorem. The
release records this as a guardrail against circular activation.

### Exact angular correction limit

At a Genuine zero, the finite angular correction does not vanish as a small
tail. It converges exactly to the negative infinite reflected Green pairing.

After radial scaling, asking that correction to close is equivalent to asking
the critical displacement to vanish. Hence the previous one-sided angular
Green bridge is itself equivalent to strong zero rigidity and cannot be used
as a weaker decay lemma.

## What is now closed

The kernel now checks the following unconditional chain:

```text
positional carry mass
        ->
unique quadratic amplitude exponent 1/2
        ->
real rotating state with phase-independent energy
        ->
real primitive bracket
        ->
precompression witness
        ->
fixed real spectral carrier
        ->
Green elimination of every transverse deformation.
```

It also checks that complex packaging and prime-camera specialization preserve
the relevant real construction rather than causing it.

For every boundary closure already equipped with the physical precompression
witness, the real Green pencil forces `sigma = 1/2`.

## Remaining honest gate

The scalar boundary predicate currently remembers only a sequence of finite
resultants and its limit. It no longer contains the state that produced those
resultants.

What remains is to derive, from the native bracket--Green--provenance
construction, a precompression witness for every scalar closure of interest.
The kernel proves:

```text
all scalar closures lift to precompression witnesses
  <->
all scalar closures preserve carry mass
  <->
strong zero rigidity.
```

Therefore this last implication is not advertised as a solved intermediate
lemma. The release solves the physical, state-preserving route and identifies
exactly where scalar compression loses the information needed for the converse.

No zeta-function identification, Riemann functional equation, `sorry`, `admit`
or local axiom is used in the new real geometry and Green-rigidity results.

## New modules

- `CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean`;
- `CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean`;
- `CPFormal/Analytic/CpNativeCarryRealPlaneComplexPackaging.lean`;
- `CPFormal/Analytic/CpNativeCarryRealPlaneGreenRigidity.lean`;
- `CPFormal/Analytic/CpNativeCarryRealSpectralBoundaryCarrier.lean`;
- `CPFormal/Analytic/CpNativeCarryRealPrecompressionBoundaryWitness.lean`;
- `CPFormal/Analytic/CpNativeCarrySymmetricBoundaryCondition.lean`;
- `CPFormal/Analytic/CpNativeCarryLogPhaseOrbit.lean`;
- `CPFormal/Analytic/CpNativeCarryLogJetGenerator.lean`;
- `CPFormal/Analytic/CpNativeCarryWeightedSpectralState.lean`;
- `CPFormal/Analytic/CpNativeCarryContinuousSpectrumThreshold.lean`;
- `CPFormal/Analytic/CpNativeCarryLogWaveBoundaryEquivalence.lean`;
- `CPFormal/Analytic/CpNativeCarryReflectedLogBoundarySymmetry.lean`;
- `CPFormal/Analytic/CpNativeCarryReflectedLogBoundaryCayley.lean`;
- `CPFormal/Analytic/CpNativeCarryReflectedLogCayleyGuardrail.lean`;
- `CPFormal/Analytic/CpNativeCarryReflectedLogGreenFluxCrosswalk.lean`;
- `CPFormal/Analytic/CpNativeCarryAngularCorrectionExactLimit.lean`.

## Verification

Before publishing the tag and GitHub Release, the release workflow executes:

```bash
bash scripts/static_audit.sh
lake build --wfail
```

The annotated tag is created on the merged `main` state only after both checks
succeed. The precompression witness checkpoint passed GitHub Actions Lean
kernel audit #673 before merge. Pull request #11 was merged into `main` as
commit `738c852dc5f882c64ab75a3c21fd60e51d89f674`.

## Archival and Zenodo

The published GitHub Release is non-draft and non-prerelease. It is the event
consumed by the repository's Zenodo integration. Zenodo assigns a new version
DOI after ingesting this immutable `v0.49.0` snapshot; the stable concept DOI
remains `10.5281/zenodo.21483474`.
