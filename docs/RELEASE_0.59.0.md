# CPFormal v0.59.0 — Carry-first active integration and immutable mirror

## Release status

- parent release: `v0.58.0`;
- release branch: `agent/v059-active-integration`;
- planned annotated tag: `v0.59.0`;
- stable Zenodo concept DOI: `10.5281/zenodo.21483474`.

The release workflow is the authority for the exact `main` commit tagged by
`v0.59.0`.  It refuses to publish if the checked-out commit is not the current
remote `main`, if the static audit fails, if any Python regression fails, or if
`lake build --wfail` does not elaborate the full Lean project.

## Reconciliation after the immutable v0.58.0 checkpoint

The `v0.58.0` preservation release retained every draft head in the Git object
graph, but several draft theorems were intentionally absent from its active
checkout. This release performs the second, semantic half of preservation: it
merges the green, non-circular content into the active `main` tree while keeping
all `v0.56.0`–`v0.58.0` workflows, notes, tags and recovery artifacts intact.

The publisher again constructs a complete bundle of all branch, tag and
pull-request refs, restores it into a fresh mirror, runs `git fsck --full
--strict`, compares ref manifests and checksum-protects the recovery assets
before publishing the immutable release. Thus both meanings of “do not lose
anything” are checked: historical reachability and active kernel integration.

## Carry comes first

This checkpoint preserves the causal order of the theory:

```text
positional carry and its quadratic mass
  -> critical displacement delta = sigma - 1/2
  -> convexity / concavity of x^(-delta)
  -> signed Cp tilt
  -> cpTiltAtSigma = 0 iff sigma = 1/2.
```

The half-abscissa is not introduced by a Hilbert-state existence assumption.
The existing kernel theorem `cpTiltAtSigma_eq_zero_iff_half`, preceded by the
strict positive and negative tilt theorems, already establishes the unique
radial equilibrium from carry geometry.

The new `CpGenuineCarryTiltFrontier` module then distinguishes that proved
rigidity from the remaining zero-transfer question.  It proves:

```text
finite reflected Green bulk = 0
  iff carry tilt = 0                       (pointwise, nonempty cutoff)

every Genuine zero annihilates carry tilt
  iff GenuineStrongNonvanishingInStrip

every Genuine zero annihilates reflected Green bulk
  iff GenuineStrongNonvanishingInStrip.
```

Thus the Green and tilt languages agree on the radial zero, while the global
arrow from a raw Genuine zero to that radial zero remains explicit.  Endpoint
closure is not misidentified with bulk closure: at a Genuine zero the proved
endpoint limit removes the boundary and leaves the radial bulk.

## Natural integer bases and the global blind point

The carry structure is not prime-specific.  The inherited PR #30 results
cover every positional base `b > 1`; the finite and analytic natural-camera
theorems cover every nondegenerate width `b >= 3`, without a primality or
parity hypothesis.  The new `CpNaturalCameraGlobalBlindSpot` module packages
the common factorization as

```text
genuineContinuation s = 0
  iff every natural camera b >= 3 is zero at s
```

for `s` in the critical strip.  At such a zero, every finite natural-camera
resultant converges to zero.  Independently,
`infiniteReflectedGreenEnergy_pos` proves that the reflected Green energy is
strictly positive at the same parameter.  Thus the kernel distinguishes a
simultaneous scalar blind point from disappearance of energy.

It does not yet identify that Green energy with one common pre-compression
state for all natural cameras.  That state-level identification is the open
`GREEN-NATCAM-INTERTWINER`, so it is not used to infer confinement.

The aligned `C2` scanner has one leg on each side.  Its equality with the
native scanner whose parameter is `4` is an implementation identity with
`halfRange 4 = 1`; it is not an equality with a geometric `C4` having two
legs on each side.

## Recovered conformal and coercive modules

Four Lean modules recovered from the interrupted research session are active
and compiled in this release:

- `CpConformalJacobian`: the complex-differentiable quarter-turn law and its
  norm/orthogonality consequences;
- `CpConformalBranchScale`: the exact radial derivative of the branch mass and
  its nonzero restoring slope at `sigma = 1/2`;
- `CpRadialCoercivity`: the global quantitative estimate
  `2 * |delta| * log p <= |cpRadialDifference p delta|`;
- `CpReflectedGreenBridge`: positive reflected energy and the exact conditional
  reduction from bulk-flux closure to the half-abscissa.

No bridge structure is instantiated by renaming the desired conclusion.

## Seeded TFVD reconstruction and finite Bessel conservation

The complete green content of draft PR #34 is incorporated.  The kernel now
checks:

- the seeded finite TFVD reconstruction checkpoint;
- exact endpoint and border cancellation identities;
- the radial closure observable as radial difference times reflected pairing;
- the amplitude/readout crosswalk;
- exact finite Bessel energy conservation;
- the associated Pythagoras identity;
- uniform finite-atlas Bessel boundedness iff the critical displacement is
  zero;
- the conditional contraction from a fixed-time native moment realization to
  `Re(s) = 1/2`.

Two additional audit modules make the terminal gate precise:

```text
existence of the proposed fixed-time native moment source
  iff Re(s) = 1/2

sources for every raw Genuine zero
  iff GenuineStrongNonvanishingInStrip.
```

`CpTfvdGpreCollapseInterface` gives a typed, non-circular interface for a
future explicit collapse from the two same-edge TFVD states into one native
tower state.  The terminal theorem is proved conditional on its coordinate
law; no collapse instance is asserted.

## Integrated draft history

This release incorporates all unique mathematical content from the outstanding
draft stacks:

- PRs #25–#26: primitive/Genuine/Riemann-zeta zero-set identity and the exact
  comparison with Mathlib's `RiemannHypothesis` proposition;
- PRs #27, #31 and #32: native/Genuine/Green crosswalk, the raw-zero
  confinement frontier, and the quadratic C2 activation frontier;
- PR #33: the deliberate red carry-cost probe, repaired into a green theorem
  with the missing mass-compatibility datum explicit;
- PR #34: seeded TFVD reconstruction, Bessel conservation, and native-moment
  contraction;
- `ops/ensure-v0.45.0-release`: its immutable GitHub/Zenodo confirmation JSON
  records, without reactivating obsolete branch-specific workflows.

Closed historical drafts already superseded by main were audited for unique
content.  The original notes recovered from the interrupted chat are preserved
under `docs/recovered/2026-08-01/`, explicitly classified as research records
rather than kernel certificates.

## Independent `formalizacao_C2` cross-audit

The separate green repository `thiagomassensini/formalizacao_C2` was audited
at commit `dc35555879e3c0f188508c729c4a0ea31be246fb`, including its complete
37-commit history.  Its sole GitHub Actions run, `29081538415` / job
`86325282214`, successfully builds the active tilt, center-Gaussian and
anti-miracle route modules.

That repository independently kernel-checks local sign and uniqueness laws for
the C2 tilt bracket, center-Gaussian saturation and branch-norm barrier.  Its
C2 bracket is the local one-leg-per-side `+/-1` detector already generalized
by the Cp tilt in this repository; it is not a geometric C4.  It does not
contain a theorem taking an arbitrary Genuine zero to any of those saturation
conditions.  The anti-miracle nonvanishing
endpoint assumes decomposition, resolvent shape and strict dominance; the
tilt-curvature theorem is separate.  Consequently no duplicate module was
imported as if it paid the missing coupling law.  The cross-audit strengthens
the carry-first diagnosis while preserving the exact open frontier.

## Exact negative result retained

The failed historical attempt to derive unconditional confinement from raw
boundary closure was not discarded.  Its open goal was

```text
NativeCarryRealPlaneMassCompatible s.re s.im.
```

The corrected green theorem accepts that datum explicitly.  The primitive
closure predicate and the full native-zero predicate remain different types:

```text
full native zero = mass compatibility + boundary closure.
```

The integrated Mathlib comparison proves that reconstructing this mass from
every raw scalar closure is equivalent to Mathlib's RH proposition.  It does
not claim that proposition.

## No-escape audit

The certified Lean source contains no local declaration beginning with
`axiom`, `sorry`, or `admit`.  It does not choose a Hilbert witness from an
existence proof that already assumes the half-abscissa.  Diagnostic failures
are preserved in documentation and history, not left as red default targets.

The recovered Python branch/tilt companion is covered by regression tests for:

- exact branch-mass saturation at `sigma = 1/2`;
- negative/zero/positive tilt across the three radial regimes;
- restoration of critical saturation after weighted-leg normalization.

Numerical output remains an audit aid and is not a premise of any Lean proof.

## What this release does not claim

This release does not prove:

- `GenuineStrongNonvanishingInStrip`;
- Mathlib's `RiemannHypothesis`;
- that raw scalar boundary closure reconstructs native mass;
- that every Genuine zero annihilates the carry tilt or reflected Green bulk;
- an unconditional TFVD-to-fixed-time native moment collapse;
- a global Parseval/LSB state whose coordinates are all prime Green readouts;
- a common natural-camera pre-compression state or the
  `GREEN-NATCAM-INTERTWINER`;
- a Hilbert–Polya operator.

It proves that these proposed terminal formulations meet at one sharply typed
frontier, after the carry geometry has already selected the half-abscissa.

## Release protocol

Before publication the `v0.59.0` workflow must run on `main` and execute:

```bash
bash scripts/static_audit.sh

python -m unittest -v \
  experiments/test_c2_real_rotation_operator.py \
  experiments/test_c2_real_rotation_minimal.py \
  experiments/test_cp_branch_tilt_operator.py

lake build --wfail
```

Only after all checks succeed may it reconstruct and verify the complete Git
bundle, create the annotated tag, attach the checksum-protected recovery
assets to a draft, publish the immutable GitHub Release, and verify its
attestation. That publication is the event consumed by the repository's Zenodo
integration; Zenodo assigns the immutable version DOI after ingestion.
