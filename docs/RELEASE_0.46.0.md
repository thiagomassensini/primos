# CPFormal v0.46.0 — Genuine-first cutoff provenance and orthogonal limit checkpoint

## Scope

This release freezes the kernel-audited Genuine-first extension integrated by pull request #3.

The checkpoint preserves cutoff error as bracket provenance, aligns distinct prime cameras without scalar compression, and carries the finite Genuine cameras and Green graph to explicit orthogonal limits.

The native C2 reading remains carry-first:

```
carry
→ critical amplitude
→ criticalLineParameter t
→ real-spectral state
→ realSpectralGenuine t
→ operator limit.
```

The ambient parameter `s : ℂ` used by some limit theorems is an extension of this native orbit, not a replacement for its carry-fixed geometry.

## Reproducible reference

- source branch: `agent/genuine-first-cutoff-tail`;
- mathematical source head before release metadata: `30d121da38d241e1e6870f7b85d00cb7cd03420c`;
- pull request: #3;
- validating workflow before integration: `Lean kernel audit`, run 421;
- validation result: `success`;
- intended integration method: merge commit, without squash or rebase;
- permanent safety branch is created from the final PR head before integration.

## Kernel-checked additions

### Cutoff provenance

- exact decomposition of the infinite bracketed chart into finite prefix and unincorporated bracket tail;
- at a Genuine zero, the remaining finite current is exactly the negative tail;
- normalized cameras retain the cutoff provenance instead of discarding it.

### Aligned multibase transfer

- crossed prime cutoffs share the same horizontal endpoint;
- exact horizontal–vertical transfer identities between distinct prime cameras;
- a bidirectional multibase defect that vanishes exactly with `genuineContinuation` inside the Genuine strip;
- bracket tails converge to zero along every aligned horizon.

### Orthogonal Green cameras

- two prime cameras are kept as independent coordinates of `EuclideanSpace ℝ (Fin 2)`;
- Green energy is measured as a sum of coordinate energies, with no cross-prime cancellation;
- finite aligned Green flux decomposes exactly into radial bulk plus bracket boundary;
- coordinatewise closure is characterized by the critical displacement in the ambient extension.

### Orthogonal Genuine operator limit

- normalized finite prime cameras converge to `genuineContinuation`;
- aligned finite Genuine operators are diagonal on `EuclideanSpace ℂ (Fin 2)`;
- strong convergence is proved state by state;
- at a Genuine zero, every finite aligned action converges to the zero operator without scalar compression between cameras.

### Infinite Green graph

- reflected gradient edges admit an absolutely summable `(n+1)^(-3)` majorant;
- the infinite reflected Green energy is defined and proved strictly positive;
- the exact orthogonal Green limit vector is computed;
- the joint Genuine/Green kernel is identified without promoting the ambient classification to a missing gate of the native C2 orbit.

## Scope correction preserved in this release

Two redundant gate modules explored during the branch history were removed before integration. Their statements merely repackaged already available carry and critical-orbit results while mixing the ambient `s : ℂ` extension with the native `t : ℝ` construction.

The final tree keeps the five genuinely new modules only:

- `CPFormal/Analytic/CpGenuineFirstCutoffTail.lean`;
- `CPFormal/Analytic/CpGenuineFirstMultibaseCutoff.lean`;
- `CPFormal/Analytic/CpGenuineFirstOrthogonalMultibaseGreen.lean`;
- `CPFormal/Analytic/CpGenuineFirstOrthogonalLimit.lean`;
- `CPFormal/Analytic/CpGenuineFirstOrthogonalGreenLimit.lean`.

## Mathematical scope

The proofs use carry weights, finite brackets, exact tilings, prime-camera compatibility, discrete Green identities, radial factorization, reflected positivity, summability and Hilbert-space convergence.

They do not use the zeta function, a functional equation, zero tables, RH, new axioms or `sorry`. Any external conjectural consequence remains outside the conceptual core recorded here.

## Verification

Before publishing the tag and GitHub Release, the release workflow executes:

```bash
bash scripts/static_audit.sh
lake build --wfail
```

The tag is created only if both commands succeed on the merged `main` commit.

## Archival and Zenodo

The annotated tag is an immutable reference to the verified `main` state. The published, non-draft, non-prerelease GitHub Release is the event consumed by the repository's Zenodo integration. Zenodo assigns the version DOI after ingesting that release.
