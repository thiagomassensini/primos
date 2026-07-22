# CPFormal v0.45.0 — Genuine-first real spectral and enriched TFVD checkpoint

## Scope

This release freezes the latest fully audited state of the `Genuine first` formalization after the integration of pull request #1 into `main`.

The release is intentionally pre-1.0. It records what the Lean kernel checks today and keeps the remaining analytic and completion gates explicit.

## Reproducible reference

- source branch integrated into `main`: `agent/lean-kernel-audit`;
- last source head before merge: `73bea948ff2b35067397c64561e7a799349d4d76`;
- validating workflow: `Lean kernel audit`, run 388;
- validation result: `success`;
- integration method: merge commit, without squash or rebase;
- permanent safety branch: `archive/green-run-388-2026-07-22`.

## Kernel-checked highlights

### Carry geometry and critical amplitude

- C2 and Cp center-leg incidence and weighted reindexing;
- prime-depth carry coordinates and aligned finite boxes;
- mass `p^(-k)`, amplitude `p^(-k/2)` and the exact quadratic identity;
- branch-norm saturation and tilt rigidity at the critical amplitude.

### Prime cameras and Genuine

- finite saturated brackets and prime charts;
- normal convergence and holomorphy of the bracketed chart;
- camera compatibility and the camera-independent Genuine continuation;
- finite and limiting real-spectral cameras.

### Green and the weighted discrete valve

- concrete unilateral shifts on `l2`;
- carry-weighted vertical Green operator;
- weighted bracket, trace and bounded affine return;
- exact TFVD reconstruction

  `I = G_q B_q + R_q Tr_q`;

- free vertical boundary relation and boundary pencils.

### Real spectral operator theory

- finite self-adjoint logarithmic generator;
- maximal infinite multiplication operator by `log(n+1)`;
- dense domain, self-adjointness and closed graph;
- isometric unitary evolution and group law on `l2`;
- real spectral resonance as a zero characteristic value of the Genuine pencil.

### Enriched provenance and native compression

- typed `G_pre` provenance axes and native value/number-flow separation;
- canonical TFVD–`G_pre` gluing by the same edge;
- closed finite enriched relations and cutoff compatibility;
- enriched analysis with a continuous TFVD left inverse;
- closed and complete finite analysis ranges;
- visible compression that preserves a nonzero blind sector;
- finite native camera coefficients converging to the real-spectral Genuine;
- projective product of all finite enriched analyses, with injective closed range.

### Native arithmetic bounds already closed

- multiplicativity, nonnegativity and global power bound for the Jordan channel;
- generic local Jordan–H compiler:

  `|a*J - 2*H| <= a*D`

  from the explicit positivity, valuation and incidence hypotheses.

## Numerical research artifacts

The repository also contains reproducible finite experiments for:

- no-refinement grid certificates;
- persistence across cutoffs;
- visible/blind energy decomposition;
- seed–bracket destructive closure;
- discrete valve boundary reconstruction.

These experiments are retained as numerical evidence and are not promoted silently to kernel theorems.

## Deliberately open gates

The following claims are not part of this release:

- the concrete prime-power and global valuation bounds for the native `H_(p,tau)` channel;
- instantiation of the local Jordan–H certificate by the full native arithmetic data;
- a concrete `NativeGpreTowerLiftCertificate`;
- the uniform norm-`128` Hilbert completion of the full provenance carrier;
- strong continuity/Stone identification beyond the currently formalized algebraic unitary group.

## Verification

```bash
bash scripts/static_audit.sh
lake build --wfail
```

Both commands must succeed before the release job creates the tag and publishes the GitHub Release.

## Archival note

This GitHub Release is the publication event consumed by the repository's Zenodo integration. Zenodo assigns the version DOI after it ingests the published, non-draft, non-prerelease release.
