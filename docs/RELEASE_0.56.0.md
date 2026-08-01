# CPFormal v0.56.0 — Complete research-history preservation

## Purpose

This release is a preservation checkpoint. It integrates the fully audited PR #34 and makes every open or historical unmerged pull-request head permanently reachable from `main` without activating deliberately failing diagnostic code.

## Integrated green mathematics

PR #34 is merged into `main` through merge commit:

```text
a07f9553e14c8586268b8fe7efa1ae443920b192
```

It contributes:

- seeded TFVD reconstruction without loss;
- exact cancellation of the aligned moving endpoint and bracket boundary at finite cutoff;
- the pure radial Green observable;
- the exact TFVD–Bessel crosswalk;
- finite Pythagorean conservation of active camera energy and orthogonal residual;
- equivalence between uniform finite-atlas Bessel conservation and `Re(s) = 1/2`;
- the conditional native `G_pre` moment-contraction endpoint with factor `11/12`.

The release does not claim the still-open implication from a raw scalar Genuine zero to a single atlas-independent native moment realization.

## Complete draft-history retention

The archive checkpoint commit is:

```text
4e29cb2fb177517d5ddaf70bb7079c8a0f7bc69c
```

Its working tree preserves the certified active source, while its Git parent graph includes every unmerged research head:

```text
PR #4   c90db393791a34846f002c7bdd526ac39e99b43d
PR #12  fca2eb91cd63bb85544f32b6ce2218b9f27d0c30
PR #16  e68cad52604e6957e19cd7cce8b1a9f21cafacad
PR #17  0519d4629aa82a46aad22d85ce1c8acaad974707
PR #25  d2b36a2f7689684c97b3c73b0122f2369bb1d14b
PR #26  68724075d7d44f7c6efb6cfabfc70030bb295945
PR #27  8d7a65824a56ed7e690d276c64b1929ef4cd021b
PR #31  9038d18de17a9008a93c04385fcabab3e4d3b6c4
PR #32  f21517a027b2ef130102f5c72ab979e88b305dea
PR #33  30c3e3018d1bb91d85c63d28324e97bfda31a994
```

Because these commits are ancestors of `main`, their complete trees and histories remain reachable even if the original pull-request branches are removed.

Independent `archive/pr-*` branch aliases were also created at each exact hash. The recovery manifest is:

```text
docs/ARCHIVE_ALL_DRAFTS_2026-08-01.md
```

PR #33 remains preserved as a deliberately failing diagnostic probe, but is not part of the active default build. This preserves both the obstruction and the green certification boundary.

## Validation protocol

The publisher must verify the exact current `main` head and run:

```bash
bash scripts/static_audit.sh

python -m unittest -v \
  experiments/test_c2_real_rotation_operator.py \
  experiments/test_c2_real_rotation_minimal.py

lake build --wfail
```

Only after all checks succeed may it create the annotated tag and public GitHub Release.

## GitHub and Zenodo archive

The annotated tag is:

```text
v0.56.0
```

The public, non-draft, non-prerelease GitHub Release is the ingestion event for the repository's Zenodo integration.

Stable concept DOI:

```text
10.5281/zenodo.21483474
```

The version DOI is assigned by Zenodo after release ingestion.
