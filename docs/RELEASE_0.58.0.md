# CPFormal v0.58.0 — Immutable complete Git mirror

## Purpose

This is the final preservation checkpoint created **after** enabling:

- protection of the `main` branch against force-push and deletion;
- GitHub immutable releases for all future publications.

The release is published from a draft only after all preservation assets are attached. Once published, GitHub locks the tag and attached assets and generates a release attestation.

## Complete repository preservation

The release contains a self-contained Git bundle carrying every ref available at publication time:

- all `refs/heads/*` branches;
- all `refs/tags/*` tags;
- all available `refs/pull/*/head` pull-request heads;
- the complete Git object graph reachable from those refs.

This is stronger than GitHub's automatically generated source ZIP, which contains only the checked-out tree at one tag.

## Immutable release assets

Before publication, the draft must contain:

- `primos-complete-v0.58.0.bundle`;
- `primos-complete-v0.58.0-refs.txt`;
- `primos-complete-v0.58.0-heads.txt`;
- `primos-complete-v0.58.0-verify.txt`;
- `primos-complete-v0.58.0-SHA256SUMS.txt`;
- `primos-complete-v0.58.0-RESTORE.txt`.

The publisher then makes the draft public. With release immutability enabled, the Git tag and these six assets cannot be moved, replaced, or deleted through normal GitHub release management.

## Verification gates

The publisher fails closed unless it:

1. sees all branch, tag, and pull-request refs;
2. passes `scripts/static_audit.sh`;
3. passes all real-rotation regression tests;
4. passes `lake build --wfail`;
5. verifies the bundle with `git bundle verify`;
6. restores the bundle into a fresh bare repository;
7. passes `git fsck --full --strict` on the restored repository;
8. proves the restored ref manifest equals the original manifest;
9. attaches all six assets before publication;
10. verifies the published release with `gh release verify`.

## Mathematical content preserved

The bundle includes the complete history of the project, including:

- positional carry, mass and quadratic rigidity;
- all camera, Green, TFVD, boundary and return constructions;
- native real-operator confinement;
- Genuine/native crosswalks and their exact logical frontiers;
- the C2 quadratic diagnostic route;
- exact seeded TFVD radial reconstruction;
- finite Bessel/Pythagoras conservation;
- native `G_pre` moment contraction;
- intentionally failing probes and every superseded historical route.

The deliberately red diagnostic modules remain outside the active default build but are preserved exactly in the Git bundle.

## Recovery

```bash
sha256sum -c primos-complete-v0.58.0-SHA256SUMS.txt

git clone --mirror \
  primos-complete-v0.58.0.bundle \
  primos-restored.git

git -C primos-restored.git fsck --full --strict
```

A normal working checkout can then be created with:

```bash
git clone primos-restored.git primos-working-copy
```

## External archive

The published GitHub Release triggers the repository's Zenodo integration. The stable concept DOI remains:

```text
10.5281/zenodo.21483474
```

A separate verification records the version DOI, checksums and exact agreement between the immutable GitHub assets and the files ingested by Zenodo.
