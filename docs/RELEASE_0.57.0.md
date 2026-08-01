# CPFormal v0.57.0 — Complete Git mirror preservation

## Purpose

This is a preservation release correcting an important distinction:
GitHub and Zenodo source-code archives contain the checked-out tree of a tag,
but they are not themselves a complete Git repository and do not necessarily
contain every historical branch tree.

Version `v0.57.0` therefore publishes a verified Git bundle as an explicit
release asset. The bundle is a self-contained, cloneable Git database carrying
all repository branches, tags, and pull-request head refs fetched at publication
time.

## Preserved refs

The publisher fetches and records:

- every `refs/heads/*` branch;
- every `refs/tags/*` tag;
- every available `refs/pull/*/head` pull-request head;
- the complete object graph reachable from those refs.

Remote branch refs are promoted to their original local branch names before the
bundle is created, so recovery recreates the branch namespace rather than only
remote-tracking aliases.

## Release assets

The release must contain, before publication:

- `primos-complete-v0.57.0.bundle` — complete cloneable Git bundle;
- `primos-complete-v0.57.0-refs.txt` — exact ref/SHA manifest;
- `primos-complete-v0.57.0-heads.txt` — heads reported by the bundle;
- `primos-complete-v0.57.0-verify.txt` — bundle and restored-repository checks;
- `primos-complete-v0.57.0-SHA256SUMS.txt` — cryptographic checksums;
- `primos-complete-v0.57.0-RESTORE.txt` — recovery commands.

The publisher fails closed unless it sees at least the 52 branch refs and 12 tag
refs audited immediately before this checkpoint, verifies the bundle, restores
it into a fresh bare repository, and passes `git fsck --full --strict` on the
restored copy.

## Mathematical checkpoint

The active tree contains the green `v0.56.0` preservation checkpoint, including
PR #34:

- exact seeded TFVD reconstruction;
- exact finite radial Green bulk;
- finite Bessel/Pythagoras conservation;
- native `G_pre` moment contraction.

Deliberately failing diagnostic probes remain outside the active build but are
preserved in the bundle and in the archived Git ancestry.

## Verification gates

Before publishing, the workflow must pass:

```bash
bash scripts/static_audit.sh
python -m unittest -v \
  experiments/test_c2_real_rotation_operator.py \
  experiments/test_c2_real_rotation_minimal.py
lake build --wfail
git bundle verify primos-complete-v0.57.0.bundle
git fsck --full --strict  # on a fresh mirror restored from the bundle
```

The release is created as a draft, all preservation assets are attached, and
only then is it published. This ordering is compatible with GitHub immutable
releases if that repository setting is enabled before publication.

## Recovery

A full mirror can be reconstructed with:

```bash
git clone --mirror primos-complete-v0.57.0.bundle primos-restored.git
cd primos-restored.git
git fsck --full --strict
```

A normal working copy can then be created from the restored mirror:

```bash
git clone primos-restored.git primos-restored
```

## Zenodo

The published GitHub Release is consumed by the existing Zenodo integration.
The Zenodo record must be checked after ingestion to confirm that the bundle,
ref manifest, verification report, restore instructions, and checksum file are
all present.

Stable concept DOI:

```text
10.5281/zenodo.21483474
```
