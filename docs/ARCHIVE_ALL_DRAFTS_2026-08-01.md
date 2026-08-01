# Immutable draft archive — 2026-08-01

This checkpoint preserves every pull-request head that was not already reachable from `main`, plus the exact head of PR #34 before integration.

The archive commit containing this file uses all listed commits as Git parents. Consequently, their complete trees and histories are reachable from `main` even if the original PR branches and the explicit `archive/*` aliases are later deleted.

## Integrated checkpoint

- PR #34 — `8bbab0b04d73c1a37914e369b1146853ba968b73`
  - merged into `main` by merge commit `a07f9553e14c8586268b8fe7efa1ae443920b192`
  - seeded TFVD reconstruction, exact finite Bessel/Pythagoras conservation, and native moment contraction

## Open research heads preserved

- PR #25 — `d2b36a2f7689684c97b3c73b0122f2369bb1d14b`
  - primitive/Genuine/zeta zero-set identity
- PR #26 — `68724075d7d44f7c6efb6cfabfc70030bb295945`
  - Mathlib RH promotion and mass-preservation frontier
- PR #27 — `8d7a65824a56ed7e690d276c64b1929ef4cd021b`
  - native/Genuine/Green/completed crosswalk
- PR #31 — `9038d18de17a9008a93c04385fcabab3e4d3b6c4`
  - raw Genuine-zero confinement frontier
- PR #32 — `f21517a027b2ef130102f5c72ab979e88b305dea`
  - quadratic C2 frontier
- PR #33 — `30c3e3018d1bb91d85c63d28324e97bfda31a994`
  - deliberately failing off-critical mass-cost diagnostic probe

## Historical unmerged heads preserved

These were superseded by later integrations, but their exact original histories are retained:

- PR #4 — `c90db393791a34846f002c7bdd526ac39e99b43d`
- PR #12 — `fca2eb91cd63bb85544f32b6ce2218b9f27d0c30`
- PR #16 — `e68cad52604e6957e19cd7cce8b1a9f21cafacad`
- PR #17 — `0519d4629aa82a46aad22d85ce1c8acaad974707`

## Independent archive refs

The following branch aliases were created at the exact hashes:

- `archive/pr-04-c90db39-2026-08-01`
- `archive/pr-12-fca2eb9-2026-08-01`
- `archive/pr-16-e68cad5-2026-08-01`
- `archive/pr-17-0519d46-2026-08-01`
- `archive/pr-25-d2b36a2-2026-08-01`
- `archive/pr-26-6872407-2026-08-01`
- `archive/pr-27-8d7a658-2026-08-01`
- `archive/pr-31-9038d18-2026-08-01`
- `archive/pr-32-f21517a-2026-08-01`
- `archive/pr-33-30c3e30-2026-08-01`
- `archive/pr-34-8bbab0b-2026-08-01`

## Recovery

Any preserved commit can be restored directly:

```bash
git switch --detach <full-sha>
git switch -c recovered/<name>
```

To verify that a commit remains reachable from the archive checkpoint:

```bash
git merge-base --is-ancestor <full-sha> <archive-checkpoint-sha>
```

The intentionally red diagnostic PR #33 is retained as history but is not placed in the active default build. This keeps the certified `main` green while preserving the exact kernel obstruction.
