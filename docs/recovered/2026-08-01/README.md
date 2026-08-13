# Recovered research context — 2026-08-01

> **Semantic archive warning.** Some recovered notes define a “native zero”
> as `mass compatibility ∧ boundary closure`. That terminology is obsolete
> and must not be used as the current API. In the active Lean sources, zero is
> boundary closure alone; mass equilibrium and the Green center are separate.
> See `docs/NATIVE_ZERO_SEMANTICS_CORRECTION.md`.

This directory preserves the mathematical notes recovered from a previous
interrupted working session.  The readable top-level copies may normalize
whitespace or correct terminology.  Their 22 byte-exact source payloads,
including the Python companion and four Lean drafts, are preserved under
`raw/` with a SHA-256 manifest.  This prevents loss of definitions, proposed
routes, chronology, negative diagnostics, and original wording.

These Markdown files are research records, not Lean certificates.  They may
contain proposed identities, numerical evidence, historical terminology, or
proof plans whose global hypotheses have not been discharged.  The current
kernel-checked scope is determined by the Lean sources, `docs/AUDIT.md`, and
`docs/CLAIM_LEDGER.md`.

Four recovered Lean drafts were promoted to active, compiled modules rather
than archived here:

- `CPFormal.Analytic.CpConformalJacobian`;
- `CPFormal.Analytic.CpConformalBranchScale`;
- `CPFormal.Analytic.CpRadialCoercivity`;
- `CPFormal.Analytic.CpReflectedGreenBridge`.

The executable branch/tilt companion was preserved as
`experiments/cp_branch_tilt_operator.py`.  Its numerical output is an audit aid
and is not a premise of any Lean theorem.

The central scope distinction recovered from the session is:

```text
carry convexity/concavity
  -> cpTiltAtSigma = 0 iff Re(s) = 1/2        (kernel checked)

genuineContinuation s = 0
  -> cpTiltAtSigma = 0                        (remaining global bridge)
```

The active module `CPFormal.Analytic.CpGenuineCarryTiltFrontier` records that
remaining bridge without reversing the causal origin of the half-abscissa or
hiding the desired conclusion in a Hilbert-state existence assumption.
