# Recovered research context — 2026-08-01

This directory preserves, verbatim, the mathematical notes recovered from a
previous interrupted working session.  Preservation here prevents loss of
definitions, proposed routes, chronology, and negative diagnostics.

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
