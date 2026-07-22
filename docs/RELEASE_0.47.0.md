# CPFormal v0.47.0 — Genuine-first completed operator and multiprime kernel-state checkpoint

## Scope

This release freezes the kernel-audited chain developed in pull requests #5, #6 and the final kernel-state checkpoint.

It combines the scalar Genuine channel with its orthogonal Green companion, proves non-vanishing off the critical abscissa for that completed operator, and reduces the still-stronger scalar Genuine observability problem to one explicit all-prime Hilbert-state construction.

The release preserves the Genuine-first distinction between these two statements:

- the completed `Genuine ⊕ Green` operator is nonzero off the half-abscissa;
- non-vanishing of `genuineContinuation` alone still requires the kernel-to-state realization identified here.

No scalar non-vanishing theorem is claimed by renaming the completed operator.

## Kernel-checked additions

### Carry-completed Genuine operator

- the first carry amplitude is identified with the critical amplitude `p^(-1/2)`;
- branch amplitude agrees with this carry amplitude exactly at `sigma = 1/2`;
- the Genuine and Green channels are retained in an orthogonal direct sum;
- inside `genuineCriticalStrip`, the completed operator is nonzero whenever `Re(s) != 1/2`;
- at a Genuine zero, the finite completed operators converge strongly to the completed limit operator.

### Cross-prime provenance and centered Bessel detector

- the difference of TFVD provenance between two prime cameras is identified exactly with the opposite Green-flux difference;
- finite equality, and asymptotic synchronization, of two distinct prime provenances is equivalent to zero critical displacement;
- the prime-independent finite boundary is removed before summing camera energies;
- square-summability of the centered all-prime Green profile is equivalent to `Re(s) = 1/2` at every nonempty cutoff;
- the native `G_pre` prime tower is proved square-summable at every positive arithmetic time.

### Canonical all-prime state and exact remaining obligation

- every finite prime atlas has a canonical Green bulk state with an exact norm ledger;
- uniform boundedness of the finite-atlas norms is equivalent to existence of one global `ell^2` prime-camera state;
- existence of that global state at one nonempty cutoff is equivalent to zero critical displacement;
- every native `G_pre` state produces a literal square-summable prime-moment vector;
- the missing coordinate identity between those moments and the centered Green bulk is isolated explicitly;
- the assertion that every Genuine zero produces the global prime state is proved equivalent to the strong scalar localization theorem and to `GenuineZeroSaturatesCarry 3`.

This last equivalence is a scope guard: the state construction is not inserted as a hidden assumption or presented as a weaker result that already contains the desired conclusion.

## New modules

- `CPFormal/Analytic/CpCarryAmplitudeIdentification.lean`;
- `CPFormal/Analytic/CpGenuineGreenCompletedOperator.lean`;
- `CPFormal/Analytic/CpGenuineCrossPrimeObservability.lean`;
- `CPFormal/Analytic/CpGenuinePrimeGreenBessel.lean`;
- `CPFormal/Analytic/CpNativeGprePrimeTowerBessel.lean`;
- `CPFormal/Analytic/CpGenuineKernelPrimeState.lean`.

## Mathematical scope

The proofs use carry amplitudes, orthogonal direct sums, finite and infinite Green identities, cross-prime provenance, prime-indexed `ell^2` spaces, Bessel control, Cauchy--Schwarz estimates and exact Hilbert completion criteria.

They do not use the zeta function, a functional equation, zero tables, RH, new axioms, `sorry` or `admit`.

## Verification

Before publishing the tag and GitHub Release, the release workflow executes:

```bash
bash scripts/static_audit.sh
lake build --wfail
```

The annotated tag is created on the merged `main` commit only after both checks succeed.

## Archival and Zenodo

The published GitHub Release is non-draft and non-prerelease. It is the event consumed by the repository's Zenodo integration. Zenodo assigns the version DOI after ingesting this immutable `v0.47.0` snapshot; the stable concept DOI remains `10.5281/zenodo.21483474`.
