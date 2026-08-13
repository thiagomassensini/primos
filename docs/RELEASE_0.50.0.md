# Nota de correção semântica

> Este documento registra historicamente a `v0.50.0`, mas sua definição de
> zero nativo foi substituída. Zero agora significa somente fechamento de
> fronteira; compatibilidade de massa e `sigma = 1/2` são propriedades
> quadráticas separadas. Consulte
> `docs/NATIVE_ZERO_SEMANTICS_CORRECTION.md`.

## CPFormal v0.50.0 — registro histórico substituído

## Scope

This release freezes a canonical theorem index and the exact zero-set
factorization of the native real carry operator.

The release keeps the causal order of the formalization:

```text
carry
→ mass
→ quadratic amplitude
→ real rotating state
→ saturated bracket
→ native resonance.
```

It does not classify zeros of a separate non-real scalar continuation. The
new theorem concerns the operator whose mass law is fixed before the bracket
is evaluated.

## Kernel target

For every natural camera width, radial presentation `sigma` and real phase
time `time`, define a native zero by:

```text
the uncompressed real state reproduces inverse carry mass
and
the finite real bracket resultants converge to zero.
```

The kernel is asked to prove the exact equivalence:

```text
native zero at (camera,sigma,time)
  <->
sigma = 1/2 and native resonance at (camera,time).
```

Consequently:

```text
native zero and sigma != 1/2
  ->
False.
```

No primality hypothesis is imposed on the camera. No parameter in the complex
plane, zeta-function identification, functional equation, bridge structure,
certificate, reconstruction premise or new axiom occurs in the theorem.

## Canonical index

`CPFormal/docs/NATIVE_CARRY_THEOREM_INDEX.md` records:

- the active route from incidence to operator confinement;
- the exact theorem names and source modules at every layer;
- the role of TFVD boundary/return reconstruction;
- the distinction between the native real operator, radial presentations,
  scalar continuation and the completed operator;
- parallel routes that were stopped by research choice rather than classified
  as barriers.

## New module

- `CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean`.

## Verification

Before publishing the tag and GitHub Release, the release workflow executes:

```bash
bash scripts/static_audit.sh
lake build --wfail
```

The annotated tag is created on the merged `main` commit only after both checks
succeed.

## Archival and Zenodo

The published GitHub Release is non-draft and non-prerelease. It is the event
consumed by the repository's Zenodo integration. Zenodo assigns a new version
DOI after ingesting the immutable `v0.50.0` snapshot; the stable concept DOI
remains `10.5281/zenodo.21483474`.
