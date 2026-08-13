# Nota de correção semântica

> Este documento registra historicamente a `v0.51.0`. Toda passagem que usa
> “confinamento do zero nativo” a partir da compatibilidade de massa deve ser
> lida como substituída: equilíbrio quadrático e anulação são predicados
> separados. Consulte `docs/NATIVE_ZERO_SEMANTICS_CORRECTION.md`.

## CPFormal v0.51.0 — registro histórico

## Scope

This release freezes the kernel-checked separation between two mathematical
layers that are often blended when interpreting the classical explicit
formula:

1. the real native carry operator, whose zero confinement is fixed by its
   quadratic mass domain before any arithmetic projection; and
2. the arithmetic readout in which Möbius deconvolution resolves the logarithm
   on all positive integers into the von Mangoldt signal supported on prime
   powers, whose L-series is the negative logarithmic derivative of Riemann
   zeta on `re(s) > 1`.

The release records the exact reversible arithmetic circuit without declaring
that the classical explicit formula is logically circular.

## Exact arithmetic round-trip

The kernel proves:

```text
ArithmeticFunction.log * ArithmeticFunction.moebius
  = ArithmeticFunction.vonMangoldt

ArithmeticFunction.vonMangoldt * ArithmeticFunction.zeta
  = ArithmeticFunction.log
```

Consequently:

```text
(log * moebius) * zeta_arithmetic = log.
```

Here `ArithmeticFunction.zeta` is the divisor-summation arithmetic function,
not the complex Riemann zeta function. The first identity extracts the
prime-power logarithmic signal; the second reconstructs the original integer
logarithm exactly.

## Pointwise support and reconstruction

The release also records:

```text
vonMangoldt(n) != 0 <-> IsPrimePow(n)

sum_{d | n} vonMangoldt(d) = Real.log(n).
```

Thus the support on prime powers is an exact Möbius-resolved presentation of
the global logarithmic field, with a lossless divisor-sum reconstruction.

## Logarithmic derivative readout

On the half-plane of absolute convergence `1 < re(s)`, the kernel proves:

```text
L(vonMangoldt)(s)
  = -deriv(riemannZeta)(s) / riemannZeta(s).
```

This identifies the classical logarithmic-derivative channel as the L-series
of the extracted prime-power signal.

## Separation from native carry confinement

The same module places the arithmetic readout beside the already established
real native operator theorem:

```text
IsNativeCarryRealOperatorZero camera sigma time
  <->
  sigma = 1/2
    and IsNativeCarryRealOperatorResonance camera time.
```

The conjunction theorem inserts no implication from the prime-power readout to
carry confinement and no implication from carry confinement to the arithmetic
identities. It records that both statements are simultaneously valid while
remaining logically separate constructions.

## Interpretation boundary

This release does not:

- formalize the complete classical explicit formula;
- call that formula logically circular;
- erase the legitimate arithmetic relation between zeros and prime-counting
  readouts;
- identify `ArithmeticFunction.zeta` with `riemannZeta` as objects;
- derive the native `sigma = 1/2` confinement from primes, Möbius inversion or
  the logarithmic derivative;
- introduce a new axiom, `sorry`, `admit`, reconstruction certificate or
  spectral bridge.

What is frozen is narrower and exact: the prime-power signal entering
`-zeta'/zeta` is obtained by an invertible arithmetic resolution of the
integer logarithm, while the native carry operator has an independently proved
quadratic confinement theorem.

## New module

- `CPFormal/Analytic/CpNativeCarryMobiusLogDerivativeGuardrail.lean`.

## Provenance

- mathematical PR: `#14`;
- audited mathematical head: `ffaffa7bc19ddd936cc925ca70af9e648dc1f9f2`;
- squash commit on `main`: `39279963f866127e88cea17a2cb6b918756bdbf5`;
- Lean kernel audit: run `#687` (`30328723908`), green.

## Verification

Before publishing the tag and GitHub Release, the release workflow executes:

```bash
bash scripts/static_audit.sh
lake build --wfail
```

The annotated tag is created on the merged `main` release commit only after
both checks succeed.

## Archival and Zenodo

The GitHub Release is published as a non-draft, non-prerelease immutable
snapshot. It is the event consumed by the repository's Zenodo integration.
Zenodo assigns a version DOI after ingesting `v0.51.0`; the stable concept DOI
remains `10.5281/zenodo.21483474`.
