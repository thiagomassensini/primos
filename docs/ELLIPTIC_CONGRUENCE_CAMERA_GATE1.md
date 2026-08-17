# Elliptic congruence camera — Gate 1

## Status

**Experimental finite arithmetic. Not kernel-checked.**

This gate tests whether the all-base/depth language can detect nonuniform
lifting on the affine congruence curve

\[
E:\quad y^2=x^3-x+1.
\]

It does not define a projective elliptic-curve group, an elliptic \(L\)-function,
a rank, a Selmer group, BSD data, or a zero-transfer theorem.

## Camera state

For every base \(q\ge2\) and depth \(k\ge1\), define

\[
X_{q,k}
=
\{(x,y)\bmod q^k:\ y^2\equiv x^3-x+1\pmod{q^k}\}.
\]

Reduction from depth \(k+1\) to \(k\) partitions \(X_{q,k+1}\) into lift
fibers over points \(P\in X_{q,k}\). The tested regular fiber size is \(q\).
The local defect and its quadratic energy are

\[
\delta_{q,k}(P)=\#\pi_{q,k}^{-1}(P)-q,
\qquad
\mathcal E_{q,k}=\sum_{P\in X_{q,k}}\delta_{q,k}(P)^2.
\]

The scalar population channel is normalized as

\[
A_{q,k}=\frac{\#X_{q,k}}{q^{k-1}},
\]

with centered depth curvature

\[
G_{q,k}=A_{q,k+1}-2A_{q,k}+A_{q,k-1}.
\]

## Gate result

The finite exhaustive ledger passes all declared checks:

1. Prime cameras \(3,5,7,11,13\) have uniform fibers and zero local defect
   energy through the tested depths.
2. Camera \(23\) has one singular residue, \((13,0)\), whose first lift fiber
   is empty. Its first energy is exactly \(23^2=529\); all other first fibers
   have size \(23\), and the tested next layer is uniform.
3. Camera \(2\) has persistent local redistribution. Its normalized scalar
   populations become constant, while the local quadratic defect energy stays
   positive. Thus scalar counting can close while fiber geometry remains live.
4. Composite cameras \(15=3\cdot5\) and \(21=3\cdot7\) are uniform through the
   tested depths.
5. Composite cameras \(6=2\cdot3\) and \(10=2\cdot5\) inherit nonuniformity
   from the factor \(2\).
6. For the tested coprime pairs, both point counts and individual lift-fiber
   sizes factor exactly through the two component cameras.

The first-level camera-6 profile is especially transparent:

\[
6\text{ fibers have size }6,
\qquad
6\text{ fibers have size }12,
\qquad
\mathcal E_{6,1}=216.
\]

## What the gate actually found

The useful object is not merely \(\#X_{q,k}\). The quadratic lift-fiber energy
retains local cancellation and redistribution that disappear after summing all
fibers. This is the first concrete reason to carry both a scalar channel and a
local Green/boundary channel into an elliptic-congruence atlas.

The composite-camera checks also support the proposed architecture:

\[
\text{all bases}
\longrightarrow
\text{coprime factorization}
\longrightarrow
\text{prime-power local cameras}.
\]

This is finite evidence, not yet a theorem inside the carry formalizations.

## Reproduce

```bash
python3 experiments/elliptic_congruence_camera.py
python3 -m unittest experiments.test_elliptic_congruence_camera
```

The script writes
`experiments/results/elliptic_congruence_camera_gate1.json` deterministically.

## Next gate

Gate 2 should replace a single curve with a finite curve family and test whether
three signals agree:

1. singular residues of the chosen integral model;
2. nonzero local lift-fiber energy;
3. support inherited by composite cameras through coprime factorization.

A positive result would justify a minimal Lean layer for finite congruence
states, reduction fibers, and the exact CRT product identity. It would still
not justify importing any elliptic \(L\)-function semantics.
