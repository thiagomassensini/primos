# C3 carrier-compensation gate

## Result

The complete-center tilt analysis removes one possible cancellation mechanism:
away from the half-abscissa, the tail of all later C3 tilt centers cannot
cancel the first complete center. The remaining scalar ledger is now exact.

For a parameter `s` in the open Genuine strip with
`Re(s) != 1 / 2`, write

```math
W_\infty(s)=\sum_{k\ge 0}W_k(s)
```

for the complete weighted-tilt trace and

```math
R_\infty(s)=\sum_{k\ge 0}R_k(s)
```

for the critical-carrier remainder. Lean proves, without assuming a zero,

```math
\boxed{
R_\infty(s)
=a_3(s)\,\mathrm{Genuine}(s)-1-W_\infty(s).
}
```

Equivalently,

```math
\boxed{
1+W_\infty(s)+R_\infty(s)
=a_3(s)\,\mathrm{Genuine}(s).
}
```

The chart factor `a_3(s)` is nonzero throughout the strip. Therefore

```math
\boxed{
1+R_\infty(s)=-W_\infty(s)
\quad\Longleftrightarrow\quad
\mathrm{Genuine}(s)=0.
}
```

This is the exact carrier-compensation gate.

## What is already coercive

Let `W_0(s)` denote the first complete tilt center. The explicit tail ratio

```math
\rho=\frac34\left(\frac65\right)^{3/2}<1
```

gives more than `W_infinity(s) != 0`. Lean proves the directional estimate

```math
\boxed{
\mathrm{Re}
\left(\overline{W_0(s)}\,W_\infty(s)\right)>0.
}
```

Thus all later complete tilt centers leave the total tilt in the strict open
half-plane selected by the first center. Neither raw phase oscillation nor the
complete tilt tail can erase the central defect.

## Why the carrier is different

For the center `c_k`, the carrier remainder has the universal block formula

```math
R_k(s)=
\bigl(g(c_k-1)-g(c_k)\bigr)h(c_k-1)
+\bigl(g(c_k+1)-g(c_k)\bigr)h(c_k+1).
```

It is made of complex carrier increments along the two legs. Complete-cell
bookkeeping preserves these terms but does not give them a scalar sign or make
them orthogonal to the tilt.

Indeed, Lean already has a complete-cell witness at `s = 0`: the cell with
center `3` and legs `2` and `4` has zero full bracket, nonzero tilt, and carrier
remainder exactly equal to the negative tilt. This boundary witness does not
assert an off-critical zero in the open strip; it shows that cell completeness
alone cannot prove carrier orthogonality.

## Exact logical strength

Define global carrier/seed noncompensation to mean

```math
1+R_\infty(s)\ne-W_\infty(s)
```

for every off-critical `s` in the strip. Lean proves

```math
\boxed{
\text{global carrier/seed noncompensation}
\quad\Longleftrightarrow\quad
\text{Genuine strong nonvanishing in the strip}.
}
```

Consequently this statement is the remaining global theorem itself at the
level of the scalar ledger. It cannot be obtained merely by deleting a cutoff
tail, multiplying by the nonzero `C0` factor, or re-associating that scalar
identity.

This does **not** mean that the carrier is a free compensating variable in the
full geometry. Endpoint, carrier, bulk, Green boundary data and Weyl output
are supposed to be readings of the same state and are tied by exact
reconstruction identities. The structurally faithful route is therefore to
compose those exact identities in one carrier and prove

```text
coherent state + zero port
  -> reconstructed bulk is zero
  -> structural defect energy is zero.
```

The half-abscissa then appears only in the already-proved final equivalence
`structural defect energy = 0 <-> Re(s) = 1 / 2`. It is not inserted as a zero
hypothesis. What the scalar scope guard establishes is only that this
state-level coherence cannot be replaced by a scalar sign argument.

## Failed scalar sign shortcut

The most direct missing estimate would try to put the seed-plus-carrier in the
same half-plane as the first tilt center. Numerical checks disprove that
universal sign: the projection

```math
\mathrm{Re}
\left(\overline{W_0(s)}\,[1+R_\infty(s)]\right)
```

changes sign in the strip, including transversally near known critical zeros.
Multiplying both channels by the same nonzero dressing, such as `C0`, only
multiplies this projection by a positive squared modulus and cannot repair the
sign.

The next viable target must therefore retain the exact reflected/state-level
carrier, endpoint and reconstructed bulk rather than use a fixed scalar
projection or an asymptotic substitute.

## Lean declarations

The implementation is in
[`CpGenuineCarrierCompensationGate.lean`](../CPFormal/Analytic/CpGenuineCarrierCompensationGate.lean).
Its public declarations are:

```lean
re_conj_mul_ge_neg_norm_mul
canonicalCriticalWeightedTiltTrace_firstBlockProjection_pos
canonicalCriticalCarrierRemainderBlock_eq_two_leg_increment
canonicalCriticalCarrierRemainderTrace_closed_form
one_add_canonicalCriticalCarrierRemainderTrace_closed_form
seed_add_infiniteTilt_add_carrier_eq_factor_mul_genuine
carrierSeed_cancels_infiniteTilt_iff_genuine_zero
CarrierSeedDoesNotCancelInfiniteTiltOffCritical
carrierSeedDoesNotCancelInfiniteTiltOffCritical_iff_strongNonvanishing
```
