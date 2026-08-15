# C3 tilt-tail noncompensation

## Scope

This note records a quantitative result about the canonical C3 tilt channel.
It proves that, away from the half-abscissa, the complete tail of later tilt
centers cannot cancel the first tilt center. It does not prove that the full
Genuine bracket is nonzero, because the exact product-rule ledger also
contains the seed and a separate critical-carrier remainder.

No zero hypothesis is used in the noncompensation theorem.

## Complete C3 cutoffs

The canonical C3 geometry is indexed by complete centers

```math
c_k=3(k+1), \qquad k=0,1,2,\ldots
```

Each center is evaluated together with both radius-one legs:

```math
c_k-1,\qquad c_k,\qquad c_k+1.
```

A cutoff with `M` centers retains the complete cells with
`k = 0, ..., M - 1`. Its analytic tail begins with the next complete center
`k = M`; it does not begin at an arbitrary raw integer and never retains a
dangling leg.

For

```math
\delta=\mathrm{Re}(s)-\frac12,
```

the phase-bearing weighted tilt block is

```math
W_k(s)=C_k(s)\,\Theta_\delta(c_k),
```

where

```math
C_k(s)=c_k^{-1/2-i\mathrm{Im}(s)}
```

is the nonzero critical carrier and `Theta` is the complete symmetric C3
tilt. The height contributes only phase:

```math
\lVert C_k(s)\rVert=c_k^{-1/2}.
```

## Explicit domination constant

Define

```math
\rho=\frac34\left(\frac65\right)^{3/2}.
```

Lean proves the exact identity

```math
\rho^2=\frac{243}{250}<1,
```

and consequently

```math
0<\rho<1.
```

The proof uses the elementary finite majorant

```math
\sum_{k=0}^{M-1}(k+2)^{-2}\le \frac34
```

together with the sharp local C3 tilt bounds. If `s` lies in the open
Genuine strip and `Re(s) != 1/2`, let `L(s) > 0` be the common first-block
scale named `canonicalTiltFirstScale` in Lean. Then, for every finite cutoff,

```math
\sum_{k=0}^{M-1}\lVert W_{k+1}(s)\rVert
\le \rho L(s)
<L(s)
\le \lVert W_0(s)\rVert.
```

Thus the first complete tilt block strictly dominates the full norm budget
of every finite later-center tail. The same estimate passes to the infinite
tail:

```math
\left\lVert\sum_{k\ge0}W_{k+1}(s)\right\rVert
<\lVert W_0(s)\rVert.
```

The reverse triangle inequality therefore gives the cofinal conclusion

```math
\boxed{
\sum_{k\ge0}W_k(s)\ne0
\quad\text{when}\quad
0<\mathrm{Re}(s)<1,
\ \mathrm{Re}(s)\ne\frac12.
}
```

This eliminates phase autocancellation between the first weighted tilt block
and the complete tail of all later weighted tilt blocks.

## What the theorem does not eliminate

The exact local product rule is

```math
B_k(s)=W_k(s)+R_k(s),
```

where `B_k` is the full Genuine bracket cell and `R_k` is the independently
defined critical-carrier curvature and cross-term remainder. At the level of
the complete chart, the seed is another separate coordinate. Hence scalar
Genuine vanishing supplies a relation of the form

```math
\text{seed}
+\sum_{k\ge0}W_k(s)
+\sum_{k\ge0}R_k(s)
=0.
```

The new theorem shows that the middle term is nonzero off the half-abscissa.
It does not show that the seed and carrier remainder cannot cancel that term.
Such a conclusion would require an additional directional, orthogonality, or
coercive estimate relating those independently retained channels.

Lean also records the resulting ledger exactly. If an off-critical Genuine
zero were supplied, then necessarily

```math
R_\infty(s)=-1-W_\infty(s),
\qquad W_\infty(s)\ne0.
```

Thus the later tilt centers have been removed from the ambiguity: the only
remaining scalar mechanism is exact nonlocal compensation by the carrier
remainder together with the seed. This conditional identity does not assert
that such a zero exists.

## Complete-cell carrier witness

There is an exact finite witness showing why the carrier remainder cannot be
discarded by algebra alone. Take the first complete C3 cell, with center `3`
and legs `2` and `4`, at `s = 0`. The full Dirichlet profile is constant, so

```math
B_0(0)=1-2+1=0.
```

The transverse displacement is `delta = -1/2`, and its complete tilt is

```math
\Theta_{-1/2}(3)=\sqrt2+2-2\sqrt3\ne0.
```

The critical carrier is nonzero. Therefore

```math
W_0(0)\ne0,
\qquad
R_0(0)=-W_0(0).
```

This is a complete center with both legs present, not an artifact of an
incomplete cutoff. The parameter `s = 0` lies on the boundary of the open
Genuine strip, so this witness is not an off-critical Genuine zero in the
strip. Its role is narrower: it refutes any universal algebraic rule claiming
that a complete scalar bracket cannot contain carrier cancellation.

## Orthogonal enriched ledger

The downstream enriched C3 crosswalk retains three real coordinates:

```math
J_M(s)=
\bigl(
\tau\,\mathrm{Re}\,D_M(s),
\tau\,\mathrm{Im}\,D_M(s),
E(s)\,\mathrm{branchDefect}(s)
\bigr),
```

where `D_M` is the exact tail-completed Genuine defect, `tau` is a nonzero
transfer coefficient, and `E(s)` is the strictly positive reflected Green
energy. Its norm satisfies the exact Pythagorean identity

```math
\lVert J_M(s)\rVert^2
=\tau^2\lVert D_M(s)\rVert^2
+\bigl(E(s)\,\mathrm{branchDefect}(s)\bigr)^2.
```

There is no cancellation between these orthogonal coordinates. In the open
strip, scalar Genuine vanishing makes `D_M(s) = 0`, so it annihilates the
first two coordinates. It does not, by itself, annihilate the third:

```math
\mathrm{Genuine}(s)=0
\quad\Longrightarrow\quad
\lVert J_M(s)\rVert^2
=\bigl(E(s)\,\mathrm{branchDefect}(s)\bigr)^2.
```

Thus the enriched ledger proves genuine noncompensation once all three
coordinates are retained. The still-unproved implication is that scalar
Genuine vanishing must close the entire enriched ledger. That implication is
not supplied by the tilt-tail estimate.

## Logical conclusion

The formal result closes one precise gate:

```text
complete later-center tilt tail cannot cancel the first weighted tilt block.
```

It leaves a separate gate open:

```text
seed plus critical-carrier remainder cannot cancel the nonzero tilt trace.
```

Accordingly, this module proves a new quantitative noncompensation theorem
for the tilt channel but makes no claim of global zero confinement.

## Public Lean declarations

The implementation is in
[`CpGenuineTiltTailNoncompensation.lean`](../CPFormal/Analytic/CpGenuineTiltTailNoncompensation.lean).
Its principal declarations are:

```lean
invSq_add_two_le_three_quarters
canonicalTiltTailRatio
canonicalTiltTailRatio_sq
canonicalTiltTailRatio_lt_one
canonicalTilt_ratio_kernel_bound
canonicalTilt_upperEnvelope_factorization
canonicalTiltFirstScale
canonicalTiltFirstScale_pos
norm_canonicalCriticalWeightedTiltBlock_succ_le_scale
finiteCanonicalCriticalWeightedTiltTailNorm_le_ratio_scale
canonicalCriticalTiltFirstBlockDominates_of_strip_offCritical
summable_norm_canonicalCriticalWeightedTiltBlock_tail
summable_canonicalCriticalWeightedTiltBlock
canonicalCriticalWeightedTiltTrace
norm_canonicalCriticalWeightedTiltTrace_tail_le
canonicalCriticalWeightedTiltTrace_ne_zero_of_strip_offCritical
canonicalCriticalWeightedTiltTrace_ne_zero
summable_canonicalCriticalCarrierRemainderBlock
canonicalCriticalCarrierRemainderTrace
canonicalBracketTrace_eq_infiniteTilt_add_carrier
carrierRemainder_eq_neg_one_sub_infiniteTilt_of_genuine_zero_offCritical
completeC3Cell_zero_at_s_zero
completeC3Cell_weightedTilt_ne_zero_at_s_zero
completeC3Cell_carrierRemainder_eq_neg_weightedTilt_at_s_zero
```

The exact product-rule declaration used to delimit the result is:

```lean
realCpSaturatedBracket_three_eq_weightedTilt_add_carrierRemainder
```

The enriched orthogonal identity is maintained downstream as
`c3EnrichedTailBranchCompletedReadout_norm_sq`.
