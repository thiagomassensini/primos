# Elliptic congruence camera — Gate 5 intrinsic fiber

## Status

**Kernel-checked identification of raw Taylor increments with the intrinsic
prime-power reduction fiber of the affine congruence-state tower.**

This gate removes the remaining dependence of the local lift theorem on chosen
integer coordinates.  It proves that the coordinate fiber from Gate 4 is
canonically equivalent to the actual `MapFiber` of

```text
AffineCongruenceState (p^(k+1)) a b
  -> AffineCongruenceState (p^k) a b.
```

It then transfers the `p / 0 / p^2` trichotomy and the singular-support theorem
directly to that intrinsic reduction fiber.

## 1. One coordinate is target plus one digit

`CPFormal/Elliptic/PrimePowerReductionFiber.lean` constructs the mixed-radix
equivalence

```text
ZMod (p^k) × ZMod p ≃ ZMod (p^(k+1)).
```

The corresponding value is

```text
target + p^k * digit,
```

and canonical reduction sends it back to `target`.

The file also treats an arbitrary integral representative `x` of the target
coordinate and proves an equivalence

```text
ZMod p ≃
MapFiber
  (ZMod (p^(k+1)) -> ZMod (p^k))
  (x mod p^k).
```

The map sends a digit `u` to

```text
x + p^k * u mod p^(k+1).
```

Injectivity and surjectivity are both proved.  Thus one coordinate fiber has
exactly one intrinsic digit, rather than merely the correct cardinality.

## 2. Raw affine lifts equal the actual affine reduction fiber

`CPFormal/Elliptic/PrimePowerAffineFiber.lean` combines the two coordinate
fibers with the short-Weierstrass equation.

For integral representatives `(x,y)` of a target state modulo `p^k`, it
constructs

```text
RawWeierstrassLiftFiber p k a b x y ≃
MapFiber
  (affineCongruenceStateReduction (p^k | p^(k+1)) a b)
  target.
```

The forward map uses the same raw point from Gate 4:

```text
(x + p^k*u, y + p^k*v) mod p^(k+1).
```

The inverse extracts the unique digit in each coordinate fiber.  The source
state already satisfies the curve equation, so those digits satisfy the raw
Taylor divisibility predicate automatically.

This is an equivalence of finite types, not only equality of cardinalities.

## 3. Independence from integral representatives

Suppose `(x,y)` and `(x',y')` represent the same target state modulo `p^k`.
Both raw increment fibers are identified with the same intrinsic `MapFiber`.
Composing one equivalence with the inverse of the other gives

```text
RawWeierstrassLiftFiber p k a b x y ≃
RawWeierstrassLiftFiber p k a b x' y'.
```

Therefore the coordinate chart does not define a new lift notion.  It is a
presentation of the existing reduction fiber.

## 4. Canonical chart and exact residual quotient

`CPFormal/Elliptic/PrimePowerIntrinsicFiber.lean` chooses the canonical integer
representatives of the target coordinates only to obtain an exact witness

```text
F(x,y) = p^k * c.
```

The quotient `c` is introduced with `Classical.choose` from a proved
divisibility theorem.  No integer division hides a premise.

The canonical raw fiber is then identified with the intrinsic reduction fiber.
Because representative independence was already proved, this choice is an
auxiliary chart and not part of the final statement.

## 5. Intrinsic cardinality trichotomy

For prime `p`, positive depth `k >= 1`, and every target affine state modulo
`p^k`, the theorem

```text
card_primePowerAffineReductionFiber_trichotomy
```

proves

```text
#MapFiber = p, 0, or p^2.
```

The fiber here is the actual state-reduction fiber, not a separately defined
coordinate proxy.

## 6. Intrinsic singular support

The theorem

```text
card_primePowerAffineReductionFiber_ne_expected_iff_singular
```

proves

```text
#MapFiber != p
  <->
the target state reduced modulo p has zero affine gradient.
```

For

```text
y^2 = x^3 + a*x + b,
```

the gradient is

```text
Fx = -3*x^2 - a,
Fy = 2*y.
```

Thus the defect support observed by the finite camera is now attached directly
to the intrinsic prime-power tower:

```text
regular prime reduction -> exactly p lifts;
singular prime reduction -> 0 or p^2 lifts.
```

The residual quotient decides which exceptional cardinality occurs, while the
vanishing gradient decides where exceptional fibers can occur.

## Kernel-checked in Gate 5

- mixed-radix decomposition `target × digit ≃ source` for one coordinate;
- compatibility of that decomposition with canonical reduction;
- bijection between one digit and a coordinate reduction fiber;
- equivalence between the raw Taylor fiber and the affine-state `MapFiber`;
- independence from chosen integral representatives;
- divisibility of the canonical integral residual by `p^k`;
- exact canonical residual quotient identity;
- intrinsic `p / 0 / p^2` fiber trichotomy;
- intrinsic non-regular-support iff singular-prime-reduction theorem.

## Evidence boundary

This gate still concerns the displayed affine short-Weierstrass integral model.
It does not yet prove:

- the universal equivalence between discriminant divisibility and the
  existence of singular affine residue states for every relevant prime;
- covariance under admissible Weierstrass coordinate changes;
- invariance under minimal-model replacement;
- projective completion or the elliptic group law;
- Mordell–Weil rank, Selmer groups, BSD, elliptic L-functions or zero transfer.

## Reproduce

```bash
lake build --wfail \
  CPFormal.Elliptic.PrimePowerReductionFiber \
  CPFormal.Elliptic.PrimePowerAffineFiber \
  CPFormal.Elliptic.PrimePowerIntrinsicFiber

lake build --wfail CPFormal
```

## Next formal gate

The next local theorem justified by the experiments is the discriminant bridge
for the displayed short-Weierstrass model:

```text
p divides Delta
  <->
there exists a singular affine state modulo p
  <->
there exists a non-regular intrinsic prime-power reduction fiber.
```

That theorem would identify the support detected by the intrinsic lift energy
with the classical bad-reduction support, while still remaining entirely local
and finite.