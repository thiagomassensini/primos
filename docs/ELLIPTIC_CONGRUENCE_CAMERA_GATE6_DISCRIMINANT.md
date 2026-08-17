# Elliptic congruence camera — Gate 6 discriminant bridge

## Status

**Kernel-checked identification of the discriminant support with singular affine
support and with the first non-regular intrinsic prime-power reduction fiber.**

For the displayed integral short-Weierstrass model

```text
y^2 = x^3 + a*x + b
```

and every prime `p >= 5`, this gate proves the finite local chain

```text
p divides Delta
  <->
there exists a singular affine state modulo p
  <->
there exists a non-regular intrinsic reduction fiber from p^2 to p.
```

The final fiber is the actual `MapFiber` of the affine-state reduction map. It
is not a separately defined coordinate proxy.

## 1. Scope and discriminant

The integral discriminant used in this gate is

```text
Delta = -16 * (4*a^3 + 27*b^2).
```

The restriction `p >= 5` is structural for this proof: `2`, `3`, `-16`, and
`27` must behave as nonzero elements of `ZMod p`. Characteristics `2` and `3`
require their own Weierstrass normal forms and are not silently smuggled into a
formula whose derivation assumes those coefficients are invertible.

The file

```text
CPFormal/Elliptic/ShortWeierstrassDiscriminant.lean
```

defines both the integral discriminant and its reduced core

```text
4*a^3 + 27*b^2 mod p.
```

It first proves

```text
p divides Delta
  <->
4*a^3 + 27*b^2 = 0 in ZMod p.
```

The factor `-16` is removed only after proving that it is nonzero modulo every
prime `p >= 5`.

## 2. Singular affine state implies discriminant vanishing

For an affine state `(x,y)` modulo `p`, singularity means

```text
-3*x^2 - a = 0,
2*y = 0.
```

Since `2` is nonzero modulo `p`, the second equation gives

```text
y = 0.
```

The first equation gives

```text
a = -3*x^2.
```

Substituting these identities into the curve equation yields

```text
b = 2*x^3.
```

The discriminant core then closes exactly:

```text
4*(-3*x^2)^3 + 27*(2*x^3)^2 = 0.
```

This direction is formalized by

```text
shortWeierstrassDiscriminantCore_eq_zero_of_singular.
```

## 3. Discriminant vanishing produces a singular affine state

The converse is constructive.

### Degenerate coefficient branch

If `a = 0 mod p`, core vanishing forces

```text
27*b^2 = 0.
```

Because `27` is nonzero modulo `p`, this gives `b = 0`, and the state

```text
(0,0)
```

is singular.

### Nonzero coefficient branch

If `a != 0 mod p`, the proof chooses

```text
x = -3*b / (2*a),
y = 0.
```

The denominator is proved nonzero before cancellation. Scaled polynomial
identities derived from

```text
4*a^3 + 27*b^2 = 0
```

then prove both

```text
-3*x^2 - a = 0
```

and

```text
x^3 + a*x + b = 0.
```

Thus `(x,0)` is an affine singular state. This direction is formalized by

```text
exists_affineSingularState_of_discriminantCore_eq_zero.
```

Combining both directions gives

```text
int_dvd_shortWeierstrassDiscriminant_iff_exists_singular.
```

## 4. Intrinsic prime-square fiber

Gate 5 already proved, for every target state modulo `p^k`,

```text
#MapFiber != p
  <->
the target reduced modulo p has zero affine gradient.
```

Gate 6 applies that theorem at the first positive depth `k = 1`. The tower is
written in its structural notation as

```text
p^(1+1) -> p^1,
```

which normalizes to

```text
p^2 -> p.
```

The capstone theorem is

```text
int_dvd_shortWeierstrassDiscriminant_iff_exists_nonregular_primeSquareFiber.
```

It proves

```text
p divides Delta
  <->
there exists a target modulo p whose actual p^2-to-p reduction fiber
has cardinality different from p.
```

The witness in the forward direction is built from canonical integer
representatives of the singular point. Reduction recovers the original point
exactly. The reverse direction uses the intrinsic Gate 5 theorem to recover a
singular prime-level state and then the discriminant bridge.

## 5. What the camera now detects

The finite lift-energy support is no longer merely correlated with bad local
behavior. For primes `p >= 5` in the displayed short-Weierstrass model, the
formal support identity is

```text
discriminant support
  = singular affine support
  = non-regular intrinsic lift-fiber support.
```

Equivalently,

```text
p does not divide Delta
  -> every p^2-to-p affine-state fiber has exactly p lifts;

p divides Delta
  -> at least one p^2-to-p affine-state fiber has 0 or p^2 lifts.
```

The residual quotient still determines whether an exceptional fiber has `0`
or `p^2` points. The discriminant and the gradient determine where exceptional
fibers can exist.

## Kernel-checked in Gate 6

- nonvanishing of `2`, `3`, `-16`, and `27` modulo primes `p >= 5`;
- reduction of the integral discriminant to its core;
- discriminant divisibility iff core vanishing;
- singular affine state implies core vanishing;
- explicit construction of a singular affine state from core vanishing;
- discriminant divisibility iff existence of singular affine support;
- discriminant divisibility iff existence of a non-regular intrinsic
  `p^2 -> p` affine reduction fiber;
- public import through `CPFormal.lean`;
- focused elliptic finite gate and full `CPFormal` kernel audit.

## Evidence boundary

This gate does not yet prove:

- the corresponding characteristic `2` and characteristic `3` normal-form
  theorems;
- covariance under admissible changes of Weierstrass coordinates;
- invariance under replacement by a minimal integral model;
- projective completion or the elliptic group law;
- conductor exponents, Kodaira symbols, Tamagawa numbers, Selmer groups,
  Mordell-Weil rank, BSD, elliptic L-functions, or zero transfer.

## Reproduce

```bash
lake build --wfail \
  CPFormal.Elliptic.ShortWeierstrassDiscriminant

lake build --wfail CPFormal
```

## Next formal gate

The next finite local gate is covariance of the detected support under
admissible short-Weierstrass coordinate scaling by a unit. The first target is
to prove that, for `u` invertible modulo `p`, the transformation

```text
x = u^2*x',
y = u^3*y'
```

transports affine states, singular support, discriminant support, and intrinsic
fiber cardinalities together. After that, characteristics `2` and `3` can be
isolated using their appropriate integral normal forms instead of being treated
as malformed exceptions to the `p >= 5` argument.
