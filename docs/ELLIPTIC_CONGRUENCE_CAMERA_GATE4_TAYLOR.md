# Elliptic congruence camera — Gate 4 Taylor bridge

## Status

**Kernel-checked integral first-order bridge from raw affine lifts to the
linearized local fiber.**

This gate closes the principal arithmetic obligation left by Gate 3.  It proves
an exact polynomial identity over `ℤ`, specializes it to shifts by `p^k`, and
identifies the resulting raw increment fiber with the previously formalized
linearized lift fiber over `ZMod p`.

The public root `CPFormal.lean` imports
`CPFormal/Elliptic/RawLiftTaylor.lean`.

## 1. Integral residual and gradient

For the displayed short-Weierstrass equation

```text
y^2 = x^3 + a*x + b,
```

define the integral residual

```text
F(x,y) = y^2 - (x^3 + a*x + b).
```

Its integral gradient coordinates are

```text
Fx(x,y) = -3*x^2 - a,
Fy(x,y) =  2*y.
```

The first-order directional term in an increment `(u,v)` is

```text
L(x,y;u,v) = u*Fx(x,y) + v*Fy(x,y).
```

## 2. Exact polynomial expansion

`shortWeierstrassResidualInt_taylor` proves the identity

```text
F(x + h*u, y + h*v)
  = F(x,y)
    + h * L(x,y;u,v)
    + h^2 * (v^2 - 3*x*u^2 - h*u^3).
```

This is an equality in `ℤ`.  It is not an asymptotic expansion, an analytic
approximation, or a statement with an omitted remainder.

## 3. Raw lift condition modulo `p^(k+1)`

Assume

```text
k >= 1,
p != 0,
F(x,y) = p^k * c.
```

Then `shortWeierstrassRawLift_dvd_iff` proves

```text
p^(k+1) divides F(x + p^k*u, y + p^k*v)
  iff
p divides c + L(x,y;u,v).
```

The reason is explicit in the formal proof.  The higher-order block contains
`p^(2k)`, and `k >= 1` implies that it is divisible by `p^(k+1)`.

The residual quotient `c` is supplied together with the exact equality

```text
F(x,y) = p^k * c.
```

No integer division is used to conceal the required divisibility of the base
residual.

## 4. Canonical raw increment fiber

For canonical increment representatives in `ZMod p`, define

```text
RawWeierstrassLiftFiber p k a b x y
```

as the subtype of pairs `(u,v) : ZMod p × ZMod p` for which

```text
F(x + p^k*u, y + p^k*v) = 0 mod p^(k+1).
```

Here the residue classes are converted to their canonical integer
representatives through `ZMod.cast`.

`linearizedEquation_zmod_iff_dvd` proves that the residue-ring equation

```text
c + u*Fx + v*Fy = 0 in ZMod p
```

is exactly the corresponding divisibility statement in `ℤ`.

## 5. Raw fiber equals linearized fiber

`rawWeierstrassLiftFiberEquivLinearized` constructs a canonical equivalence

```text
RawWeierstrassLiftFiber p k a b x y
  ≃
LinearizedLiftFiber p c Fx Fy.
```

The equivalence is the identity on the increment pair `(u,v)`.  Only the
certified predicate is transported using the exact Taylor divisibility theorem.
Thus this is stronger than equality of cardinalities.

The specialized theorem

```text
rawWeierstrassLiftFiberEquivWeierstrassLinearized
```

packages the target as the short-Weierstrass linearized fiber attached to the
reduced affine state modulo `p`.

## 6. Consequences transferred to actual raw increments

The earlier linearized trichotomy now transfers to the raw increment fiber:

```text
card RawWeierstrassLiftFiber = p, 0, or p^2.
```

More precisely,

```text
card RawWeierstrassLiftFiber != p
  iff
its reduced affine state has zero gradient.
```

Therefore the finite singular-support theorem is no longer confined to an
abstract first-order equation.  It applies to the explicitly parametrized raw
lifts from depth `k` to depth `k+1`.

## Evidence boundary

### Kernel-checked in Gate 4

- the exact integral polynomial expansion;
- divisibility of the higher-order remainder modulo `p^(k+1)` for `k >= 1`;
- equivalence of the raw lift condition and the linearized equation;
- canonical equivalence of raw and linearized increment fibers;
- transfer of the `p / 0 / p^2` trichotomy to raw increments;
- transfer of singular-gradient support to raw fiber defects.

### Still outside this gate

- packaging the theorem directly as an equivalence with the existing
  `MapFiber` of reduction between affine congruence-state types modulo `p^(k+1)`
  and `p^k`;
- proof that the construction is independent of the chosen integral
  representative of a state modulo `p^k`;
- a universal discriminant/singular-support theorem for every displayed
  integral model;
- covariance under admissible Weierstrass coordinate changes;
- minimal versus nonminimal models;
- projective completion and the group law;
- rank, Selmer groups, BSD, elliptic L-functions or zero transfer.

## Reproduce

```bash
lake build --wfail CPFormal.Elliptic.RawLiftTaylor
lake build --wfail CPFormal
```

## Next formal gate

The next exact bridge is to identify

```text
RawWeierstrassLiftFiber p k a b x y
```

with the existing reduction fiber

```text
MapFiber
  (affineCongruenceStateReduction ...)
  target
```

for prime-power levels.  That theorem should include representative
independence, so the raw increment description becomes an intrinsic statement
about the affine congruence-state tower rather than a statement tied to one
chosen integer lift of the base residue class.
