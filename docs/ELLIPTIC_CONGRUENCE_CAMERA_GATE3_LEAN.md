# Elliptic congruence camera — Gate 3 Lean

## Status

**Kernel-checked finite layer for the linearized local camera, coprime affine
states, reduction fibers and quadratic product energy.**

This gate formalizes the finite algebra isolated by Gates 1 and 2.  It does not
upgrade the experimental curve-family ledger into a theorem about every
integral model, and it does not assert rank, Selmer, BSD, elliptic L-functions
or zero transfer.

The public root `CPFormal.lean` imports all modules listed below.

## 1. Linearized local lift equation

For a prime `p`, residual quotient `c : ZMod p` and gradient coordinates
`gx, gy : ZMod p`, define

```text
LinearizedLiftFiber p c gx gy
  = {(u,v) : ZMod p × ZMod p | c + u*gx + v*gy = 0}.
```

`CPFormal/Elliptic/LinearizedLift.lean` proves:

```text
card = p, 0, or p^2;
```

```text
gradient nonzero  -> card = p;
gradient zero and c = 0 -> card = p^2;
gradient zero and c != 0 -> card = 0;
```

and the exact support statement

```text
card != p <-> gx = 0 and gy = 0.
```

The proof uses explicit equivalences when either gradient coordinate is
nonzero.  No counting oracle or imported elliptic theorem is used.

## 2. Short-Weierstrass singular support

For the displayed affine model

```text
y^2 = x^3 + a*x + b,
```

`CPFormal/Elliptic/WeierstrassLinearizedLift.lean` specializes

```text
Fx = -3*x^2 - a,
Fy =  2*y.
```

It defines a singular affine state by `Fx = 0` and `Fy = 0`, and proves

```text
linearized fiber card != p
  <-> the affine state has zero gradient.
```

Thus the residual quotient selects between the exceptional cardinalities
`0` and `p^2`, but it does not change the support of the defect.

This is a theorem about the linearized lift equation.  The integer Taylor
bridge identifying every raw lift modulo `p^(k+1)` with this equation remains a
separate obligation.

## 3. Coprime affine-state factorization

`CPFormal/Elliptic/CoprimeState.lean` defines the affine congruence state

```text
AffineCongruenceState modulus a b
  = {(x,y) in ZMod modulus × ZMod modulus |
       y^2 - (x^3 + a*x + b) = 0}.
```

For coprime `m,n`, it proves the coordinatewise Chinese-remainder equivalence

```text
AffineCongruenceState (m*n) a b
  ≃ AffineCongruenceState m a b × AffineCongruenceState n a b,
```

and the induced exact factorization of finite state counts.

## 4. Exact reduction-fiber factorization

`CPFormal/Elliptic/ProductFiber.lean` proves two abstract finite facts:

1. a commuting square with equivalences on source and target transports
   fibers;
2. the fiber of a product map is equivalent to the product of the component
   fibers.

`CPFormal/Elliptic/ReductionFiber.lean` applies those facts to canonical
`ZMod.castHom` reductions.  The CRT state equivalences commute with reduction,
so every composite affine reduction fiber is canonically equivalent to the
product of its two local reduction fibers.  Consequently,

```text
#Fiber_(mn)(P_m,P_n)
  = #Fiber_m(P_m) * #Fiber_n(P_n)
```

for the formal coprime reduction square.

## 5. Quadratic product energy

`CPFormal/Elliptic/ProductEnergy.lean` defines

```text
defect(expected,count) = count - expected,
energy = sum defect^2.
```

For product profiles it proves the exact double-sum formula.  When the right
camera is regular with fiber size `b`, it proves

```text
E_(ab) = card(X_b) * b^2 * E_a,
```

with the symmetric theorem when the left camera is regular.

This formalizes the composite-camera scaling observed in Gate 2 without
hard-coding any experimental value.

## Evidence boundary

### Kernel-checked in Gate 3

- local cardinality trichotomy `p / 0 / p^2`;
- non-regular linearized support equals zero-gradient support;
- specialization to the displayed short-Weierstrass gradient;
- CRT equivalence of affine congruence states;
- exact product factorization of reduction fibers;
- exact product-energy formula and one-regular-camera scaling laws.

### Still outside this gate

- the raw integer Taylor bridge from actual lifts modulo `p^k` and
  `p^(k+1)` to the linearized equation;
- a universal theorem relating discriminant divisibility to singular affine
  support for every displayed model;
- covariance under admissible Weierstrass coordinate changes;
- minimal versus nonminimal models;
- projective completion and the group law;
- rank, Selmer groups, BSD, elliptic L-functions or zero transfer.

## Reproduce

```bash
lake build --wfail \
  CPFormal.Elliptic.LinearizedLift \
  CPFormal.Elliptic.WeierstrassLinearizedLift \
  CPFormal.Elliptic.ProductFiber \
  CPFormal.Elliptic.ProductEnergy \
  CPFormal.Elliptic.CoprimeState \
  CPFormal.Elliptic.ReductionFiber

lake build --wfail CPFormal
```

## Next formal gate

The next justified theorem is the integer first-order expansion for a raw
candidate lift

```text
(x + p^k*u, y + p^k*v)
```

modulo `p^(k+1)`, proving that its Weierstrass residual vanishes exactly when

```text
F(x,y)/p^k + u*Fx(x,y) + v*Fy(x,y) = 0 mod p.
```

Once that bridge is kernel-checked, the linearized support theorem becomes an
exact theorem about the actual reduction fibers measured by the Python gates.
