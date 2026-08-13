# Elliptic congruence camera — Gate 2

## Status

**Experimental finite arithmetic. Not kernel-checked.**

Gate 2 replaces the single curve from Gate 1 with a finite family of affine
short Weierstrass models

\[
E_{a,b}:\qquad y^2=x^3+a x+b
\]

and tests prime cameras

\[
p\in\{5,7,11,13,17,19,23,29,31\}.
\]

The restriction \(p\ge5\) keeps the short Weierstrass gradient in its ordinary
form. This gate does not construct the projective group law, rank, Selmer data,
BSD data, an elliptic \(L\)-function, or a zero-transfer theorem.

## Exact local lift law tested

Let

\[
F(x,y)=y^2-x^3-a x-b
\]

and let \(P=(x,y)\) be a point modulo \(p^k\). Every candidate lift has the form

\[
P+p^k(u,v),
\qquad
u,v\in\mathbb F_p.
\]

Modulo \(p^{k+1}\), the higher-order terms vanish and the lift condition is

\[
\frac{F(P)}{p^k}
+uF_x(P)+vF_y(P)
\equiv0\pmod p.
\]

The finite predictor used by the gate is therefore:

- if \((F_x,F_y)\not\equiv(0,0)\pmod p\), the fiber has exactly \(p\) lifts;
- if \((F_x,F_y)\equiv(0,0)\pmod p\), the fiber has either \(0\) or \(p^2\)
  lifts, according to the residual quotient.

The brute-force lift engine and this linearized predictor agree for every
tested point at the first level and, whenever the reduction is singular, at
the second level as well.

Consequently, on the tested prime cameras, the support of the nonzero fiber
defect

\[
\delta_{p,k}(P)
=
\#\pi_{p,k}^{-1}(P)-p
\]

is exactly the singular support. The quadratic energy is

\[
\mathcal E_{p,k}
=
\sum_P\delta_{p,k}(P)^2.
\]

## Curve family and prime-camera result

| Curve id | Affine equation | Discriminant | Detected bad prime signatures |
|---|---|---:|---|
| `control_2_3_only` | \(y^2=x^3+1\) | \(-432=-2^4 3^3\) | none on the tested grid |
| `single_bad_5` | \(y^2=x^3-2x-1\) | \(80=2^4 5\) | \(p=5:\ 25\to0\) |
| `single_bad_23` | \(y^2=x^3-x+1\) | \(-368=-2^4 23\) | \(p=23:\ 529\to0\) |
| `two_bad_13_19` | \(y^2=x^3+x-3\) | \(-3952=-2^4 13\cdot19\) | \(p=13:\ 169\to0;\ p=19:\ 361\to0\) |
| `two_bad_5_7` | \(y^2=x^3+2x-2\) | \(-2240=-2^6 5\cdot7\) | \(p=5:\ 25\to0;\ p=7:\ 49\to0\) |
| `persistent_bad_5` | \(y^2=x^3+2x-3\) | \(-4400=-2^4 5^2 11\) | \(p=5:\ 400\to2875;\ p=11:\ 121\to0\) |

Here \(E_1\to E_2\) denotes the first and second lift-fiber energies.

Across all 54 curve/prime cases, the gate verifies the finite equivalence

\[
p\mid\Delta
\quad\Longleftrightarrow\quad
\text{a singular affine residue exists modulo }p
\quad\Longleftrightarrow\quad
\mathcal E_{p,1}>0.
\]

The finite family contains both singular fiber types:

- a **dead singular fiber**, with \(0\) lifts;
- an **excess singular fiber**, with \(p^2\) lifts.

It also exposes two depth signatures:

### Transient boundary pulse

For every tested bad prime with \(v_p(\Delta)=1\), the first energy is nonzero
and the second energy is zero. The singular branch creates a finite boundary
defect and the surviving tower becomes regular at the next tested depth.

### Persistent local redistribution

For

\[
y^2=x^3+2x-3
\quad\text{at}\quad p=5,
\]

the discriminant has \(v_5(\Delta)=2\). The singular first fiber has \(25\)
lifts rather than \(5\), and

\[
\mathcal E_{5,1}=400,
\qquad
\mathcal E_{5,2}=2875.
\]

Thus the local quadratic channel separates a one-level singular pulse from a
defect that remains active deeper in the congruence tower.

This is finite evidence from the selected family. It is not yet a theorem that
the discriminant valuation alone determines the entire depth signature.

## Exact CRT inheritance

For coprime bases \(a,b\), Gate 2 checks pointwise

\[
L_{ab}(P_a,P_b)
=
L_a(P_a)L_b(P_b),
\]

where \(L_q(P)\) is the lift-fiber size in camera \(q\).

It then checks three consequences directly against the composite-camera
enumeration:

1. point counts factor;
2. defective support is inherited from the union of the two component
   supports;
3. quadratic energy agrees with the product-profile prediction

\[
\mathcal E_{ab}
=
\sum_{P_a,P_b}
\left(
L_a(P_a)L_b(P_b)-ab
\right)^2.
\]

The tested composite energies are:

| Curve id | Composite camera | Direct energy | Product prediction |
|---|---:|---:|---:|
| `control_2_3_only` | \(5\cdot7=35\) | \(0\) | \(0\) |
| `single_bad_5` | \(5\cdot7=35\) | \(3675\) | \(3675\) |
| `single_bad_23` | \(23\cdot5=115\) | \(92575\) | \(92575\) |
| `two_bad_13_19` | \(13\cdot5=65\) | \(12675\) | \(12675\) |
| `two_bad_5_7` | \(5\cdot7=35\) | \(13475\) | \(13475\) |
| `persistent_bad_5` | \(5\cdot7=35\) | \(176400\) | \(176400\) |
| `persistent_bad_5` | \(11\cdot7=77\) | \(53361\) | \(53361\) |

When one component camera \(b\) is regular, the checked identity reduces to

\[
\mathcal E_{ab}
=
\#X_b\;b^2\mathcal E_a.
\]

For the bad-bad camera \(5\cdot7\) on `two_bad_5_7`, the defective support has
exactly \(11\) points, equal to the union count predicted from the two local
supports, and the full product energy is \(13475\).

This strengthens the all-bases architecture:

\[
\text{all modular cameras}
\longrightarrow
\text{exact coprime factorization}
\longrightarrow
\text{prime-power local defect channels}.
\]

## Evidence

Gate 2 contains:

- exhaustive finite enumeration of all declared fibers;
- an independent first-order predictor for every tested lift;
- nine unit tests with exact expected values;
- deterministic JSON ledger generation;
- a dedicated GitHub Actions job.

It contains no new Lean declaration and makes no kernel-checked elliptic claim.

## Reproduce

```bash
python3 -m unittest -v \
  experiments.test_elliptic_congruence_camera_family

python3 -m experiments.elliptic_congruence_camera_family \
  --output /tmp/elliptic_congruence_camera_gate2.json
```

## Boundary before formalization

The current signal belongs to the chosen integral affine model. Before treating
it as an invariant of an elliptic curve rather than an invariant of a displayed
equation, a later gate must test covariance under admissible changes of
Weierstrass coordinates and compare minimal and nonminimal models.

## Next formal gate

The smallest justified Lean layer is now:

1. the exact linearized lift-count trichotomy \(p,\ 0,\ p^2\);
2. equality of defective and singular support for prime cameras;
3. the CRT product identity for congruence states and lift fibers;
4. the induced composite quadratic-energy formula.

Only after those finite identities are kernel-checked should the project add
projective completion, group structure, or any global arithmetic semantics.
