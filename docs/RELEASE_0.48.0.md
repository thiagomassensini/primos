# CPFormal v0.48.0 — Native carry complex time and Green-symmetric boundary pencil

## Scope

This release freezes the kernel-audited stack developed in pull requests #8, #9 and #10.

It reorganizes the final scalar localization problem in the native language of the carry operator:

- the carry geometry fixes the critical amplitude `n^(-1/2)`;
- real time rotates phase without changing that amplitude;
- an arbitrary complex parameter is re-expressed as complex carry time;
- the desired scalar theorem becomes the assertion that continuation does not create resonances after deforming the native amplitude;
- the characteristic parameter of the operator-theoretic realization is `z` itself, not the scalar readout `G(z)`.

The release constructs the abstract spectral gate and the concrete Green-symmetric boundary carrier needed for this program. It does not declare the remaining resonance-to-characteristic-value realization as an assumption and does not claim strong scalar non-vanishing before that construction is completed.

## Kernel-checked additions

### Connected C2, TFVD and native `G_pre` preservation

- the connected C2/Richardson defect is transported through the TFVD port;
- the full Dirichlet one-jet and log-jet prefixes are injected losslessly into enriched TFVD--`G_pre` carriers;
- tagged cofinal synthesis is identified exactly with the horizontal camera gap at every cutoff;
- scalar camera compression is proved rank one even after inserting the canonical carry amplitudes;
- an explicit diagonal camera pair has zero scalar compression and positive quadratic carry energy;
- promoting tagged scalar closure to Green closure or carry saturation is proved equivalent to the strong scalar Genuine theorem, preventing a circular activation claim.

### Native complex-time coordinates

The release defines

```text
carryComplexTimeParameter z = 1/2 + z * I
carryComplexTimeOfParameter s = s.im - criticalDisplacement(s.re) * I
```

and proves that these maps are inverse.

For the native state at complex time,

```text
||carryComplexTimeState z n|| = (n+1)^(-1/2 + z.im).
```

Consequently,

```text
NativeCarryCriticalAmplitudePreserved z <-> z.im = 0.
```

On real time, the complex-time state and readout are literally the previously formalized real-spectral orbit and `realSpectralGenuine`.

The following formulations are proved equivalent to the existing strong scalar target:

```text
NativeCarrySpectrumExhaustsGenuine
NativeCarryComplexTimeZeroRigidity
NativeCarryComplexTimeZeroPreservesCriticalAmplitude
GenuineStrongNonvanishingInStrip
```

No instance of these equivalent final scalar propositions is declared.

For the completed `Genuine ⊕ Green` operator, complex-time rigidity is unconditional: its zeros are exactly real-time native resonances with the critical amplitude preserved.

### Fixed spectral pencil with parameter `z`

For a fixed partially defined operator `A`, the release defines the literal pencil

```text
A - z I
```

and characteristic values by the existence of a nonzero kernel vector. The kernel proves:

```text
A self-adjoint
and
(A - z I)x = 0, x != 0
--------------------------------
Im z = 0.
```

The same result is formalized for linear boundary relations. If a symmetric relation contains a nonzero direction `(u, z • u)`, the Green identity paired with that direction forces `conj z = z`.

For a value--flux pencil, relation symmetry is proved equivalent to the exact two-state identity

```text
<Gamma_1 y, Gamma_0 x> = <Gamma_0 y, Gamma_1 x>.
```

Thus any concrete native realization satisfying this identity and identifying native resonances with characteristic slopes immediately yields critical-amplitude preservation, real spectral exhaustion and strong off-critical scalar non-vanishing.

### Concrete TFVD--`G_pre` Hilbert boundary carrier

For every finite provenance atlas `S`, the release constructs the full vertical-Hilbert traces

```text
Gamma_0 x = (x 0, provenanceValue_S x)
Gamma_1 x = (q^(-1) * x 1 - x 0, provenanceNumberFlux_S x)
```

in the orthogonal boundary space

```text
C ⊕_2 EuclideanSpace C S.
```

Both the finitely supported edge core and the completed vertical carry Hilbert space `ell^2(N,C)` are covered.

The provenance number flux is coordinatewise multiplication by the real material tower level. Therefore the provenance leg satisfies Green symmetry exactly before scalar compression and after Hilbert completion.

### Exact Wronskian defect and admissible domains

The free vertical boundary defect is calculated exactly:

```text
W_q(x,y)
  = q^(-1) * (conj(y 1) * x 0 - conj(y 0) * x 1).
```

After orthogonally gluing all finite-atlas provenance coordinates,

```text
GreenDefect(Gamma_0,Gamma_1;x,y) = W_q(x,y).
```

Hence a restricted native boundary pencil is Green-symmetric if and only if its state domain is pairwise Wronskian-isotropic. This identifies the precise boundary condition that the bracket/Green/log-phase equation must select.

## Operator guardrails

Two incorrect spectral candidates are excluded in the Lean kernel:

1. the free vertical TFVD relation is the whole scalar boundary plane, so it is not symmetric and permits every complex slope;
2. for `0 < q < 1`, the dressed vertical centered bracket is not symmetric on the standard amplitude Hilbert space, since its neighbouring matrix coefficients are `q` and `q^(-1)`.

Therefore the dressed bracket belongs to the reconstruction and interior-equation channel. It cannot be renamed as the self-adjoint spectral operator. The fixed spectral realization must use the logarithmic phase generator together with the Green-symmetric boundary restriction.

## Remaining honest gate

The remaining vertical/operator construction is now reduced to two explicit tasks:

1. construct the bracket--Green--log-phase admissible domain and prove its Wronskian isotropy, followed by maximality/self-adjointness;
2. prove that a native complex-time resonance is exactly a characteristic slope/eigenvalue `z` of that fixed realization.

No scalar coefficient `G(z)` is inserted into the pencil definition, and no zeta-function identification is used to prove the new operator and boundary results.

## New modules

- `CPFormal/Analytic/CpNativeCarrySpectrumExhaustion.lean`;
- `CPFormal/Analytic/CpNativeCarrySelfAdjointBoundaryPencil.lean`;
- `CPFormal/Analytic/CpNativeCarrySelfAdjointBoundaryRelation.lean`;
- `CPFormal/Analytic/CpNativeCarryBoundaryGreenSymmetry.lean`;
- `CPFormal/Analytic/CpCarryVerticalBoundaryGreenDefect.lean`;
- `CPFormal/Analytic/CpNativeGpreFiniteProvenanceGreenSymmetry.lean`;
- `CPFormal/Analytic/CpNativeGpreHilbertProvenanceGreenSymmetry.lean`;
- `CPFormal/Analytic/CpNativeGpreFiniteGluedGreenDefect.lean`;
- `CPFormal/Analytic/CpNativeGpreHilbertGluedGreenDefect.lean`;
- `CPFormal/Analytic/CpCarryWeightedVerticalBracketNotSymmetric.lean`.

The release also includes the connected C2, TFVD, log-jet, `G_pre`, simple-root ledger and Green-activation checkpoint modules merged through pull request #8.

## Verification

Before publishing the tag and GitHub Release, the release workflow executes:

```bash
bash scripts/static_audit.sh
lake build --wfail
```

The annotated tag is created on the merged `main` commit only after both checks succeed. The consolidated pre-release stack passed GitHub Actions Lean kernel audit #608 before merge into `main`.

## Archival and Zenodo

The published GitHub Release is non-draft and non-prerelease. It is the event consumed by the repository's Zenodo integration. Zenodo assigns the version DOI after ingesting this immutable `v0.48.0` snapshot; the stable concept DOI remains `10.5281/zenodo.21483474`.
