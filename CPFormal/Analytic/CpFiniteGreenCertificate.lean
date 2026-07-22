import CPFormal.Analytic.CpReflectedEndpoint

/-!
# Certificado Green complexo em corte finito

Este modulo empacota duas identidades independentes ja verificadas:

1. o Wronskiano dos blocos Cp e a diferenca dos autovalores vezes a energia
   refletida;
2. o fluxo de Stokes discreto e literalmente o endpoint externo menos o
   endpoint interno.

O fluxo total e a soma dessas duas correntes definidas antes do teorema. O
bordo tambem e definido apenas pelos endpoints. Assim, a identidade Green
finita abaixo nao usa um residual `fluxo - energia` disfarçado de bordo.

O certificado ainda e complexo. Retirar a fase comum e tomar a parte real
positiva pertencem ao proximo nivel, antes de construir um
`SignedGreenCertificate` infinito.
-/

namespace CPFormal.Analytic.Cp

noncomputable section

/-!
Dados minimos de um certificado Green complexo finito. `bulkFlux` e
`stokesFlux` sao mantidos separados para que as duas obrigacoes matematicas
nao sejam coladas por definicao.
-/
structure FiniteComplexGreenCertificate where
  coefficient : ℂ
  energy : ℂ
  bulkFlux : ℂ
  stokesFlux : ℂ
  outerEndpoint : ℂ
  innerEndpoint : ℂ
  bulk_identity : bulkFlux = coefficient * energy
  stokes_identity : stokesFlux = outerEndpoint - innerEndpoint

namespace FiniteComplexGreenCertificate

/-- Bordo assinado literal do corte. -/
def boundary (certificate : FiniteComplexGreenCertificate) : ℂ :=
  certificate.outerEndpoint - certificate.innerEndpoint

/-- Fluxo total: corrente de bloco mais corrente de Stokes. -/
def flux (certificate : FiniteComplexGreenCertificate) : ℂ :=
  certificate.bulkFlux + certificate.stokesFlux

/-- Identidade Green finita derivada das duas identidades independentes. -/
theorem green_identity (certificate : FiniteComplexGreenCertificate) :
    certificate.flux =
      certificate.coefficient * certificate.energy + certificate.boundary := by
  unfold flux boundary
  rw [certificate.bulk_identity, certificate.stokes_identity]

end FiniteComplexGreenCertificate

/-- Corrente de Stokes para os valores de Dirichlet refletidos. -/
def finiteReflectedStokesFlux (M : ℕ) (s : ℂ) : ℂ :=
  finiteGreenBulk
    (fun n : ℕ ↦ (starRingEnd ℂ) (positiveDirichletValue s n))
    (fun n : ℕ ↦ positiveDirichletValue (reflectedParameter s) n)
    M

/-- O fluxo de Stokes e o bordo formado pelos dois endpoints verdadeiros. -/
theorem finiteReflectedStokesFlux_eq_endpoints
    (M : ℕ) (s : ℂ) :
    finiteReflectedStokesFlux M s =
      finiteReflectedOuterEndpoint M s -
        finiteReflectedOuterEndpoint 0 s := by
  simpa [finiteReflectedStokesFlux, finiteReflectedOuterEndpoint,
    finiteGreenBoundary] using
      (finiteGreenBulk_eq_boundary
        (fun n : ℕ ↦ (starRingEnd ℂ) (positiveDirichletValue s n))
        (fun n : ℕ ↦ positiveDirichletValue (reflectedParameter s) n)
        M)

/-- Bordo refletido explicito do corte. -/
def finiteReflectedBoundary (M : ℕ) (s : ℂ) : ℂ :=
  finiteReflectedOuterEndpoint M s - finiteReflectedOuterEndpoint 0 s

/-- O endpoint interno vale exatamente um. -/
theorem finiteReflectedInnerEndpoint_eq_one (s : ℂ) :
    finiteReflectedOuterEndpoint 0 s = 1 := by
  rw [finiteReflectedOuterEndpoint_eq_inv]
  norm_num

/-- Formula fechada do bordo finito: `1/(M+1)-1`. -/
theorem finiteReflectedBoundary_eq_inv_sub_one
    (M : ℕ) (s : ℂ) :
    finiteReflectedBoundary M s = (((M + 1 : ℕ) : ℂ))⁻¹ - 1 := by
  unfold finiteReflectedBoundary
  rw [finiteReflectedOuterEndpoint_eq_inv,
    finiteReflectedInnerEndpoint_eq_one]

/-- Instancia Cp concreta do certificado Green complexo em corte finito. -/
def finiteCpGreenCertificate (p M : ℕ) (s : ℂ) :
    FiniteComplexGreenCertificate where
  coefficient :=
    (starRingEnd ℂ) (natDirichletTerm s p) -
      natDirichletTerm (reflectedParameter s) p
  energy := finiteReflectedGradientPairing M s
  bulkFlux := finiteCpGreenFlux p M s
  stokesFlux := finiteReflectedStokesFlux M s
  outerEndpoint := finiteReflectedOuterEndpoint M s
  innerEndpoint := finiteReflectedOuterEndpoint 0 s
  bulk_identity :=
    finiteCpGreenFlux_eq_eigenvalueDifference_mul_pairing p M s
  stokes_identity := finiteReflectedStokesFlux_eq_endpoints M s

/-!
Forma totalmente expandida da identidade certificada. A esquerda contem as
duas correntes concretas; a direita contem coeficiente, energia e endpoints.
-/
theorem finiteCpGreen_identity_explicit
    (p M : ℕ) (s : ℂ) :
    finiteCpGreenFlux p M s + finiteReflectedStokesFlux M s =
      ((starRingEnd ℂ) (natDirichletTerm s p) -
          natDirichletTerm (reflectedParameter s) p) *
        finiteReflectedGradientPairing M s +
      finiteReflectedBoundary M s := by
  rw [finiteCpGreenFlux_eq_eigenvalueDifference_mul_pairing,
    finiteReflectedStokesFlux_eq_endpoints]
  rfl

/-- A instancia concreta satisfaz a API abstrata do certificado finito. -/
theorem finiteCpGreenCertificate_green_identity
    (p M : ℕ) (s : ℂ) :
    (finiteCpGreenCertificate p M s).flux =
      (finiteCpGreenCertificate p M s).coefficient *
          (finiteCpGreenCertificate p M s).energy +
        (finiteCpGreenCertificate p M s).boundary :=
  (finiteCpGreenCertificate p M s).green_identity

/-- O bordo armazenado pela instancia Cp possui a formula fechada esperada. -/
theorem finiteCpGreenCertificate_boundary_eq_inv_sub_one
    (p M : ℕ) (s : ℂ) :
    (finiteCpGreenCertificate p M s).boundary =
      (((M + 1 : ℕ) : ℂ))⁻¹ - 1 := by
  change finiteReflectedBoundary M s = (((M + 1 : ℕ) : ℂ))⁻¹ - 1
  exact finiteReflectedBoundary_eq_inv_sub_one M s

end

end CPFormal.Analytic.Cp
