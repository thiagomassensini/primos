# Checkpoint 0.20.0 — certificado Green Cp complexo em corte finito

Este checkpoint empacota o bulk espectral e a formula de Stokes num
certificado Green finito concreto. Fluxo, energia e bordo sao definidos antes
da identidade; o bordo nao e um residual escolhido para fechar a equacao.

## Duas identidades independentes

O certificado guarda separadamente:

```text
bulkFlux = coefficient * energy
stokesFlux = outerEndpoint - innerEndpoint.
```

Na instancia Cp,

```text
coefficient
  = conj(p^(-s)) - p^(-(1-conj(s)))

energy
  = sum_(n<M) conj(g_s(n))*g_(1-conj(s))(n)

bulkFlux
  = W_(p,M)(s).
```

O `stokesFlux` e a soma discreta da regra do produto aplicada aos dois
valores de Dirichlet refletidos. Pelo teorema de telescopagem, ele e
literalmente a diferenca dos endpoints.

## Fluxo, energia e bordo

O fluxo total e definido geometricamente por

```text
flux = bulkFlux + stokesFlux,
```

e o bordo por

```text
boundary = outerEndpoint - innerEndpoint.
```

Somente depois dessas definicoes, o kernel deriva

```text
flux = coefficient * energy + boundary.
```

Para a reflexao `s#=1-conj(s)`, os endpoints ja calculados no checkpoint
anterior fornecem a forma fechada

```text
boundary(M,s) = 1/(M+1) - 1.
```

Portanto o bordo cru nao tende a zero: seu endpoint externo tende a zero, mas
o endpoint interno vale um. A futura porta bracketada precisa produzir o
cancelamento desse termo interno. Essa obrigacao agora esta localizada e nao
pode ser absorvida numa definicao de cauda.

## Tipo exato do certificado

`FiniteComplexGreenCertificate` e deliberadamente complexo. Ele preserva a
identidade exata antes de retirar a fase comum dos autovalores. Ainda nao e um
`SignedGreenCertificate`, cujos fluxo, energia e bordo sao reais e cuja
energia deve ser estritamente positiva.

## Fronteira honesta

Este checkpoint ainda nao:

- retira a fase `exp(i*t*log p)*sqrt(p)`;
- escreve o coeficiente como `2*delta` vezes um fator real de sinal conhecido;
- prova a positividade da parte real da energia refletida;
- identifica o termo interno com o traco bracketado de
  `genuineContinuation`;
- constroi um `SignedGreenCertificate` concreto;
- constroi operador Hilbert--Polya ou prova RH.

## Evidencia de compilacao

- repositorio privado: `thiagomassensini/primos`;
- branch: `agent/lean-kernel-audit`;
- pull request: `#1` (rascunho);
- commit matematico: `b0b47a87a64acfd129fbeb4f0cac148ccc4114ae`;
- workflow run: `29671533493`;
- job verde: `88151337679`;
- resultado: auditoria estatica e `lake build --wfail` concluidos com sucesso.

## Endpoints principais

- `Analytic.Cp.FiniteComplexGreenCertificate`;
- `Analytic.Cp.FiniteComplexGreenCertificate.boundary`;
- `Analytic.Cp.FiniteComplexGreenCertificate.flux`;
- `Analytic.Cp.FiniteComplexGreenCertificate.green_identity`;
- `Analytic.Cp.finiteReflectedStokesFlux_eq_endpoints`;
- `Analytic.Cp.finiteReflectedBoundary_eq_inv_sub_one`;
- `Analytic.Cp.finiteCpGreenCertificate`;
- `Analytic.Cp.finiteCpGreen_identity_explicit`;
- `Analytic.Cp.finiteCpGreenCertificate_boundary_eq_inv_sub_one`.
