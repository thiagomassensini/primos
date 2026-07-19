# Checkpoint 0.21.0 — normalizacao radial Green Cp finita

Este checkpoint retira a fase do operador Cp no lugar matematicamente
correto: dentro de cada bloco, antes da conjugacao e da formacao do
Wronskiano. O resultado e uma identidade Green real assinada em corte finito,
com fluxo, energia e bordo definidos explicitamente.

## Normalizacao antes do Wronskiano

Para

```text
delta = Re(s)-1/2,
N_p(s) = p^(1/2+i Im(s)),
```

o kernel verificou

```text
N_p(s) * p^(-s) = p^(-delta),
N_p(1-conj(s)) * p^(-(1-conj(s))) = p^delta.
```

Os dois termos do lado direito sao reais e positivos. Essa etapa nao e uma
rotacao aplicada depois ao resultado: o normalizador multiplica o gradiente
do bloco antes da forma sesquilinear. Assim, a conjugacao do Wronskiano nao
reintroduz a fase.

## Fator radial e sinal

O fluxo normalizado fatora exatamente como

```text
W_norm(p,M,s)
  = (p^(-delta)-p^delta) * reflectedPairing(M,s).
```

Orientando o fluxo no sentido de `delta`, aparece

```text
D_p(delta) = p^delta-p^(-delta).
```

Foi definido o prolongamento radial

```text
A_p(delta) = log p                         se delta=0,
             D_p(delta)/(2*delta)          se delta!=0.
```

O kernel verificou, para todo `delta` real e todo primo `p`,

```text
D_p(delta) = 2*delta*A_p(delta),
A_p(delta) > 0.
```

Portanto o fator radial possui exatamente o sinal do deslocamento critico.

## Identidade Green real finita

Com

```text
energy(p,M,s)
  = A_p(delta) * Re(reflectedPairing(M,s)),

flux(p,M,s)
  = Re(orientedWronskian(p,M,s)) + Re(stokesFlux(M,s)),

boundary(M,s)
  = Re(outerEndpoint(M,s)-innerEndpoint(s)),
```

o kernel deriva

```text
flux(p,M,s) = 2*delta*energy(p,M,s) + boundary(M,s).
```

O bordo continua literal. Pela etapa anterior, sua expressao crua e
`1/(M+1)-1`; o termo `-1` nao foi apagado nem absorvido na energia.

## O que a positividade provada significa

Foi provado que o cofator `A_p(delta)` e estritamente positivo. Ainda nao foi
provado que

```text
Re(reflectedPairing(M,s)) > 0.
```

Logo ainda nao existe prova de que `energy(p,M,s)>0`. Essa e a proxima
obrigacao minima. O checkpoint tambem ainda nao prova que um zero do Genuine
anula o fluxo nem que o bracket cancela o endpoint interno.

## Proximo nucleo minimo

1. obter uma forma quadratica ou soma de quadrados para a parte real do
   pareamento refletido finito;
2. provar sua positividade sob hipoteses exatas;
3. identificar o endpoint interno e a anulacao do fluxo com o bracket do
   `genuineContinuation`;
4. somente depois controlar o limite e instanciar `SignedGreenCertificate`.

## Evidencia de compilacao

- repositorio privado: `thiagomassensini/primos`;
- branch: `agent/lean-kernel-audit`;
- pull request: `#1` (rascunho);
- commit matematico: `3326ae95321c9e3e3f0477f347a0ccf6f3ca8c02`;
- workflow run: `29673514330`;
- job verde: `88156612420`;
- resultado: auditoria estatica e `lake build --wfail` concluidos com sucesso.

## Endpoints principais

- `Analytic.Cp.cpPhaseNormalizer_mul_eigenvalue`;
- `Analytic.Cp.phaseNormalizedCpBlockGradient_eq_radial_mul`;
- `Analytic.Cp.phaseNormalizedCpBlockGradient_reflected_eq_radial_mul`;
- `Analytic.Cp.finitePhaseNormalizedCpGreenFlux_eq_radialDifference_mul_pairing`;
- `Analytic.Cp.cpRadialDifference_eq_two_mul_delta_mul_cofactor`;
- `Analytic.Cp.cpRadialCofactor_pos`;
- `Analytic.Cp.finiteOrientedCpGreenFlux_eq_radialDifference_mul_pairing`;
- `Analytic.Cp.finiteSignedCpGreen_identity`.

Este checkpoint nao constroi uma instancia concreta de
`SignedGreenCertificate`, nao constroi operador Hilbert--Polya e nao prova RH.
