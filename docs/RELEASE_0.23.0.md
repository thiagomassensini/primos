# Checkpoint 0.23.0 — porta bracketada e bordo Green canonico

Este checkpoint fecha a identificacao que faltava entre o endpoint interno da
identidade Green refletida e a carta bracketada do Genuine canonico. O novo
alvo compilado e `CPFormal.Analytic.CpBracketGreenBoundary`.

## A coincidencia exata

O representante `genuineContinuation` usa a camera canonica `p=3`. Nessa
camera, `halfRange(3)=1`; portanto a semente da carta e literalmente

```text
seedSum_3(s) = 1^(-s) = 1 = reflectedInnerEndpoint(s).
```

Isso nao e uma calibracao nem uma identificacao imposta depois da conta. Os
dois lados reduzem, por suas definicoes independentes, ao mesmo numero `1`.

## Identidade finita do bordo acoplado

Se

```text
trace_M(s) = sum_{k<M} bracket_3,k(s),
```

o kernel verificou

```text
finiteBracketedChart_3,M(s) = innerEndpoint(s) + trace_M(s).
```

O bordo Green cru e `outerEndpoint_M-innerEndpoint`. Definindo a porta
acoplada pela subtracao do traco bracketado independente, segue a identidade
finita exata

```text
rawBoundary_M(s) - trace_M(s)
  = outerEndpoint_M(s) - finiteBracketedChart_3,M(s).
```

O bordo nao foi definido como residual da identidade Green. Cada objeto foi
definido antes, e a igualdade foi provada por expansao das definicoes.

## Fechamento do bordo nos zeros Genuine

Para `s` na faixa critica, um zero de `genuineContinuation` e um zero da carta
bracketada da camera `p=3`. Alem disso,

```text
finiteBracketedChart_3,M(s) -> bracketedChart_3(s),
outerEndpoint_M(s) -> 0.
```

Logo, em todo zero Genuine na faixa,

```text
finiteBracketCoupledBoundary_M(s) -> 0.
```

O kernel verificou tanto a versao complexa quanto sua parte real assinada. Ele
tambem verificou a identidade equivalente `canonicalBracketTrace(s)=-1` nos
zeros Genuine.

## Identidade Green apos a porta

Subtraindo a mesma parte real de `trace_M` do fluxo e do bordo da identidade
assinada finita, permanece exata a formula

```text
coupledFlux_M
  = 2*(Re(s)-1/2)*finiteRadialGreenEnergy_M
      + coupledBoundary_M.
```

A energia finita ja era estritamente positiva para todo corte nao vazio.

## Escopo rigoroso

Este checkpoint fecha o **bordo**, nao o certificado Green completo. Ainda nao
foi provado que, num zero Genuine,

- o fluxo de bulk acoplado converge a zero ou se anula;
- a energia possui o limite ou a normalizacao exigida pela passagem final;
- existe uma instancia concreta de `SignedGreenCertificate`.

Portanto este checkpoint nao constroi um operador Hilbert--Polya e nao prova a
Hipotese de Riemann.

## Evidencia do kernel

- commit matematico: `d082847d71a26257045de7fb056403ed0c1d02cf`;
- workflow run: `29706219224` (`Lean kernel audit`);
- job: `88243582695` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`.

## Proximo nucleo minimo

Isolar o fluxo de bulk acoplado como objeto independente e provar seu
comportamento nos zeros Genuine. A prova nao pode obter a anulacao definindo o
fluxo como o residual `2*delta*energy+boundary`; ela precisa vir da propria
geometria bracketada/Green.
