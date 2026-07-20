# Checkpoint 0.26.0 — log-jet finito da porta angular

Este checkpoint constroi, no nivel escalar finito, um candidato independente
ao segundo traco da lei de porta. O alvo compilado continua sendo
`CPFormal.Analytic.CpAngularPort`.

## Definicao independente do log-jet

No vertice positivo `n+1`, foi definido o campo vestido

```text
L_s(n) = log(n+1) * (n+1)^(-s).
```

Ele e o coeficiente esperado de `-d/ds`, mas sua definicao Lean nao usa
derivadas, `Phi`, Green, zeros ou um residual. Aplicando aos gradientes de
`L_s` os mesmos pesos angulares `1,2,0`, obtemos

```text
Psi_M(s)
  = -sum_{m<M} sum_{r<3}
      ((r+1) mod 3) * (L_s(3m+r+1)-L_s(3m+r)).
```

No codigo esse objeto se chama `finiteCanonicalAngularLogJetTrace`.

## Carta log-bracketada e telescopagem

A carta finita log-pesada foi definida separadamente pela segunda diferenca

```text
logBracket_m
  = L_s(3m+1) - 2*L_s(3m+2) + L_s(3m+3).
```

O kernel verificou, para todo `M` e todo `s : Complex`, sem hipotese
analitica,

```text
finiteCanonicalLogBracketChart M s
  = finiteCanonicalAngularLogJetTrace M s
      + L_s(3M).
```

Portanto `Psi_M` nao foi definido como a diferenca entre carta e bordo. Os
dois lados foram construidos antes, e o unico vertice externo saiu da
telescopagem dos pesos.

## Bordo externo

O kernel verificou a norma exata

```text
||L_s(n)|| = log(n+1) * (n+1)^(-Re(s)).
```

Usando `log x = o(x^sigma)` para `sigma>0`, concluiu

```text
Re(s)>0
  -> L_s(3M) -> 0.
```

Essa passagem elimina somente o bordo externo. Este checkpoint ainda nao
formaliza a convergencia da serie log-bracketada nem identifica seu limite
com a derivada analitica da carta.

## Fronteira honesta para a lei de porta

O objeto construido e um log-jet escalar finito derivado de `E A`. Ainda
faltam teoremas que:

- o identifiquem com o retorno TFVD enriquecido sem perder proveniencia;
- tipem seu pareamento com `Phi_M`;
- provem que o Wronskiano `Phi/Psi` coincide com o fluxo Green acoplado;
- deduzam que zeros Genuine anulam esse fluxo.

Assim, a equivalencia ja provada

```text
coupledFlux_M -> 0  <->  Re(s)=1/2
```

nao foi promovida para uma prova de localizacao dos zeros.

## Escopo rigoroso

Este checkpoint ainda nao:

- prova a identidade Wronskiana de porta;
- prova a passagem ao limite do log-jet completo;
- prova que o fluxo Green acoplado se anula nos zeros Genuine;
- constroi uma instancia concreta de `SignedGreenCertificate`;
- identifica o Genuine com `riemannZeta`;
- constroi operador Hilbert--Polya;
- prova a Hipotese de Riemann.

## Evidencia do kernel

- commit matematico: `de6715e04877994629747455ebfc6cc2c54f8ab0`;
- workflow run: `29710050913` (`Lean kernel audit`);
- job: `88252649077` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`.
