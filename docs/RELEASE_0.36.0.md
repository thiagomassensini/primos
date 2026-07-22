# Checkpoint 0.36.0 — colapso dos traços na linha crítica

Este checkpoint recombina a anti-Hermiticidade residual do 0.35 com o canal
Green radial e fecha os três traços completos na linha crítica. O novo módulo
compilado é
`CPFormal.Analytic.CpFiniteTfvdLogJetCriticalLineTraces`.

## Anulação exata do Green

Para uma câmera prima `p`, o fluxo Green orientado já possuía a fatoração

```text
finiteOrientedCpGreenFlux(p,M,s)
  = (p^delta-p^(-delta)) * reflectedPairing(M,s),
delta = Re(s)-1/2.
```

Se `Re(s)=1/2`, então `delta=0` e

```text
p^delta-p^(-delta) = 0.
```

O kernel conclui, para todo corte `M`,

```text
finiteOrientedCpGreenFlux(p,M,s) = 0.
```

Essa anulação ocorre antes de qualquer limite. Não é necessário estimar,
normalizar ou provar convergência do pareamento Green.

## Termos de Abel na linha crítica

O 0.35 já havia provado a anti-Hermiticidade do bulk. O novo módulo registra
também, em cada corte,

```text
Re(finiteVertexFlux(N,s)) = 0,
Re(movingCutoff(N,s)) = 0,
Re(crossBulk(N,s)) = 0.
```

Logo os dois termos da integração por partes discreta permanecem no eixo
imaginário separadamente.

## Colapso dos três traços finitos

As fórmulas do 0.33 eram

```text
ResidualTrace
  = movingCutoff + crossBulk + (log(p)-1) GreenFlux,

CommutatorTrace
  = -log(p) GreenFlux,

DefectTrace
  = movingCutoff + crossBulk - GreenFlux.
```

Substituindo a anulação exata do Green, o kernel prova

```text
ResidualTrace(p,M,s)
  = finiteVertexFlux(3M,s)
  = movingCutoff(3M,s) + crossBulk(3M,s),

CommutatorTrace(p,M,s) = 0,

DefectTrace(p,M,s)
  = finiteVertexFlux(3M,s)
  = movingCutoff(3M,s) + crossBulk(3M,s).
```

Consequentemente,

```text
DefectTrace(p,M,s) = ResidualTrace(p,M,s)
```

em todo corte da linha crítica. Os traços residual e de defeito têm parte
real exatamente zero.

## Limites completos

O 0.34 provou a convergência absoluta do fluxo de vértices no strip fechado.
Compondo seus cutoffs com `M -> 3M`, o kernel obtém na linha crítica

```text
ResidualTrace(p,M,s)   -> B(s),
CommutatorTrace(p,M,s) -> 0,
DefectTrace(p,M,s)     -> B(s),
Re(B(s)) = 0,
```

onde

```text
B(s) = reflectedLogJetVertexFluxSeries(s).
```

Assim o canal Green radial desaparece, mas o canal residual imaginário não é
apagado pela mesma identidade.

## Ponto central

Em `s=1/2`, o 0.35 já havia provado a anulação termo a termo do fluxo de
vértices. Com o Green também nulo, seguem para toda câmera prima e todo corte

```text
ResidualTrace(p,M,1/2) = 0,
CommutatorTrace(p,M,1/2) = 0,
DefectTrace(p,M,1/2) = 0.
```

Fora do centro, este checkpoint prova somente que o limite residual pertence
ao eixo imaginário.

## Leitura estrutural

```text
Re(s)=1/2
    -> delta=0
    -> GreenFlux=0 em cada corte
    -> CommutatorTrace=0

ResidualTrace = DefectTrace
    = finiteVertexFlux
    = movingCutoff + crossBulk
    -> B(s) puramente imaginário

s=1/2
    -> fluxo de vértices também zera termo a termo
    -> todos os três traços são zero
```

## Fronteira bracket--Green preservada

O documento da linha crítica já distinguia o Green radial estabelecido da
porta bracket--Green ainda aberta. Este checkpoint usa somente a fatoração
radial finita. Ele não identifica um zero Genuine com a anulação desses
traços e não cancela o endpoint interno bracketado.

## Próximo núcleo mínimo

Abrir explicitamente o perfil que ainda pode sobreviver no eixo imaginário.
Na linha crítica, a forma fechada da corrente sugere uma série real de senos
para `B(1/2+it)/I`. O próximo passo é formalizar essa representação,
estabelecer suas simetrias em `t` e reduzir qualquer questão de não anulação
a uma afirmação real sobre esse perfil — ainda sem invocar zeros Genuine.

## Escopo rigoroso

Este checkpoint ainda não:

- prova que `B(1/2+it)` seja não nulo para algum `t != 0`;
- prova que `B(1/2+it)` seja zero para todo `t`;
- constrói a representação real por senos do perfil residual;
- liga os traços completos a zeros Genuine;
- cancela o endpoint interno da porta bracket--Green;
- prova somabilidade absoluta dos incrementos já reagrupados do bulk;
- prova cancelamento do off-diagonal aritmético;
- identifica o Genuine com `riemannZeta`;
- constrói operador Hilbert--Polya;
- prova a Hipótese de Riemann.

## Evidência do kernel

- commit matemático: `95f71d0cf9ebb4dda3b6853a5ca5c3d6ff4e2120`;
- workflow run: `29725876017` (`Lean kernel audit`);
- job: `88298736244` (`Build CPFormal`);
- resultado: `success` em auditoria estática e `lake build --wfail`;
- nenhum `sorry`, `admit` ou axioma local.
