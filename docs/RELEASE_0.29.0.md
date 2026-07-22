# Checkpoint 0.29.0 — aresta dormente e intertwiner TFVD angular--Green

Este checkpoint determina exatamente quanta informacao do Green e carregada
pela porta TFVD angular do checkpoint 0.27 e constroi a menor ampliacao que
fecha o transporte local. O novo modulo compilado e
`CPFormal.Analytic.CpFiniteTfvdAngularGreenIntertwiner`.

## A descoberta

Cada bloco da camera angular `p=3` possui tres gradientes com pesos

```text
residuo 0 -> peso 1
residuo 1 -> peso 2
residuo 2 -> peso 0.
```

O portador TFVD anterior guarda os dois primeiros porque sao exatamente os
canais necessarios para o readout de `Phi_M/Psi_M`. O fluxo Green, entretanto,
pareia cada gradiente horizontal e portanto tambem consome o residuo 2.

A terceira aresta nao e nula: ela e somente dormente para a sintese angular.

## Alcance exato do portador atual

O retorno da coordenada angular atual recupera literalmente

```text
positiveDirichletGradient(s,3m)
positiveDirichletGradient(s,3m+1).
```

Os mapas `angularTfvdToCpGreenFirst` e
`angularTfvdToCpGreenSecond` transportam esses dois valores para os
portadores Green canonicos nos indices `3m` e `3m+1`. O kernel verificou
ambas as igualdades sem termo de erro.

## Obstrucao formal

O teorema

```text
no_universalDormantEdgeDecoder_from_currentTfvdPair
```

prova que nao existe um mapa universal

```text
TfvdCoordinate x TfvdCoordinate -> Complex
```

capaz de recuperar uma terceira aresta arbitraria do par TFVD ordinario e
log-jet atual. O witness mantem literalmente as mesmas entradas e exige
saidas `0` e `1`.

Logo a aresta dormente nao pode ser reconstruida por uma escolha de retorno
ou calibracao posterior: ao menos uma nova coordenada de proveniencia e
necessaria.

## Enriquecimento minimo

Foi definida

```text
EnrichedAngularTfvdCoordinate =
  (visible : TfvdCoordinate, dormantEdge : Complex).
```

O retorno enriquecido recupera exatamente as tres arestas. Esquecer
`dormantEdge` devolve definicionalmente as portas TFVD anteriores. Portanto
os readouts continuam literalmente

```text
Phi_block  e  Psi_block.
```

Nenhuma formula escalar existente foi alterada.

## Intertwiner local completo

A aresta adicional produz o terceiro portador Green canonico, no indice
`3m+2`. Reunindo os dois canais visiveis e o dormente, o teorema

```text
enrichedAngularTfvdToCpGreenTriple_eq_canonical
```

verifica bloco por bloco

```text
enriched angular TFVD block m
  -> (Green[3m], Green[3m+1], Green[3m+2]).
```

Assim, uma unica coordenada escalar extra e necessaria e suficiente para o
transporte local completo da porta angular ao portador Green.

## Consequencia estrutural

```text
porta escalar Phi/Psi
        esquece a aresta de peso 0
TFVD enriquecido
        preserva os tres residuos
trio Green canonico
        alimenta a diagonal 0.28.
```

A informacao nao desaparecia; estava invisivel para aquele readout.

## Escopo rigoroso

Este checkpoint ainda nao:

- reagrupa formalmente a soma global por trios em todos os cutoffs;
- identifica o Wronskiano do log-jet enriquecido com o wedge Green;
- prova cancelamento da interferencia escalar;
- prova que zeros Genuine anulam o fluxo;
- passa ao limite infinito;
- identifica o Genuine com `riemannZeta`;
- constroi operador Hilbert--Polya;
- prova a Hipotese de Riemann.

## Evidencia do kernel

- commit matematico: `ef39ed4ec05e97ec449422a524537c2c570907d6`;
- workflow run: `29715936088` (`Lean kernel audit`);
- job: `88269139110` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`;
- nenhum `sorry`, `admit` ou axioma local.
