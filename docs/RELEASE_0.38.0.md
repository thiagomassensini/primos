# Checkpoint 0.38.0 — orçamento angular Genuine-first

Este checkpoint volta ao zero de `genuineContinuation` antes de impor qualquer
conclusão sobre a linha crítica. O novo módulo compilado é
`CPFormal.Analytic.CpFiniteGenuineAngularGreenBudget`.

## Ponto de partida Genuine

Para `s` no strip crítico, o kernel já sabia que

```text
genuineContinuation(s)=0
  -> finiteCanonicalAngularTrace(M,s) -> 0.
```

O 0.38 combina essa porta angular com a porta no parâmetro refletido

```text
s# = 1-conj(s).
```

Se `s` e `s#` são zeros Genuine, o produto escalar refletido tende a zero:

```text
conj(Phi_M(s)) * Phi_M(s#) -> 0.
```

Esta conclusão usa somente os dois zeros e o teorema já existente para o
traço angular; não usa `Re(s)=1/2`.

## Decomposição finita antes da compressão

O produto das portas é aberto antes de perder a proveniência dos blocos. O
kernel prova a identidade exata

```text
ScalarAngularPairing(M,s)
  = GreenPairing(3M,s)
  + LocalTrioCorrection(M,s)
  + OffDiagonalBlockPairing(M,s).
```

Assim a correção não radial total fica tipada como

```text
AngularGreenCorrection
  = LocalTrioCorrection + OffDiagonalBlockPairing.
```

A primeira parcela é completamente explícita. Em cada trio ela contém:

- os dois produtos cruzados entre as arestas `3m` e `3m+1`;
- a correção do peso angular `2`;
- a restauração da aresta `3m+2`, dormente na porta angular comprimida.

A segunda parcela contém somente interferência entre blocos distintos. Ela
não é misturada com a correção local.

## Orçamento de um par de zeros

Com os dois zeros Genuine, a decomposição anterior dá

```text
GreenPairing(3M,s) + AngularGreenCorrection(M,s) -> 0.
```

Isto não afirma separadamente que o Green ou a correção tendam a zero. É um
orçamento exato: qualquer cancelamento ainda possível ficou localizado e
nomeado.

## Duas obrigações transparentes

O módulo introduz `GenuineAngularGreenCancellationBridge p` com somente dois
campos:

```text
1. zero Genuine em s -> zero Genuine em s#;

2. cpRadialDifference(p,delta)
     * AngularGreenCorrection(M,s) -> 0.
```

Nenhuma instância dessa estrutura é declarada. Portanto nem a simetria dos
zeros nem o fechamento da correção são postulados como fatos do projeto.

Sob exatamente esses dois campos, o kernel multiplica o orçamento pelo
coeficiente radial, subtrai a correção e obtém

```text
cpRadialDifference(p,delta) * GreenPairing(3M,s) -> 0.
```

A parte real do pareamento Green é positiva no primeiro nível e monótona.
Logo não pode tender a zero por perda de energia. O coeficiente radial precisa
ser nulo:

```text
cpRadialDifference(p,delta)=0
  -> delta=0.
```

O módulo então constrói formalmente
`GenuineCarryFluxBridge p`, a interface isolada no 0.37. Consequentemente,
qualquer instância futura da nova ponte já se compõe com os teoremas
existentes para concluir `Re(s)=1/2` nos zeros Genuine do strip.

## O que foi reduzido

O gargalo deixou de ser a afirmação opaca

```text
zero Genuine -> fluxo acoplado fecha
```

e passou a ser a soma de duas tarefas auditáveis:

```text
simetria refletida dos zeros
            +
cancelamento radial da correção local/off-diagonal.
```

A teoria de defeitos ajuda a interpretar a separação: defeitos conectados
dentro do trio e interferências entre blocos são mecanismos diferentes. O
canal lambda não fornece, por si só, nenhum dos dois teoremas que faltam.

## Escopo rigoroso

Este checkpoint ainda não:

- prova que `genuineContinuation(s#)=0` a partir de
  `genuineContinuation(s)=0`;
- prova o fechamento da correção angular escalada;
- declara uma instância de `GenuineAngularGreenCancellationBridge`;
- declara uma instância de `GenuineCarryFluxBridge`;
- cancela o off-diagonal por uma triangulação aritmética;
- constrói o complexo simplicial multibase completo;
- identifica o Genuine com `riemannZeta`;
- prova a Hipótese de Riemann.

## Próximo núcleo mínimo

O 0.39 deve atacar separadamente um dos dois campos da ponte. A ordem mais
limpa é verificar primeiro a simetria refletida de `genuineContinuation`,
porque ela depende da própria definição do objeto Genuine. Depois, a
correção já separada pode ser organizada como soma de defeitos locais e
circulação entre blocos, com a triangulação usada apenas onde houver um
teorema de cancelamento de arestas internas.

## Evidência do kernel

- commit matemático: `749a4cfb915a398c6f660356baacfa66a54c8c20`;
- workflow run: `29733959804` (`Lean kernel audit`);
- job: `88324777534` (`Build CPFormal`);
- resultado: `success` em auditoria estática e `lake build --wfail`;
- nenhum `sorry`, `admit` ou axioma local.
