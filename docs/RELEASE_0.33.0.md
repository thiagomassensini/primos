# Checkpoint 0.33.0 — cutoff móvel e bulk cruzado do canal residual

Este checkpoint soma, em blocos completos de três arestas, o canal residual
isolado no 0.32 e executa a integração por partes discreta sem perder a
proveniência TFVD. O novo módulo compilado é
`CPFormal.Analytic.CpFiniteTfvdLogJetResidualCutoff`.

## Integração por partes finita

Para funções complexas `f,g : Nat -> Complex`, o kernel prova a identidade
válida inclusive em `N=0`:

```text
sum_{n<N} (f(n+1)-f(n)) g(n)
  = f(N) g(N-1) - f(0) g(0)
      + sum_{n<N-1} f(n+1) (g(n)-g(n+1)).
```

Aplicamos isso a

```text
ell(n) := log(n+1),
X(n,s) := reflectedDirichletVertexCrossFlux(n,s).
```

Como `ell(0)=log(1)=0`, o endpoint interno desaparece literalmente. Logo

```text
finiteReflectedLogJetVertexFlux(N,s)
  = reflectedLogJetMovingCutoff(N,s)
      + finiteReflectedLogJetCrossBulk(N,s),
```

onde

```text
movingCutoff(N,s) = ell(N) X(N-1,s),

crossBulk(N,s)
  = sum_{n<N-1} ell(n+1) (X(n,s)-X(n+1,s)).
```

Nenhum desses termos é apagado ou identificado por hipótese.

## Soma por blocos completos

O teorema `sum_range_threeBlocks_eq_range` prova, para toda função complexa,

```text
sum_{m<M} (f(3m)+f(3m+1)+f(3m+2))
  = sum_{n<3M} f(n).
```

Assim, as três coordenadas TFVD são mantidas até o pareamento e somente então
sintetizadas pelo campo `TfvdWedgeTriple.total`. O reagrupamento não descarta
a aresta dormente.

## Fórmula exata do residual

Somando o trio residual do 0.32, o kernel obtém

```text
ResidualTrace(p,M,s)
  = movingCutoff(3M,s)
      + crossBulk(3M,s)
      + (log(p)-1) GreenFlux(p,3M,s).
```

Esta é a forma finita correta do canal que o wedge do comutador não captura.

## Traços completos do comutador e do defeito

Para `p` primo, a identidade local do 0.32 soma exatamente para

```text
CommutatorTrace(p,M,s)
  = -log(p) GreenFlux(p,3M,s).
```

O defeito log-jet--Green satisfaz, sem hipótese de cancelamento,

```text
DefectTrace(p,M,s)
  = movingCutoff(3M,s)
      + crossBulk(3M,s)
      - GreenFlux(p,3M,s).
```

E, para `p` primo,

```text
DefectTrace = CommutatorTrace + ResidualTrace.
```

Portanto o coeficiente `log(p)` cancela somente na recombinação algébrica
entre os dois canais; ele não elimina o cutoff móvel nem o bulk cruzado.

## Witness kernel-checked de bulk genuíno

No primeiro bloco completo, `N=3` (isto é, `M=1`), e em `s=0`, o kernel
calcula

```text
X(0,0) = -1/2,
X(1,0) = -1/6,
X(2,0) = -1/12,

crossBulk(3,0)
  = -log(2)/3 - log(3)/12 < 0.
```

Consequentemente,

```text
finiteReflectedLogJetCrossBulk(3,0) != 0.
```

Isso refuta uma anulação algébrica universal do bulk cruzado. O witness está
fora da faixa crítica e não decide cancelamento sob hipóteses adicionais,
comportamento na linha crítica ou passagem ao limite.

## Leitura estrutural

```text
trios TFVD completos
        -> soma consecutiva de 3M arestas

fluxo log-jet de vértices
        -> cutoff móvel + bulk cruzado

defeito finito
        -> cutoff móvel + bulk cruzado - Green diagonal
```

O cutoff móvel é um termo de bordo real da integração por partes discreta. O
bulk cruzado mede a variação consecutiva da corrente refletida e já possui um
witness formal não nulo. Ambos precisam ser controlados quantitativamente
antes de qualquer limite ou conclusão espectral.

## Próximo núcleo mínimo

Derivar uma forma fechada para `X(n,s)` e provar estimativas explícitas para o
cutoff móvel e para os incrementos do bulk cruzado. O objetivo do 0.34 será
determinar, em um domínio declarado, se esses termos convergem, desaparecem
ou persistem — sem pressupor a resposta.

## Escopo rigoroso

Este checkpoint ainda não:

- controla o cutoff móvel quando `M -> infinity`;
- prova convergência, anulação ou sinal do bulk cruzado na faixa crítica;
- trata cutoffs incompletos como sínteses TFVD completas;
- prova cancelamento da interferência escalar off-diagonal;
- prova que zeros Genuine anulam o fluxo Green;
- identifica o Genuine com `riemannZeta`;
- constrói operador Hilbert--Polya;
- prova a Hipótese de Riemann.

## Evidência do kernel

- commit matemático: `c0342f9ccecdc155a6f43f8f8675df8458640da3`;
- workflow run: `29720105453` (`Lean kernel audit`);
- job: `88281241341` (`Build CPFormal`);
- resultado: `success` em auditoria estática e `lake build --wfail`;
- nenhum `sorry`, `admit` ou axioma local.
