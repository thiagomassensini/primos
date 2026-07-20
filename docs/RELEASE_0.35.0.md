# Checkpoint 0.35.0 — anti-Hermiticidade do bulk residual

Este checkpoint determina a geometria refletida da série residual construída
no 0.34. O novo módulo compilado é
`CPFormal.Analytic.CpFiniteTfvdLogJetResidualReflection`.

## Involução espectral

Para

```text
s# = 1 - conj(s),
```

o kernel prova primeiro

```text
(s#)# = s.
```

Se `Re(s)=1/2`, então `s#=s`. Essa é uma identidade do parâmetro complexo,
não uma hipótese sobre zeros ou sobre continuação analítica.

## Anti-Hermiticidade local

Escrevendo `X(n,s)` para a corrente cruzada entre os vértices `n+1` e
`n+2`, a involução troca as duas pernas do pareamento. O kernel obtém

```text
X(n,s#) = -conj(X(n,s)).
```

Como o salto

```text
log(n+2)-log(n+1)
```

é real, cada fluxo log-jet de aresta satisfaz a mesma lei:

```text
vertexFlux(n,s#) = -conj(vertexFlux(n,s)).
```

## Todo corte finito preserva a simetria

A identidade foi transportada separadamente para os três objetos do 0.33:

```text
finiteVertexFlux(N,s#) = -conj(finiteVertexFlux(N,s)),
movingCutoff(N,s#)     = -conj(movingCutoff(N,s)),
crossBulk(N,s#)        = -conj(crossBulk(N,s)).
```

Assim a integração por partes discreta não cria nem destrói a simetria
refletida. Em particular, se `Re(s)=1/2`, cada cutoff finito do bulk já possui
parte real exatamente nula.

## Passagem à série

Para

```text
B(s) = reflectedLogJetVertexFluxSeries(s),
```

a conjugação comuta com o `tsum`. A identidade termo a termo produz

```text
B(s#) = -conj(B(s)).
```

Essa igualdade do `tsum` é algébrica e vale sem hipótese de strip. As
estimativas do 0.34 entram quando o `tsum` é identificado com o limite do
bulk. Na linha crítica, elas dão conjuntamente

```text
crossBulk(3M,s) -> B(s),
Re(B(s)) = 0.
```

Portanto o limite do bulk residual na linha crítica pertence ao eixo
imaginário.

## Ponto central

No ponto real `s=1/2`, os dois expoentes cruzados são iguais. Logo o kernel
prova, para todo `n` e `N`,

```text
X(n,1/2) = 0,
vertexFlux(n,1/2) = 0,
crossBulk(N,1/2) = 0,
B(1/2) = 0.
```

Esse é um cancelamento termo a termo, mais forte que a mera
anti-Hermiticidade.

## O que a simetria não força

Fora do ponto central, a equação

```text
z = -conj(z)
```

implica somente `Re(z)=0`. O módulo registra formalmente o witness

```text
I = -conj(I),
I != 0.
```

Consequentemente, a simetria refletida não prova que `B(1/2+it)` seja zero
ou não zero quando `t != 0`; ela apenas elimina sua parte real.

## Leitura estrutural

```text
s -> s# troca as pernas do pareamento
        -> corrente e fluxo mudam para -conjugado
        -> cutoff, bulk e série preservam a lei

Re(s)=1/2
        -> s#=s
        -> bulk finito e limite são puramente imaginários

s=1/2
        -> produtos cruzados coincidem
        -> cancelamento termo a termo
        -> B(1/2)=0
```

## Próximo núcleo mínimo

Recombinar essa estrutura com o canal Green já formalizado. Como o
coeficiente radial de `finiteOrientedCpGreenFlux` é

```text
p^delta - p^(-delta),
delta = Re(s)-1/2,
```

o próximo passo é provar que o canal Green se anula literalmente na linha
crítica em todo corte e transportar isso para os traços completos do
comutador, do residual e do defeito. O objetivo é separar exatamente a parte
real que desaparece da parte imaginária residual que ainda pode sobreviver.

## Escopo rigoroso

Este checkpoint ainda não:

- prova que `B(1/2+it)` seja não nulo para algum `t != 0`;
- prova que `B(1/2+it)` seja zero para todo `t`;
- identifica os pontos da linha crítica com zeros Genuine;
- passa o traço Green completo ao limite nesta decomposição;
- prova somabilidade absoluta dos incrementos já reagrupados do bulk;
- prova cancelamento do off-diagonal aritmético;
- prova que zeros Genuine anulam qualquer fluxo;
- identifica o Genuine com `riemannZeta`;
- constrói operador Hilbert--Polya;
- prova a Hipótese de Riemann.

## Evidência do kernel

- commit matemático: `1368605c3311ef9d4e3a64e08a11cd88d72cf9b9`;
- workflow run: `29724391676` (`Lean kernel audit`);
- job: `88294072133` (`Build CPFormal`);
- resultado: `success` em auditoria estática e `lake build --wfail`;
- nenhum `sorry`, `admit` ou axioma local.
