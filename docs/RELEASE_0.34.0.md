# Checkpoint 0.34.0 — decaimento do cutoff e limite do bulk residual

Este checkpoint abre a corrente cruzada do 0.33, prova estimativas uniformes
no strip fechado `0 <= Re(s) <= 1` e determina o destino dos dois termos
produzidos pela integração por partes discreta. O novo módulo compilado é
`CPFormal.Analytic.CpFiniteTfvdLogJetResidualAsymptotics`.

## Forma fechada da corrente cruzada

Para

```text
a = n+1,
b = n+2,
s# = 1-conj(s),
```

o kernel prova primeiro a conjugação correta da potência complexa em base
natural positiva e obtém

```text
X(n,s)
  = a^(-conj(s)) b^(-(1-conj(s)))
      - b^(-conj(s)) a^(-(1-conj(s))).
```

Essa identidade não usa aproximação assintótica nem troca de ramo.

## Cota uniforme no strip fechado

Se `0 <= sigma <= 1`, os dois produtos radiais satisfazem

```text
b^(-sigma) a^(sigma-1) <= 1/a,
a^(-sigma) b^(sigma-1) <= 1/a.
```

Aplicando as normas exatas já formalizadas para os produtos refletidos,
segue

```text
||X(n,s)|| <= 2/(n+1).
```

O salto logarítmico também é controlado sem constante oculta:

```text
||log(n+2)-log(n+1)|| <= 1/(n+1).
```

Portanto cada fluxo residual de vértices satisfaz

```text
||reflectedLogJetVertexFlux(n,s)||
  <= 2 * (n+1)^(-2).
```

## Convergência absoluta do fluxo residual

A série quadrática majorante é somável. O kernel conclui, em todo o strip
fechado,

```text
Summable (fun n => ||reflectedLogJetVertexFlux(n,s)||)
```

e consequentemente a série complexa também é somável. Seu limite canônico
foi nomeado

```text
reflectedLogJetVertexFluxSeries(s)
  = sum_n reflectedLogJetVertexFlux(n,s).
```

Os cutoffs finitos do fluxo convergem para essa série.

## O cutoff móvel desaparece

Para o cutoff deslocado, o kernel prova a cota explícita

```text
||movingCutoff(N+1,s)||
  <= 4 * log(N+2)/(N+2).
```

Como `log x / x -> 0`, segue

```text
movingCutoff(N,s) -> 0
```

em todo o strip fechado. Assim, o termo de bordo descoberto no 0.33 é real e
indispensável em cada corte finito, mas desaparece no limite desse domínio.

## O bulk converge

A identidade finita do 0.33 era

```text
vertexFluxCutoff = movingCutoff + crossBulk.
```

Com o primeiro termo convergindo para a série e o cutoff tendendo a zero, o
kernel prova

```text
crossBulk(N,s) -> reflectedLogJetVertexFluxSeries(s).
```

A mesma conclusão vale nos cutoffs TFVD completos `N=3M`.

O argumento não exige somabilidade absoluta dos incrementos já reagrupados
do bulk: sua convergência é herdada da identidade exata de Abel, da
somabilidade absoluta do fluxo original e do desaparecimento do cutoff.

## Persistência formal em `s=0`

No endpoint `s=0`, a forma fechada se reduz para todo `n` a

```text
X(n,0) = 1/(n+2) - 1/(n+1) < 0.
```

O salto logarítmico é estritamente positivo. Logo cada somador do fluxo tem
parte real estritamente negativa. Usando a somabilidade já provada, o kernel
conclui

```text
Re(reflectedLogJetVertexFluxSeries(0)) < 0,
reflectedLogJetVertexFluxSeries(0) != 0.
```

Consequentemente, nos cutoffs completos,

```text
crossBulk(3M,0)
```

converge, mas não converge a zero. O bulk residual persiste como limite não
nulo nesse endpoint.

`s=0` pertence ao bordo do strip fechado, não ao interior da faixa crítica.
Esse witness não prova persistência na linha crítica nem em zeros Genuine.

## Leitura estrutural

```text
corrente cruzada X = O(1/n)
        + salto de log = O(1/n)
        -> fluxo residual = O(1/n^2)
        -> série absolutamente convergente

cutoff móvel = O(log N / N)
        -> zero

bulk cruzado
        -> mesma série residual
        -> não nulo em s=0
```

## Próximo núcleo mínimo

Provar a simetria refletida da série residual,

```text
B(s#) = -conj(B(s)),
```

e extrair sua estrutura na linha crítica. O objetivo do 0.35 será decidir o
que a anti-Hermiticidade força — e o que ela não força — antes de recombinar
o limite residual com o canal Green.

## Escopo rigoroso

Este checkpoint ainda não:

- prova que o bulk seja não nulo na linha crítica;
- identifica os zeros ou o sinal do limite residual no interior do strip;
- prova somabilidade absoluta dos incrementos já reagrupados do bulk;
- passa o traço Green completo ao limite nesta nova decomposição;
- prova cancelamento do off-diagonal aritmético;
- prova que zeros Genuine anulam o fluxo Green;
- identifica o Genuine com `riemannZeta`;
- constrói operador Hilbert--Polya;
- prova a Hipótese de Riemann.

## Evidência do kernel

- commit matemático: `907619a2e2086f161e28b713a9de94e0d280dfb7`;
- workflow run: `29722869515` (`Lean kernel audit`);
- job: `88289399970` (`Build CPFormal`);
- resultado: `success` em auditoria estática e `lake build --wfail`;
- nenhum `sorry`, `admit` ou axioma local.
