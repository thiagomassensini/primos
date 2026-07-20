# Checkpoint 0.30.0 — wedge log-jet enriquecido e canal de defeito Green

Este checkpoint forma o wedge refletido diretamente nas portas TFVD
angular e log-jet enriquecidas do checkpoint 0.29. A proveniencia dos tres
residuos e preservada ate o pareamento. O novo modulo compilado e
`CPFormal.Analytic.CpFiniteTfvdLogJetGreenComparison`.

## As quatro portas do pareamento

Para cada bloco `m`, o kernel retorna antes da sintese as tres arestas de

```text
Phi(s), Psi(s), Phi(s#), Psi(s#),
s# = 1-conj(s).
```

O objeto `enrichedTfvdReflectedLogJetWedge` forma coordenada a coordenada

```text
conj(Psi_edge(s))*Phi_edge(s#)
  - conj(Phi_edge(s))*Psi_edge(s#).
```

O teorema

```text
canonicalEnrichedTfvdReflectedLogJetWedgeTriple_eq_canonical
```

verifica que o retorno TFVD produz exatamente o trio direto nos indices
`3m`, `3m+1` e `3m+2`. Nao ha compressao escalar, termo off-diagonal,
hipotese de zero ou passagem ao limite.

## Formula local descoberta pelo kernel

Escreva

```text
V_s(n) = (n+1)^(-s)
G_s(n) = V_s(n+1)-V_s(n)
L_s(n) = log(n+1)*V_s(n)
J_s(n) = L_s(n+1)-L_s(n).
```

O wedge log-jet de uma aresta e

```text
W_log(n,s) = conj(J_s(n))*G_s#(n) - conj(G_s(n))*J_s#(n).
```

Depois de expandir os quatro gradientes, os termos diagonais cancelam e o
kernel prova

```text
W_log(n,s)
  = (log(n+2)-log(n+1))
      * (conj(V_s(n))*V_s#(n+1)
          - conj(V_s(n+1))*V_s#(n)).
```

Esse e um fluxo cruzado entre vertices consecutivos. Ele foi definido
independentemente como `reflectedLogJetVertexFlux` e identificado pelo
teorema `canonicalReflectedLogJetEdgeWedge_eq_vertexFlux`.

## Comparacao com Green

O wedge Green orientado da mesma aresta usa outro canal:

```text
W_G(p,n,s)
  = conj(G_s(n))*B_p#(n) - conj(B_p(n))*G_s#(n),
```

onde `B_p` e o bloco Cp normalizado em fase. Portanto o log-jet de vertices
e o gerador radial Cp nao sao definicionalmente o mesmo objeto.

Foi mantido o canal explicito

```text
D(p,n,s) = reflectedLogJetVertexFlux(n,s) - W_G(p,n,s).
```

Como os dois termos foram construidos antes da comparacao, a identidade

```text
W_log(n,s) = W_G(p,n,s) + D(p,n,s)
```

nao define o wedge desejado por um residual. Ela registra a diferenca entre
dois canais independentes depois de identificar primeiro a forma fechada do
wedge log-jet.

Bloco por bloco, inclusive na aresta dormente, o teorema central e

```text
canonicalEnrichedTfvdReflectedLogJetWedgeTriple_eq_green_add_defect.
```

## Obstrucao kernel-checked

A igualdade direta nao ficou apenas sem prova. O kernel verificou o witness

```text
n = 0, s = 0:
W_log(0,0) = -log(2)/2,
W_G(p,0,0) = 0                  para todo p.
```

Como `log(2)>0`, os dois valores sao distintos. Logo nao existe uma
identidade algebrica universal que permita apagar `D`.

O witness `s=0` esta fora da faixa critica. Ele refuta somente a igualdade
universal; nao refuta uma identidade adicional sob hipoteses mais fortes,
uma renormalizacao correta ou um mecanismo de cancelamento no cutoff.

## Consequencia estrutural

```text
porta angular/log-jet enriquecida
        preserva os tres residuos
wedge log-jet por aresta
        = fluxo cruzado de vertices
comparacao com wedge Green radial
        = Green + defeito explicito
```

O checkpoint 0.29 corrigiu a perda da terceira aresta. O 0.30 mostra que
preservar a proveniencia era necessario, mas nao suficiente: o log-jet de
vertices e o canal radial Green sao operadores diferentes.

## Proximo nucleo minimo

O candidato natural do checkpoint 0.31 e formalizar o comutador log-jet do
bloco Cp. A identidade finita esperada, ainda nao promovida neste checkpoint,
e da forma

```text
B_p(J_s) - p^(-s)*J_s
  = log(p)*p^(-s)*G_s.
```

Ela separaria o gerador radial primo do fluxo cruzado horizontal revelado
acima. Somente depois deve-se testar se o defeito e um cobordo telescopico,
um termo de cutoff ou um canal genuinamente adicional.

## Escopo rigoroso

Este checkpoint ainda nao:

- prova a identidade do comutador log-jet Cp anunciada como proximo alvo;
- reagrupa a soma global por trios em todos os cutoffs;
- prova que o canal de defeito telescopa ou se anula;
- prova cancelamento da interferencia escalar off-diagonal;
- prova que zeros Genuine anulam o fluxo Green;
- passa ao limite infinito;
- identifica o Genuine com `riemannZeta`;
- constroi operador Hilbert--Polya;
- prova a Hipotese de Riemann.

## Evidencia do kernel

- commit matematico: `946d8579cb6a2557721e72be2e51676f1899d629`;
- workflow run: `29717563536` (`Lean kernel audit`);
- job: `88273712912` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`;
- nenhum `sorry`, `admit` ou axioma local.
