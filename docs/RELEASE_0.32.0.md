# Checkpoint 0.32.0 — wedge do comutador e canal residual do defeito

Este checkpoint forma o wedge refletido do comutador log-jet provado no
0.31 e o compara, preservando os tres residuos, com o defeito log-jet--Green
do 0.30. O novo modulo compilado e
`CPFormal.Analytic.CpFiniteTfvdLogJetCommutatorDefect`.

## Wedge do comutador

O 0.31 provou antes do pareamento

```text
C_p(s,n) := [B_p,log](s,n)
          = log(p) p^(-s) G_s(n).
```

Depois da normalizacao de fase, o checkpoint atual forma exatamente o mesmo
wedge orientado usado pelas portas angular/log-jet:

```text
W_C(p,n,s)
  = conj(C_p^N(s,n)) G_s#(n)
      - conj(G_s(n)) C_p^N(s#,n).
```

As quatro portas sao construidas independentemente antes do retorno.

## Proveniencia TFVD completa

A coordenada

```text
canonicalEnrichedCpLogJetCommutatorTfvdCoordinate
```

carrega separadamente as arestas `3m`, `3m+1` e `3m+2`. O teorema

```text
canonicalEnrichedTfvdCpLogJetCommutatorWedgeTriple_eq_canonical
```

verifica que o retorno enriquecido produz literalmente os tres wedges
diretos. A aresta dormente nao e descartada e nenhuma sintese escalar ocorre
antes do pareamento.

## Formula local descoberta

Como os coeficientes radiais normalizados nos parametros refletidos sao
`p^(-delta)` e `p^delta`, com `delta=Re(s)-1/2`, o kernel prova

```text
W_C(p,n,s) = -log(p) * W_G(p,n,s).
```

O sinal negativo vem da orientacao do wedge log-jet em relacao ao wedge
Green. O teorema e

```text
canonicalReflectedCpLogJetCommutatorWedge_eq_neg_log_mul_green.
```

Portanto o wedge induzido pelo cobordo do 0.31 permanece inteiramente na
direcao Green. Ele nao produz o fluxo cruzado de vertices do log-jet.

Bloco a bloco, inclusive no terceiro residuo,

```text
commutatorWedgeTriple
  = -log(p) * greenWedgeTriple.
```

## Comparacao com o defeito do 0.30

O canal que resta depois de separar o wedge do comutador e construido sem
usar o defeito como entrada:

```text
R(p,n,s)
  = reflectedLogJetVertexFlux(n,s)
      + (log(p)-1) W_G(p,n,s).
```

O teorema local prova

```text
D_logJet-Green(p,n,s) = W_C(p,n,s) + R(p,n,s).
```

O teorema central preserva os tres residuos:

```text
canonicalLogJetGreenDefectTriple
  = commutatorWedgeTriple + residualTriple.
```

Existe tambem a versao em que `commutatorWedgeTriple` e retornado diretamente
das portas TFVD enriquecidas.

## Obstrucao kernel-checked

No witness `n=0,s=0`, para toda camera prima,

```text
W_G       = 0,
W_C       = 0,
R         = -log(2)/2,
D         = -log(2)/2.
```

Como `log(2)>0`, o kernel prova tanto a desigualdade por aresta quanto a
desigualdade dos trios em `m=0`:

```text
canonicalLogJetGreenDefectTriple
  != canonicalReflectedCpLogJetCommutatorWedgeTriple.
```

O witness esta fora da faixa critica. Ele decide somente a identidade
algebrica universal: o comutador nao esgota o defeito. Nao exclui um
cancelamento do canal residual sob hipoteses adicionais ou depois de uma
soma de cutoff corretamente tipada.

## Leitura estrutural

```text
comutador antes do wedge
        soma a um bordo finito

wedge refletido do comutador
        = -log(p) * Green

defeito log-jet--Green
        = parcela do comutador
          + canal residual de vertices
```

O documento de log-jet enriquecido foi usado apenas como controle de tipo:
o dipolo de cutoff/comutador nao deve ser reduzido antes da colagem, e a
proveniencia deve sobreviver ao pareamento. Nenhuma conclusao pos-`T0`,
Green--zero ou espectral foi importada.

## Proximo nucleo minimo

Somar o canal residual em cutoffs formados por blocos completos de tres
arestas. O objetivo e separar formalmente sua parcela telescopica de um
eventual termo de cutoff e testar se sobra um bulk cruzado genuino.

## Escopo rigoroso

Este checkpoint ainda nao:

- prova que o canal residual telescopa, se anula ou possui sinal;
- reagrupa todos os cutoffs incompletos por trios;
- prova cancelamento da interferencia escalar off-diagonal;
- prova que zeros Genuine anulam o fluxo Green;
- passa ao limite infinito;
- identifica o Genuine com `riemannZeta`;
- constroi operador Hilbert--Polya;
- prova a Hipotese de Riemann.

## Evidencia do kernel

- commit matematico: `c200dac5d55fc10ec2d9d8f5ebc8ecd6b17a6a25`;
- workflow run: `29719225646` (`Lean kernel audit`);
- job: `88278484382` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`;
- nenhum `sorry`, `admit` ou axioma local.
