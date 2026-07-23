# Defeito conectado C2 e a ponte Genuine--Green

## Resultado da auditoria

O material `teoria_defeitos_c2_unificada.md` fornece uma alternativa
conceitual ao dicionario local de Tate. A parte aproveitavel e a algebra
formal dos cumulantes locais; as regressoes, sinais por primos e conjecturas
de estabilidade permanecem evidencia numerica ou heuristica e nao entram na
cadeia de prova.

Para duas marginais, escreva

```text
a_h(p)  = 1 - h epsilon_p
a_h(q)  = 1 - h epsilon_q
a_h(pq) = 1 - h epsilon_pq
K_h     = a_h(pq) - a_h(p) a_h(q).
```

Uma conta exata fornece

```text
2 K_(1/2) - K_1 = (1/2) epsilon_p epsilon_q.
```

O termo conjunto `epsilon_pq` e todos os termos lineares cancelam, desde que
o mesmo modelo de halving `a_h=1-h epsilon` valha em todo o suporte
`{p,q,pq}`. Essa e a caracteristica nova: o readout preserva somente a
interacao conectada entre as duas marginais.

O modulo `CPFormal.Analytic.CpConnectedC2Defect` verifica essa identidade no
kernel e registra tambem:

```text
radialC2(p,q,delta)
  = (1/2) R_p(delta) R_q(delta)
  = 2 delta^2 A_p(delta) A_q(delta).
```

Para `p` e `q` primos, os cofatores `A_p,A_q` sao positivos. Portanto o
detector-modelo radial e positivo quando `delta != 0` e zera exatamente em
`delta = 0`.

Essa especializacao e apenas um detector-modelo. Ela nao identifica o defeito
de massa `epsilon_M(p)` do documento com `cpRadialDifference p delta`.

## Por que o defeito atual nao basta

No documento C2, `p,q` sao fatores primos observados pela mesma profundidade
diadica e pelo mesmo cutoff. No codigo Cp atual, `p,q` sao modulos de cameras
distintas. Essa diferenca de tipos matematicos impede uma substituicao direta.

O objeto mais proximo no repositorio e
`crossPrimeAlignedCutoffDefect`. Contudo, ja foi provado que

```text
D_L = chart_q - chart_p = (F_q - F_p) genuineContinuation,
```

independentemente de `L`. Logo a combinacao formal nas escalas alinhadas
`L` e `2L` satisfaz

```text
2 D_(2L) - D_L = D_L.
```

O Lean verifica essa identidade em
`crossPrimeAlignedCutoffDefect_richardson_eq_self`. Assim, aplicar Richardson
ao defeito existente apenas repete o detector escalar de posto um. Nao produz
o produto conectado.

Ha uma segunda diferenca: o cutoff alinhado e afim em `L`, portanto
`L -> 2L` nao e literalmente o halving `M -> 2M` do documento. Qualquer uso
da lei de halving exigira uma construcao de escala nova e explicita.

## Relação com `G_pre`

`G_pre` e o carrier atual mais proximo da algebra conectada:

- possui quatro cantos com sinais `(+,-,-,+)`;
- preserva os eixos aritmeticos, de canto, orientacao e proveniencia;
- possui inversao de Moebius--Jordan e readouts reduzidos;
- possui uma realizacao TFVD finita.

Mas ainda nao possui:

- massas `a_M` ou defeitos `epsilon_M`;
- um cumulante misto entre duas bases;
- uma lei de halving entre dois cutoffs;
- um teorema que transporte o zero Genuine para esse readout conectado.

A compressao Genuine atual de `G_pre` e construida diretamente em
`criticalLineParameter t`. Ela certifica a camera real-espectral na linha,
mas nao pode localizar a parte real de um zero ainda desconhecido.

## Menor ponte nova

Uma rota C2--`G_pre` honesta precisa construir um intertwiner com quatro
propriedades separadas:

1. um estado conjunto de duas bases no mesmo cutoff;
2. uma identidade finita de Richardson que extraia o canal conectado;
3. uma projecao coerciva desse canal sobre a proveniencia `same-s` ou sobre o
   detector radial;
4. uma lei, derivada do zero Genuine, que feche o readout conectado.

A propriedade 3 nao pode pressupor que a proveniencia zera: para cameras
primas distintas, isso ja equivale a `delta = 0`.

A normalizacao tambem e obrigatoria. No modelo C2,
`epsilon_M(p) epsilon_M(q)` tende a zero quando a profundidade cresce.
Portanto provar apenas

```text
epsilon_M(p) epsilon_M(q) * provenanceGap_M -> 0
```

nao controla `provenanceGap_M`. E necessario obter uma identidade finita
exata, ou um erro pequeno relativamente ao defeito conectado.

## Papel de Tate

O modulo `CpTateCarryLocalCarrier` permanece util como dicionario local:
ele prova a covariancia geometrica, o carrier nao ramificado trivial e o
mismatch quadratico do bracket congelado. O modulo
`CpCriticalRadialBracketGuard` registra que transformar isso numa ponte global
ja equivale ao teorema forte.

Assim, Tate pode ser dispensado como linguagem da proxima tentativa. O novo
alvo mais concreto e o intertwiner cumulante C2--`G_pre`; o gargalo de
observabilidade, porem, continua explicitamente aberto.
