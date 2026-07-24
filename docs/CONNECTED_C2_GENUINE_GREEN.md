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

## A porta TFVD ja contem o cumulante

Existe uma identificacao mais forte e inteiramente interna ao projeto. Pela
definicao da forma de bordo,

```text
sameSEdgeBoundaryWedge(left,right,jetLeft,jetRight)
  = right * jetLeft - left * jetRight.
```

Logo

```text
K_h
  = a_h(pq) - a_h(p) a_h(q)
  = sameSEdgeBoundaryWedge(a_h(p),a_h(pq),1,a_h(q)).
```

O modulo `CPFormal.Analytic.CpConnectedC2TfvdPort` codifica essas quatro
entradas com `enrichedAngularTfvdEncode` e prova, depois do retorno exato da
valvula:

```text
visibleCell = K_h
dormantCell = 0.
```

Richardson aplicado diretamente a essas celulas visiveis produz
`(1/2) epsilon_p epsilon_q`. Portanto existe uma codificacao algebrica finita
de coordenadas C2 na porta TFVD universal, e Tate nao e necessario para
construir essa parte. Isso ainda nao e um intertwiner entre a dinamica C2 e o
operador Genuine.

## O pushforward realiza as duas escalas formalmente usadas

O pushforward truncado das fibras impares fornece agora uma realizacao
aritmetica exata da porta anterior. Para um core positivo `m`, as duas pernas
na profundidade `k >= 2` sao

```text
2^k m - 1,   2^k m + 1,
```

cada uma com peso `2^(-k)`. O modulo
`CPFormal.Carry.C2OddCorePushforward` define separadamente as ultimas
profundidades admissiveis das duas pernas e soma somente os niveis realmente
contidos no cutoff. A partir dessas somas finitas, sem postular uma lei de
halving, o kernel prova

```text
2 a_(8M)(m) - a_(4M)(m) = 1              (0 < m <= M).
```

Escrevendo

```text
epsilon_(M,r) = 1 - a_(4M)(r),
K_T(p,q)      = a_T(pq) - a_T(p) a_T(q),
```

o modulo `CPFormal.Analytic.CpC2OddCorePushforwardTfvd` especializa essa
identidade simultaneamente em `p`, `q` e `pq` e obtem

```text
2 K_(8M)(p,q) - K_(4M)(p,q)
  = (1/2) epsilon_(M,p) epsilon_(M,q).
```

As quatro massas concretas

```text
(a_T(p), a_T(pq); 1, a_T(q))
```

sao codificadas na porta TFVD enriquecida. O retorno exato da valvula prova

```text
visibleCell = K_T(p,q),
dormantCell = 0,
```

e a celula visivel satisfaz a mesma identidade de Richardson. Assim, os
parametros formais `h=1` e `h=1/2` do modelo conectado sao de fato os
cutoffs aritmeticos `4M` e `8M`. Esta realizacao ainda e um `encode/decode`
sintetico de quatro escalares na porta universal; ela nao afirma que essas
coordenadas sejam o estado canonico de gradientes.

Ha tambem uma ligacao finita com o canal log-Dirichlet. Depois de normalizar
explicitamente o coeficiente unitario por `a_T(1)=1` e zerar os indices
pares, defina `b_T` por inversao de Dirichlet:

```text
b_T * a_T = a_T log.
```

Para primos impares distintos, o kernel prova

```text
b_T(pq) = log(pq) K_T(p,q),

2 b_(8M)(pq) - b_(4M)(pq)
  = log(pq) (1/2) epsilon_(M,p) epsilon_(M,q).
```

Vestir esse coeficiente pelo monomio `positiveDirichletValue` produz
exatamente o `positiveLogDirichletValue` ja usado pelo log-jet canonico. A
telescopagem finita adicional

```text
positiveLogDirichletValue(s,N)
  = sum_{n<N} positiveLogDirichletGradient(s,n)
```

coloca o monomio semiprimo no span linear do campo de arestas log-jet nativo.
O modulo `CPFormal.Analytic.CpC2LogJetGpreLift` conserva agora esse span como
um estado finitamente suportado, em vez de somar as arestas antes da analise.
Para todo atlas finito de proveniencia, o mesmo estado alimenta as pernas
TFVD e `G_pre`; a inversa continua existente reconstrui o estado vertical
inteiro, e somente depois um readout finito recupera
`positiveLogDirichletValue(s,N)`.

Consequentemente, a identidade de Richardson semiprima concreta fatora pelo
carrier enriquecido:

```text
RichardsonLogCoefficient(pq) * positiveDirichletValue(s,pq-1)
  = (1/2 epsilon_(M,p) epsilon_(M,q))
      * enrichedReadout(enrichedAnalysis(logJetPrefix(s,pq-1))).
```

O coeficiente conectado permanece como escalar externo. Cada coordenada de
proveniencia selecionada e populada explicitamente antes do readout, mas a
inversa atual recupera o prefixo pela perna TFVD e nao usa essas coordenadas.
Portanto, esse e um lift sem perda do prefixo log-jet usado pelo `C2`, nao um
lift da interacao conectada inteira para a proveniencia. Ainda falta provar
que uma combinacao ponderada das pernas `G_pre` detecta esse coeficiente e
desce para a proveniencia Green canonica.

Um guarda operacional simples torna essa fronteira precisa: o teorema de
reconstrucao e o readout escalar continuam validos com o atlas vazio
`S = empty`. Portanto, qualquer proximo lema que pretenda ser uma lei de
proveniencia deve depender nao trivialmente de coordenadas selecionadas do
atlas e comparar as duas cameras; nao basta reutilizar a inversa TFVD.

O mesmo modulo prova ainda o crosswalk semiprimo exato

```text
positiveLogDirichletValue(s,pq-1)
  = cpLogScaleCoefficient(p,s)
  + cpLogScaleCoefficient(q,s)
  + finiteCpLogJetCommutator(p,q-1,s)
  + finiteCpLogJetCommutator(q,p-1,s).
```

Assim, o vertice sintetizado se abre em duas sementes de cameras e dois
bordos de comutador finitos, sem primalidade, condicao de faixa ou zero
Genuine.

O portador canonico `same-s` usado atualmente pelo Genuine, porem, codifica
gradientes Dirichlet e log-Dirichlet consecutivos. A porta C2 acima codifica
massas `a_M(p),a_M(q),a_M(pq)`. A telescopagem nova alcanca o span do campo
log-jet e o novo lift conserva o estado enquanto popula o atlas de
proveniencia, mas a seta ponderada que use esse atlas para recuperar a
interacao conectada e o gap Green `same-s` entre duas cameras ainda nao
existe.

## Covariancia `same-s` e seu limite

Para uma unica camera `p`, aplicar o bloco Cp simultaneamente ao gradiente
ordinario e ao log-gradiente cancela exatamente o shear logaritmico no
determinante:

```text
W(B_p D, B_p L) = natDirichletTerm(s,p)^2 W(D,L).
```

Depois da normalizacao de fase critica, o fator e puramente radial:

```text
W_p^norm = p^(-2 delta) W_0.
```

Isso identifica a lei de transporte local sugerida pelo canon, mas nao
sincroniza duas cameras. Para `p != q`, os fatores radiais continuam
diferentes quando `delta != 0`; usar sua igualdade como hipotese seria
reintroduzir exatamente a conclusao forte.

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

`G_pre` e o carrier aritmetico atual mais proximo da algebra conectada:

- possui quatro cantos com sinais `(+,-,-,+)`;
- preserva os eixos aritmeticos, de canto, orientacao e proveniencia;
- possui inversao de Moebius--Jordan e readouts reduzidos;
- possui uma realizacao TFVD finita.

Mas ainda nao possui:

- massas `a_M` ou defeitos `epsilon_M`;
- um cumulante misto entre duas bases;
- uma lei de halving entre dois cutoffs;
- um teorema que transporte o zero Genuine para esse readout conectado.

Existem ainda duas obstrucoes exatas, formalizadas em
`CPFormal.Analytic.CpNativeGpreConnectedC2Guard`.

Primeiro, a massa Jordan infinita atual e multiplicativa. Para `m,n`
coprimos,

```text
J_tau(mn) - J_tau(m) J_tau(n) = 0.
```

Em particular, especializar diretamente o cumulante C2 nessa massa para dois
primos distintos produz zero, nao um detector positivo.

Segundo, os carriers e tracos atuais sao lineares na coordenada de aresta.
Nao existe um funcional puramente linear somente nas duas marginais

```text
L : R x R -> R
```

com `L(epsilon_p,epsilon_q)=epsilon_p epsilon_q`. O wedge da porta C2 resolve
a parte algebrica por ser bilinear; uma realizacao aritmetica no carrier
`G_pre` ainda precisa desse wedge, de uma coordenada quadratica/tensorial ou
de um estado aumentado que ja armazene o monomio misto.

A compressao Genuine atual de `G_pre` e construida diretamente em
`criticalLineParameter t`. Ela certifica a camera real-espectral na linha,
mas nao pode localizar a parte real de um zero ainda desconhecido.

## Menor ponte nova

O pushforward novo fecha as duas primeiras tarefas da rota finita: fornece
um estado conjunto no mesmo cutoff e o coloca exatamente na porta C2--TFVD.
Uma rota C2--`G_pre` completa ainda precisa construir um intertwiner com as
duas propriedades espectrais restantes:

1. uma projecao coerciva dessa porta sobre a proveniencia canonica `same-s`
   ou sobre o detector radial;
2. uma lei, derivada do zero Genuine, que feche o readout conectado.

A primeira propriedade restante nao pode pressupor que a proveniencia zera:
para cameras
primas distintas, isso ja equivale a `delta = 0`.

A normalizacao tambem e obrigatoria. No modelo C2,
`epsilon_M(p) epsilon_M(q)` tende a zero quando a profundidade cresce.
O modulo novo registra a lei finita mais precisa: ao duplicar `M`, cada
defeito marginal e dividido por `2` e o coeficiente conectado e dividido por
`4`:

```text
epsilon_(2M,r) = (1/2) epsilon_(M,r),
connectedDefect_(2M)(p,q) = (1/4) connectedDefect_M(p,q).
```

Portanto provar apenas

```text
epsilon_M(p) epsilon_M(q) * provenanceGap_M -> 0
```

nao controla `provenanceGap_M`. E necessario obter uma identidade finita
exata, ou um erro pequeno relativamente ao defeito conectado. Em particular,
o produto conectado vezes um vertice semiprimo fixo converge a zero para
todo `s`; esse limite nao caracteriza zeros Genuine.

## Guardas para o canal zeta do pushforward

A formalizacao usa somente a camada finita que e exata. As afirmacoes
analiticas adicionais do material exigem correcoes antes de entrarem na
cadeia:

- para usar inversao de Dirichlet, o canal normalizado substitui
  explicitamente o coeficiente bruto do core `1` por `a_T(1)=1`; o `b_T`
  formalizado pertence a esse canal impar seed-normalizado, nao ao polinomio
  truncado bruto sem essa correcao constante;
- convergencia pontual dos coeficientes `b_T(n)` nao autoriza trocar limite e
  serie sem uma majorante uniforme;
- `(1-2^(-s)) zeta(s)` tem zeros adicionais na reta `Re(s)=0`, portanto a
  equivalencia de zeros com Genuine so e segura no strip aberto;
- num zero de multiplicidade `r`, o residuo de `-Z'/Z` e `-r`, nao `+r`, e
  existe ainda o comportamento singular em `s=1`.

Por isso nenhum limite de serie, continuacao meromorfa ou enunciado de polos
foi usado nos modulos novos. A inversao de Dirichlet e coeficiente por
coeficiente e inteiramente finita.

## Papel de Tate

O modulo `CpTateCarryLocalCarrier` permanece util como dicionario local:
ele prova a covariancia geometrica, o carrier nao ramificado trivial e o
mismatch quadratico do bracket congelado. O modulo
`CpCriticalRadialBracketGuard` registra que transformar isso numa ponte global
ja equivale ao teorema forte.

Assim, Tate pode ser dispensado como linguagem da proxima tentativa. O novo
alvo mais concreto e o intertwiner cumulante C2--`G_pre`; o gargalo de
observabilidade, porem, continua explicitamente aberto.
