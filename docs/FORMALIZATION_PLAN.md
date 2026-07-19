# Plano de formalizacao CP

## Decisao de rota: Genuine first

O nucleo ativo nao comeca por Hilbert--Polya. Ele deve construir o Genuine a
partir da geometria finita antes de importar qualquer linguagem espectral.

```text
pares e centros
  -> cancelamento finito
  -> bijecao de carry
  -> pesos por profundidade
  -> series bracketadas
  -> carta Genuine
  -> zero-equivalencia
```

## Objetivo final condicional

Para um zero Genuine `s`, queremos uma das duas rotas:

### Rota direta CP

```text
GenuineZero(s)
  -> incidencia angular nula
  -> pressao transversal nula
  -> delta(s) = 0
  -> Re(s) = 1/2
```

### Rota espectral CP — reserva posterior

```text
GenuineZero(s)
  -> spectralParameter(s) e autovalor de H_CP
  -> H_CP e autoadjunto
  -> spectralParameter(s) e real
  -> Re(s) = 1/2
```

As duas rotas compartilham toda a infraestrutura ate a equacao Genuine. A rota
espectral nao faz parte do import principal enquanto essa infraestrutura nao
estiver formalizada.

## Fase 0 — logica e higiene

Entregas:

- `OnCriticalLine`;
- `spectralParameter`;
- teorema condicional `hilbertPolya_implication`;
- estados de evidencia;
- proibicao mecanica e editorial de `sorry` e `axiom`.

Estado: os modulos importados pelo nucleo ativo passaram pelo kernel no
checkpoint 0.2.0. Os modulos de reserva continuam separados.

## Fase 1 — combinatoria finita do carry

Objetos:

- pares simetricos `(c-r,c+r)`;
- profundidade `v_p(n)`;
- representante balanceado modulo `p`;
- centro, perna, raio e evento de carry;
- shifts multiplicativos `S_p`;
- caixas finitas de indices.

Teoremas-alvo:

- `balancedRepresentative_existsUnique`;
- `primeDepth_eq_zero_iff_noCarry`;
- `mulShift_comm`;
- `horizontalAsOtherVerticals_finite`;
- `symmetricPair_midpoint`;
- versoes precisas das identidades XOR, depois de desambiguadas.

Tudo nesta fase deve ser provado primeiro em conjuntos finitos.

## Fase 2 — bracket e cancelamento exato

Objetos:

- `centeredSecondDifference`;
- `saturatedBracket`;
- canal direto finito;
- canal de pernas finito;
- canal de centros sobreviventes.

Teoremas-alvo:

- simetria no raio;
- linearidade do bracket;
- reindexacao das pernas por classes residuais;
- cancelamento literal perna a perna;
- identidade finita `direct - legs = centers + boundary`;
- descricao explicita do termo de fronteira.

Somente depois desta fase introduzimos potencias complexas.

Primeiro endpoint implementado:

```text
Genuine.finiteCancellation
C2.finite_genuine_cancellation
Cp.finite_genuine_cancellation
```

Esses endpoints estao `KERNEL_CHECKED`; nao usam resultados analiticos como
hipoteses.

Ponte de carry C2 implementada e verificada pelo kernel:

```text
OddLeg = {n : Nat // 3 <= n e n impar}
Incidence = {(c,n) // 4 <= c, 4 | c e n = c-1 ou n = c+1}
OddLeg equiv Incidence
```

O codominio inclui a perna, e nao apenas o centro: cada centro possui duas
pernas. Essa e a bijecao correta que permite reindexar uma soma sem perder
multiplicidade.

A igualdade de profundidades tambem foi verificada pelo kernel:

```text
effectiveDepth(n)
  = max (v_2(n-1)) (v_2(n+1))
  = v_2(adjacentCenter(n)).
```

Ela e a justificativa formal para transportar qualquer funcao de peso da
profundidade do canal direto para o bracket correspondente.

O endpoint de reindexacao esta verificado pelo kernel com bordo assinado
explicito:

```text
direct(legs)
  = expected(bracket incidences)
    + extra direct incidences
    - missing bracket incidences.
```

Para uma cobertura exata, os dois termos de bordo desaparecem. A primeira
caixa aritmetica C2 foi implementada com os centros `4,8,...,4M` e as duas
pernas de cada centro. O kernel verificou que a caixa induzida de pernas
recupera exatamente essas incidencias, logo extras e faltantes sao vazios.

A caixa de pernas tambem foi caracterizada diretamente como a enumeracao
`2k+3`, `k<2M`. Portanto ela contem exatamente os impares entre `3` e
`4M+1` e possui cardinalidade `2M`; ambos os fatos estao verificados pelo
kernel.

Os dois primeiros passos Cp estao verificados. Para primo impar `p`,
`ZMod.valMinAbs` fornece uma bijecao entre residuos nao nulos e offsets
balanceados, e a camera possui exatamente `p-1` pernas. Essa bijecao foi
elevada a uma bijecao global

```text
{n : Int // p nao divide n}
  equiv
{(c,a) // p divide c e a e offset balanceado},
```

com `n=c+a` e existencia/unicidade verificadas pelo kernel.

O transporte da profundidade Cp tambem esta verificado. Para cada perna `n`
nao multipla de `p`, a carta testa independentemente todos os offsets
balanceados `a` por meio de `v_p(n-a)`. O kernel provou

```text
p divide (n-a)  <->  a = offsetCanonico(n)

sup {v_p(n-a) | a offset balanceado}
  = v_p(centroCanonico(n)).
```

Logo a definicao da profundidade efetiva nao foi calibrada com o centro: ela
e um supremo finito sobre a carta inteira, e a bijecao prova qual termo
sobrevive. Pela convencao finita de `padicValInt`, `v_p(0)=0`; a profundidade
positiva foi registrada separadamente sob a hipotese `centroCanonico(n) != 0`.

A reindexacao ponderada Cp tambem esta verificada. Para qualquer caixa finita
de pernas `L` e qualquer caixa esperada de incidencias `E`, o kernel elaborou

```text
direct(L)
  = expected(E)
    + extra(incidenceImage(L), E)
    - missing(incidenceImage(L), E).
```

O peso do canal direto pode ser qualquer funcao da profundidade efetiva; na
incidencia, ele se torna a mesma funcao de `v_p(centro)`. Se a imagem da
bijecao coincide com `E`, o bordo desaparece por igualdade finita exata. O
kernel tambem verificou a primeira familia concreta que satisfaz essa
cobertura. Para `M` centros, ela usa

```text
centros = p, 2p, ..., Mp
offsets por centro = todos os p-1 offsets balanceados nao nulos
numero de incidencias = M(p-1).
```

A caixa direta e definida como a pre-imagem dessa caixa de incidencias pela
bijecao global Cp. Aplicar a bijecao de volta recupera literalmente a caixa
esperada; portanto extras e faltantes sao ambos vazios e a igualdade
ponderada nao possui termo de bordo.

O peso concreto do operador de ramo tambem foi ligado a essa infraestrutura.
Na meia abscissa, a profundidade `k` recebe massa `p^(-k)` e amplitude
`p^(-k/2)`. O kernel verificou `amplitude^2 = massa` e especializou a
reindexacao alinhada para esses pesos, sem bordo. Portanto o indice de
profundidade usado pelo ramo e a profundidade de carry ja provada pela camera.

A primeira passagem infinita controlada tambem foi verificada. Para primo
impar `p` e `sigma > 0`, a norma quadratica pura foi definida pela serie

```text
(p-1) * sum_{k>=1} p^(-2 k sigma)
```

e depois somada geometricamente. O kernel provou

```text
branchNormSq(p,sigma) = 1  <->  sigma = 1/2.
```

O tilt Cp de todas as pernas foi definido separadamente. Sua anulacao em
`delta = sigma-1/2 = 0` e a implicacao `defeito da norma = 0 -> tilt = 0`
estao verificadas. A volta tambem foi fechada para todo primo impar e centro
estritamente fora do semialcance da camera. O kernel verificou primeiro a
identidade finita

```text
cpTilt(p,delta,c)
  = (1/2) * sum_{a in A_p}
      [(c-a)^(-delta) + (c+a)^(-delta) - 2c^(-delta)].
```

Cada termo e estritamente positivo para `delta>0`, por convexidade estrita, e
estritamente negativo para `-1<delta<0`, por concavidade estrita. Como
`sigma>0` implica `delta=sigma-1/2>-1`, segue

```text
cpTiltAtSigma(p,sigma,c)=0  <->  sigma=1/2
```

quando `c>halfRange(p)`. Assim `TiltRigidityAt` agora possui uma construcao
canonica nesse dominio, e o tilt nulo equivale ao defeito nulo da norma. A
ponte `zero Genuine -> saturacao do ramo` permanece uma interface sem
instancia e e o proximo gargalo analitico.

A caracterizacao direta da pre-imagem alinhada por desigualdades e residuos
continua sendo um alvo finito independente, mas nao bloqueia os pesos ja
formalizados.

A primeira abertura finita da carta Cp tambem foi verificada. Definindo o
bloco completo com o offset zero recolocado, o kernel provou

```text
centerBlock(p,f,c) = legSum(p,f,c) + f(c),
bracket(p,f,c) = centerBlock(p,f,c) - p*f(c).
```

Para os centros `p,2p,...,Mp`, segue sem limites

```text
finiteChart(p,M,f)
  = blockPrefix(p,M,f)
    - p * sum_{k<M} f(p(k+1)).
```

O kernel tambem verificou o ladrilhamento minimo indispensavel

```text
blockPrefix(p,M,f)
  = sum_{1 <= n <= pM+halfRange(p)} f(n),
```

e portanto a forma literal da carta finita. Como o teorema vale para qualquer
`f`, nao sera criado um lema separado que apenas o especialize em `n^(-s)`.
Em vez disso, a primeira especializacao analitica foi feita somente onde
acrescenta conteudo: usando a multiplicatividade segura de `Complex.cpow` em
bases naturais nao negativas, o kernel verificou

```text
p * sum_{m=1}^M (p*m)^(-s)
  = p^(1-s) * sum_{m=1}^M m^(-s),
```

e substituiu esse termo na carta finita. Nenhum limite ou hipotese sobre
`Re(s)` e necessario nessa igualdade.

A passagem minima ao limite tambem esta verificada. Foi definido
`genuineDirichlet(s)` pela propria serie positiva `sum_(n>=1) n^(-s)`, sem
usar `riemannZeta` como definicao. Para `Re(s)>1`, o kernel provou a
somabilidade, a convergencia dos prefixos curto e longo e o limite

```text
finiteChart_p,M(s)
  -> (1-p^(1-s)) * genuineDirichlet(s).
```

O passo bracketado seguinte tambem foi fechado no nivel pontual. O kernel
verificou o ganho quadratico da segunda diferenca, sua especializacao a
`x^(-s)`, a somabilidade absoluta para `Re(s)>-1` e a identidade finita

```text
Genuine.Cp.bracket = saturatedBracket.
```

Consequentemente, os proprios prefixos `Genuine.Cp.finiteChart` convergem
para `bracketedDirichletChart` em `Re(s)>-1`. No semiplano comum `Re(s)>1`, a
unicidade do limite identifica essa carta com
`(1-p^(1-s))*genuineDirichlet(s)`.

O passo local-uniforme tambem foi fechado. Em torno de cada ponto
`z` com `Re(z)>-1`, escolhe-se a bola de raio `(Re(z)+1)/2`. Nela, o kernel
verificou uma p-serie somavel que domina simultaneamente todos os blocos,
independentemente do ponto da bola. O criterio de Weierstrass fornece a
holomorfia da cauda e da carta. Como o semiplano e preconexo, o principio da
identidade prova a unicidade da continuacao a partir de `Re(s)>1`.

Foi exportada a forma local em bolas, que e suficiente para holomorfia; nao
foi criado um corolario redundante quantificando separadamente sobre todo
compacto.

O fator da carta tambem foi fechado. O kernel verificou

```text
||p^(1-s)|| = p^(1-Re(s))
```

e concluiu que `1-p^(1-s)=0` so pode ocorrer em `Re(s)=1`. No interior da
faixa critica, a divisao e portanto regular. O objeto explicitamente
dependente da camera

```text
cpGenuineQuotient(p,s) = bracketedDirichletChart(p,s)/(1-p^(1-s))
```

e holomorfo na faixa, coincide com a serie Genuine original em `Re(s)>1`
para primo impar e possui os mesmos zeros da carta onde o fator nao zera.

A independencia prima tambem foi fechada sem importar uma zeta externa.
Primeiro o kernel prolongou a identidade cruzada

```text
(1-q^(1-s))*bracketedChart(p,s)
  = (1-p^(1-s))*bracketedChart(q,s)
```

de `Re(s)>1` para `Re(s)>-1`, antes de dividir. Somente no interior da faixa,
onde os dois fatores sao nao nulos, eles foram cancelados. Assim todos os
quocientes de primos impares coincidem com `genuineContinuation`; qualquer
carta prima impar possui exatamente os zeros desse mesmo objeto na faixa.
Preservacao de multiplicidades permanece separada e nao bloqueia a proxima
ponte Genuine--Green.

O gargalo Green foi decomposto numa interface mais informativa que a ponte
final. `SignedGreenCertificate` exige separadamente

```text
flux = 2*(sigma-1/2)*radialEnergy + boundary,
radialEnergy > 0,
genuine(s)=0 -> flux(s)=0,
genuine(s)=0 -> boundary(s)=0.
```

O kernel verificou que esses quatro fatos implicam `sigma=1/2`, anulam todo
tilt Cp e constroem uma `GenuineBranchBridge` para cada primo. Nenhum
certificado **real assinado** concreto foi construido: o traco de fluxo e o
fechamento do endpoint interno continuam sendo a obrigacao analitica aberta.

O primeiro nivel concreto da rota Green agora esta fechado. Em cortes finitos,
o kernel verificou a identidade Stokes com endpoints literais, o autovetor
`B_p g_s=p^(-s)g_s` e a fatoracao exata do Wronskiano refletido pela diferenca
dos autovalores. Para `s#=1-conj(s)`, o endpoint externo e exatamente
`1/(M+1)` e tende a zero. Isso nao cancela o endpoint inicial: ele deve ser
identificado separadamente com a porta bracketada do Genuine.

Esse nivel foi agora empacotado em `FiniteComplexGreenCertificate`. O fluxo
total e definido como Wronskiano mais corrente de Stokes, a energia e o
pareamento refletido e o bordo e formado pelos endpoints. A instancia Cp
satisfaz

```text
flux = coefficient*energy + boundary,
boundary = 1/(M+1)-1.
```

A formula explicita mostra que o bordo cru nao converge a zero: a porta
bracketada precisa cancelar o `-1` do endpoint interno.

## Fase 3 — pesos, series e caudas

Objetos:

- `n ^ (-s)` em `Complex`;
- correntes `J_{p,m,j}(s)`;
- normalizadores intrinsecos de carry;
- somas parciais e caudas.

Teoremas-alvo:

- representacao integral da segunda diferenca;
- majorante uniforme `O(m^(-sigma-2))` em vizinhancas locais — concluido;
- somabilidade para a regiao declarada — concluido;
- convergencia localmente uniforme suficiente para Weierstrass — concluido;
- holomorfia da carta — concluido;
- taxa de cauda na linha critica.

Nenhum `O(...)` de documento entra no kernel sem uma desigualdade com
constantes e quantificadores explicitos.

## Fase 4 — carta Genuine

Teoremas-alvo:

- identidade inicialmente em `Re(s) > 1`;
- continuacao por identidade holomorfa;
- nao anulacao do fator da carta no critical strip;
- equivalencia de zeros;
- preservacao de multiplicidade;
- compatibilidade entre cartas primas.

O arquivo `Analytic/Chart.lean` contem a logica abstrata
`chart = factor * genuine`; a instancia Cp concreta de continuacao esta em
`Analytic/CpBracketHolomorphic.lean`, e o fator regular e o quociente Cp estao
em `Analytic/CpGenuineQuotient.lean`. A compatibilidade entre cameras e o
representante Genuine canonico estao em `Analytic/CpGenuineCompatibility.lean`.

Ordem local atual para essa instancia:

1. **concluido:** passagem ao limite minima em `Re(s)>1`, onde os dois
   prefixos de Dirichlet convergem absolutamente;
2. **concluido:** identidade inicial do limite da carta com o Genuine definido
   pela serie positiva;
3. **concluido:** ganho de duas potencias, somabilidade absoluta pontual em
   `Re(s)>-1`, identificacao finita com o bracket Genuine e passagem dos
   prefixos ao limite;
4. **concluido:** majorante uniforme numa bola canonica em torno de cada ponto,
   holomorfia da carta bracketada e unicidade da continuacao pelo principio da
   identidade;
5. **concluido:** o fator so pode zerar em `Re(s)=1`; o quociente Cp e
   holomorfo na faixa, recupera a serie em `Re(s)>1` e seus zeros equivalem aos
   zeros da carta na faixa;
6. **concluido:** prolongar a identidade cruzada antes da divisao, cancelar
   fatores regulares na faixa e provar que todos os quocientes primos
   coincidem com um unico `genuineContinuation`;
7. **concluido:** construir o bulk Green em cortes finitos, provar o autovetor
   do bloco Cp, fatorar o fluxo refletido, controlar os endpoints e construir
   a instancia Cp concreta de `FiniteComplexGreenCertificate`;
8. **concluido:** retirar a fase dentro do bloco antes do Wronskiano, obter os
   autovalores reais `p^(-delta)` e `p^delta`, fatorar sua diferenca como
   `2*delta` vezes um cofator positivo e projetar a identidade finita para uma
   forma real assinada;
9. **proximo nucleo minimo:** provar a positividade da parte real da energia
   refletida finita, com hipoteses exatas e sem deduzi-la apenas da positividade
   do cofator radial;
10. identificar o endpoint inicial e a anulacao do fluxo com a porta
    bracketada de `genuineContinuation`, preservando o bordo literal;
11. controlar o limite e montar o `SignedGreenCertificate` concreto.
    Multiplicidades ficam
   como refinamento posterior, pois nao bloqueiam a implicacao simples sobre a
   localizacao dos zeros.

## Fase 5 — Hilbert ponderado e projecao

Objetos:

- indice disjunto das coordenadas `(p, tipo, m, j)`;
- peso `w_e`;
- espaco `lp`/`WeightedL2` apropriado;
- corrente `z(s)`;
- vetor de Riesz `k_e = 1/w_e`;
- funcional de sintese continuo;
- projecao `P_syn`.

Teoremas-alvo:

- `z(s)` pertence ao espaco;
- `k` pertence ao espaco;
- `inner k z = synthesis z`;
- `P_syn` e limitado;
- `P_syn^2 = P_syn`;
- `P_syn* = P_syn`;
- `P_syn z = 0` se, e somente se, o Genuine zera;
- o score finito e um quociente de Rayleigh da projecao finita.

Aqui fica formalmente separado:

- a projecao, cujos autovalores sao `0` e `1`;
- o parametro `t` no qual a corrente entra no kernel.

## Fase 6 — manometro transversal

Teoremas-alvo:

- definicao do perfil relativo `R(delta,t)`;
- curvatura discreta escalada;
- Hardy de carry;
- analise e sintese do frame;
- kernel exato do manometro:
  `M R(delta,t) = 0 <-> delta = 0`.

## Fase 7A — ponte direta

Alvo aberto:

```text
P_syn (z(s)) = 0 -> M (R(delta,t)) = 0
```

Subproblemas:

- operador explicito `S_CP_to_C2`;
- compatibilidade local de centros e raios;
- identidade com residual independente;
- controle uniforme de cauda e fronteira;
- proibicao de definir o residual tautologicamente.

## Fase 7B — realizacao Hilbert–Polya

Alvo aberto:

- construir um operador simetrico denso `A_CP`;
- definir mapas de fronteira independentes do parametro espectral;
- construir uma extensao `H_CP` com dominio fixo;
- provar a identidade secular com o Genuine completado;
- provar autoadjunticidade do dominio;
- provar espectro discreto, multiplicidades e ausencia de extras.

Ferramentas matematicas candidatas:

- triplas de fronteira e funcao de Weyl;
- funcoes de Herglotz/Nevanlinna;
- sistemas canonicos/de Branges;
- extensoes autoadjuntas de perturbacoes de posto finito.

Essas ferramentas sao candidatas, nao premissas estabelecidas.

## Fase 8 — teorema final

Somente depois de uma das fases 7 estar `KERNEL_CHECKED` sera criado um
arquivo chamado `RiemannHypothesis.lean`. Antes disso, esse nome nao aparece
como teorema do projeto.
