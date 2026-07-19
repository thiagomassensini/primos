# Ledger de afirmacoes — checkpoint 0.21.0 Genuine-first

Estados usados:

- `VISION`: intuicao ainda sem enunciado unico;
- `LEAN_STATEMENT`: interface/enunciado Lean condicional;
- `PAPER_ARGUMENT`: argumento matematico fora do kernel;
- `NUMERICAL`: evidencia computacional;
- `KERNEL_CHECKED`: compilado sem axiomas nem `sorry`;
- `OPEN_BRIDGE`: teorema necessario ainda nao demonstrado.

| ID | Afirmacao | Estado atual | Dependencias | Proxima acao |
|---|---|---|---|---|
| LOG-001 | `Im(spectralParameter s)=0 <-> Re(s)=1/2` | LEAN_STATEMENT | aritmetica real | compilar |
| LOG-002 | correspondencia com espectro real implica linha critica | LEAN_STATEMENT | LOG-001 | compilar |
| FIN-001 | soma das pernas de um par e duas vezes o centro | KERNEL_CHECKED | inteiros | usar na reindexacao |
| FIN-002 | segunda diferenca e invariante por `r -> -r` | KERNEL_CHECKED | grupo aditivo | usar nas cameras |
| FIN-003 | bracket saturado e aditivo | KERNEL_CHECKED | FIN-002 | usar nas somas finitas |
| CAR-001 | shifts multiplicativos primos comutam | KERNEL_CHECKED | multiplicacao natural | construir enunciado de planura finita |
| CAR-002 | horizontal de uma base e soma/sombra das verticais restantes | VISION | fatoracao unica | escolher enunciado finito |
| XOR-001 | XOR de um par de gemeos detecta evento de carry | VISION/AMBIGUOUS | semantica do XOR | fixar operandos e codominio |
| GEN-001 | `legs - (legs - coefficient*center) = coefficient*center` | KERNEL_CHECKED | anel comutativo | reutilizar sem analise |
| GEN-002 | lei Genuine finita ponderada para centros arbitrarios | KERNEL_CHECKED | GEN-001, somas finitas | instanciar com pesos de carry |
| GEN-C2-001 | bracket C2 local deixa duas copias do centro | KERNEL_CHECKED | GEN-001 | ligar ao canal direto |
| GEN-C2-002 | canal C2 finito direto menos brackets deixa centros | KERNEL_CHECKED | GEN-002 | adicionar reindexacao e fronteira |
| GEN-CP-001 | offsets balanceados excluem zero e respeitam o semialcance | KERNEL_CHECKED | intervalos inteiros finitos | provar cardinalidade e cobertura residual |
| GEN-CP-002 | bracket Cp local deixa `p-1` copias do centro | KERNEL_CHECKED | GEN-001, GEN-CP-001 | ligar ao canal direto Cp |
| GEN-CP-003 | canal Cp finito direto menos brackets deixa centros | KERNEL_CHECKED | GEN-002, GEN-CP-002 | adicionar reindexacao Cp |
| GEN-CP-BLOCK | o bloco completo inclui exatamente as `p-1` pernas e uma copia do centro; para `p` impar possui cardinalidade `p` | KERNEL_CHECKED | GEN-CP-001, GEN-CARD-CP | usado na abertura da carta finita |
| GEN-CP-CHART-FIN | nos centros `p,2p,...,Mp`, os blocos ladrilham exatamente `1,...,pM+halfRange(p)` e a carta finita e esse prefixo literal menos `p` vezes a soma dos centros | KERNEL_CHECKED | GEN-CP-BLOCK, GEN-CP-002 | usado na carta finita de Dirichlet |
| GEN-CP-DIR-FIN | para o ramo principal positivo, `p sum_(m=1)^M (pm)^(-s) = p^(1-s) sum_(m=1)^M m^(-s)` e a carta finita e o prefixo longo menos esse termo | KERNEL_CHECKED | GEN-CP-CHART-FIN, multiplicatividade de `Complex.cpow` em naturais nao negativos | usado na passagem ao limite |
| GEN-CP-DIR-LIM | para primo impar e `Re(s)>1`, `finiteChart_p,M(s)` converge para `(1-p^(1-s))*genuineDirichlet(s)`, onde `genuineDirichlet` e a propria serie positiva | KERNEL_CHECKED | GEN-CP-DIR-FIN, somabilidade complexa de `n^(-s)`, convergencia dos prefixos | obter o ganho bracketado e decidir a extensao necessaria alem de `Re(s)>1` |
| GEN-CP-BRACKET-PAIR | para primo impar, o bracket Genuine por pernas balanceadas coincide exatamente com a soma saturada das segundas diferencas de raios `1,...,halfRange(p)` | KERNEL_CHECKED | GEN-CP-BLOCK, reindexacao finita dos intervalos positivos e negativos | usado para identificar cada prefixo analitico com `Genuine.Cp.finiteChart` |
| GEN-CP-BRACKET-BOUND | para `Re(s)>-1`, cada bloco bracketado possui majorante explicito por constante finita vezes `(k+1)^(-Re(s)-2)` | KERNEL_CHECKED | derivadas de `x^(-s)`, desigualdade de valor medio aplicada duas vezes | usado na somabilidade absoluta |
| GEN-CP-BRACKET-ABS | para primo `p` e `Re(s)>-1`, as normas dos blocos bracketados formam uma serie somavel | KERNEL_CHECKED | GEN-CP-BRACKET-BOUND, p-serie real | define a carta bracketada por `tsum` |
| GEN-CP-BRACKET-LIM | para primo impar e `Re(s)>-1`, os prefixos `Genuine.Cp.finiteChart p M (n^(-s))` convergem para `bracketedDirichletChart p s` | KERNEL_CHECKED | GEN-CP-BRACKET-PAIR, GEN-CP-BRACKET-ABS | usado na carta analitica |
| GEN-CP-BRACKET-COMMON | para primo impar e `Re(s)>1`, `bracketedDirichletChart p s = (1-p^(1-s))*genuineDirichlet(s)` | KERNEL_CHECKED | GEN-CP-DIR-LIM, GEN-CP-BRACKET-LIM, unicidade do limite | conjunto de coincidencia para o principio da identidade |
| GEN-CP-BRACKET-LOCAL | para cada `z` com `Re(z)>-1`, existe uma bola canonica e uma sequencia real somavel que domina uniformemente a norma de todo bloco em todos os pontos dessa bola | KERNEL_CHECKED | GEN-CP-BRACKET-BOUND, cota local de `||s(s+1)||`, p-serie deslocada | usado diretamente no criterio de Weierstrass; o corolario quantificado sobre compactos nao foi exportado separadamente |
| GEN-CP-BRACKET-HOLO | a cauda por `tsum` e a carta bracketada completa sao holomorfas em `Re(s)>-1` | KERNEL_CHECKED | GEN-CP-BRACKET-LOCAL, termos inteiros, criterio de Weierstrass | usado no principio da identidade |
| GEN-CP-FACTOR-REG | para primo `p`, `1-p^(1-s)=0` implica `Re(s)=1`; portanto o fator nao zera quando `Re(s) != 1`, em particular no interior da faixa critica | KERNEL_CHECKED | formula `||p^(1-s)||=p^(1-Re(s))`, monotonicidade estrita de `Real.rpow` | permite dividir a carta na faixa |
| GEN-CP-QUOTIENT | para primo impar e `Re(s)>1`, `cpGenuineQuotient p s = genuineDirichlet s` | KERNEL_CHECKED | GEN-CP-BRACKET-COMMON, GEN-CP-FACTOR-REG, cancelamento em corpo | ancora o quociente na serie Genuine original |
| GEN-CP-QUOTIENT-HOLO | para primo `p`, `cpGenuineQuotient p` e holomorfo em `0<Re(s)<1` | KERNEL_CHECKED | GEN-CP-BRACKET-HOLO, GEN-CP-FACTOR-REG, analiticidade do fator, quociente analitico | objeto Cp regular na faixa critica |
| GEN-CP-ZERO-EQ | no interior da faixa critica, `bracketedDirichletChart p s = 0` se e somente se `cpGenuineQuotient p s = 0` | KERNEL_CHECKED | GEN-CP-FACTOR-REG, definicao do quociente | usado na equivalencia global independente da camera |
| GEN-CP-CROSS | para primos impares `p,q`, `F_q * bracketedChart_p = F_p * bracketedChart_q` em todo `Re(s)>-1` | KERNEL_CHECKED | GEN-CP-BRACKET-COMMON, GEN-CP-BRACKET-HOLO, principio da identidade | cancelar os fatores somente onde ambos sao regulares |
| GEN-GENUINE-CANON | na faixa critica, todos os `cpGenuineQuotient p` de primos impares coincidem com um representante `genuineContinuation`, holomorfo na faixa e igual a serie Genuine em `Re(s)>1` | KERNEL_CHECKED | GEN-CP-CROSS, GEN-CP-FACTOR-REG, GEN-CP-QUOTIENT-HOLO | usar este unico escalar no certificado Green concreto |
| GEN-GLOBAL-ZERO-EQ | na faixa critica, os zeros de qualquer carta prima impar sao exatamente os zeros de `genuineContinuation` | KERNEL_CHECKED | GEN-GENUINE-CANON, GEN-CP-ZERO-EQ | formular o traco Green sem dependencia espuria da camera |
| GREEN-FIN-STOKES | o bulk discreto finito telescopa para o endpoint externo menos o endpoint inicial, com bordo definido literalmente e nao como residual | KERNEL_CHECKED | algebra em anel comutativo, soma finita | instanciar no traco bracketado |
| GREEN-CP-EIGEN-FIN | o somador de um bloco Cp completo satisfaz `B_p g_s = p^(-s) g_s` exatamente | KERNEL_CHECKED | telescopagem, multiplicatividade de `Complex.cpow` em naturais positivos | usado na normalizacao radial |
| GREEN-CP-FLUX-FIN | o Wronskiano finito Cp e a diferenca dos autovalores refletidos vezes o pareamento refletido finito, sem erro de bulk | KERNEL_CHECKED | GREEN-CP-EIGEN-FIN, linearidade de soma finita | usado no certificado complexo e no radial |
| GREEN-ENDPOINT-OUTER | para `s#=1-conj(s)`, o produto refletido no endpoint `M+1` e exatamente `(M+1)^(-1)` e tende a zero | KERNEL_CHECKED | conjugacao de `Complex.cpow`, soma de expoentes, limite do inverso natural | identificar e cancelar separadamente o endpoint inicial |
| GREEN-FIN-CERT | existe uma instancia Cp concreta de `FiniteComplexGreenCertificate`; seu fluxo total e Wronskiano mais Stokes, sua energia e o pareamento refletido e seu bordo e `1/(M+1)-1` | KERNEL_CHECKED | GREEN-FIN-STOKES, GREEN-CP-FLUX-FIN, GREEN-ENDPOINT-OUTER | usado como certificado exato anterior a parte real |
| GREEN-PHASE-RADIAL | multiplicar cada bloco por `p^(1/2+i Im(s))` antes de formar o Wronskiano transforma os autovalores de `s` e `1-conj(s)` nos reais `p^(-delta)` e `p^delta` | KERNEL_CHECKED | GREEN-CP-EIGEN-FIN, identidades de `Complex.cpow` | usado na fatoracao radial do fluxo |
| GREEN-RADIAL-COFACTOR | `p^delta-p^(-delta)=2*delta*A_p(delta)`, onde `A_p(0)=log p`, e `A_p(delta)>0` para todo primo `p` e todo `delta` real | KERNEL_CHECKED | monotonicidade estrita de `Real.rpow`, `log p>0` | usado na energia radial finita |
| GREEN-FIN-SIGNED | o fluxo Green real finito orientado satisfaz `flux=2*delta*finiteRadialGreenEnergy+boundary`, com todos os termos definidos explicitamente | KERNEL_CHECKED | GREEN-FIN-STOKES, GREEN-PHASE-RADIAL, GREEN-RADIAL-COFACTOR | provar positividade da parte real do pareamento refletido e ligar o bordo ao bracket Genuine |
| GEN-BIJ-C2 | pernas impares `n>=3` estao em bijecao com incidencias `(centro multiplo de 4, perna)` | KERNEL_CHECKED | aritmetica modular | usar na reindexacao ponderada |
| GEN-DEP-C2 | `max(v_2(n-1),v_2(n+1)) = v_2(adjacentCenter(n))` para `n` impar, `n>=3` | KERNEL_CHECKED | GEN-BIJ-C2, valoracao 2-adica | transportar o peso na soma finita |
| GEN-REINDEX-C2 | soma ponderada das pernas = soma das incidencias esperadas + extras - faltantes | KERNEL_CHECKED | GEN-BIJ-C2, GEN-DEP-C2, somas finitas | reutilizar nas caixas Cp |
| GEN-BOX-C2 | os centros `4,8,...,4M` com suas duas pernas possuem cobertura exata e bordo vazio | KERNEL_CHECKED | GEN-REINDEX-C2 | reutilizar como modelo das caixas Cp |
| GEN-INTERVAL-C2 | a caixa alinhada de pernas e exatamente `3,5,...,4M+1` e possui cardinalidade `2M` | KERNEL_CHECKED | GEN-BOX-C2, paridade | transportar a construcao para Cp |
| GEN-BIJ-CP | residuos nao nulos correspondem unicamente aos offsets balanceados | KERNEL_CHECKED | primo impar, `ZMod.valMinAbs` | usado na bijecao global Cp |
| GEN-CARD-CP | a camera balanceada de modulo primo impar possui exatamente `p-1` pernas | KERNEL_CHECKED | GEN-BIJ-CP, intervalo inteiro | usar na reindexacao Cp |
| GEN-GLOBAL-BIJ-CP | inteiros nao multiplos de `p` estao em bijecao com incidencias `(centro multiplo de p, offset balanceado)` e admitem decomposicao unica `n=c+a` | KERNEL_CHECKED | GEN-BIJ-CP, aritmetica modular | transportar a profundidade `v_p` |
| GEN-DEP-CP | somente o offset canonico satisfaz `p | (n-a)`, os demais possuem profundidade zero e `sup_a v_p(n-a) = v_p(centroCanonico(n))` | KERNEL_CHECKED | GEN-GLOBAL-BIJ-CP, valoracao `p`-adica, supremo finito | usado na reindexacao ponderada Cp |
| GEN-REINDEX-CP | soma ponderada das pernas Cp = soma das incidencias esperadas + extras - faltantes; cobertura exata elimina o bordo | KERNEL_CHECKED | GEN-GLOBAL-BIJ-CP, GEN-DEP-CP, somas finitas | construir caixas Cp alinhadas |
| GEN-BOX-CP | os centros `p,2p,...,Mp`, cada um com todos os `p-1` offsets balanceados, possuem `M(p-1)` incidencias, cobertura exata e bordo vazio | KERNEL_CHECKED | GEN-REINDEX-CP, GEN-CARD-CP | caracterizar diretamente a caixa de pernas |
| GEN-WEIGHT-CP | na profundidade de carry `k`, a massa critica e `p^(-k)`, a amplitude e `p^(-k/2)` e `amplitude^2 = massa`; a caixa alinhada transporta esse peso sem bordo | KERNEL_CHECKED | GEN-DEP-CP, GEN-BOX-CP, potencia real | usar nos coeficientes complexos `p^(-ks)` |
| BRANCH-NORM-CP | a norma quadratica pura e a serie `(p-1) sum_{k>=1} p^(-2k sigma)` e possui a forma geometrica fechada para `sigma>0` | KERNEL_CHECKED | GEN-CARD-CP, GEN-WEIGHT-CP, serie geometrica | ligar aos coeficientes complexos do ramo |
| BRANCH-HALF-CP | para primo impar e `sigma>0`, `branchNormSq p sigma = 1 <-> sigma=1/2` | KERNEL_CHECKED | BRANCH-NORM-CP, monotonicidade de `Real.rpow` | usar como barreira quadratica |
| TILT-CP-ANN | o tilt de todas as pernas Cp se anula em `sigma=1/2`; defeito nulo da norma implica tilt nulo em qualquer centro | KERNEL_CHECKED | BRANCH-HALF-CP, GEN-CARD-CP | usado na equivalencia norma--tilt |
| TILT-CP-PAIR | o tilt Cp e metade da soma dos brackets simetricos dos pares `±a` | KERNEL_CHECKED | GEN-CARD-CP, involucao dos offsets | usado na prova de sinal global |
| TILT-CP-SIGN | para primo impar, centro `c>halfRange(p)` e `sigma>0`, o tilt e negativo abaixo de `1/2` e positivo acima de `1/2` | KERNEL_CHECKED | TILT-CP-PAIR, convexidade/concavidade estritas de `x^(-delta)` | usado na rigidez |
| TILT-CP-RIGID | para primo impar, `sigma>0` e `c>halfRange(p)`, `tilt=0 <-> sigma=1/2`; nesse dominio, tilt nulo equivale a defeito nulo da norma | KERNEL_CHECKED | TILT-CP-SIGN, TILT-CP-ANN, BRANCH-HALF-CP | usar na ponte Genuine--ramo |
| GREEN-REDUCTION | uma identidade `flux = 2 delta energy + boundary`, com energia positiva e anulacao de fluxo e bordo nos zeros Genuine, implica `delta=0`, tilt nulo e uma instancia de `GenuineBranchBridge` | KERNEL_CHECKED | BRANCH-HALF-CP, TILT-CP-ANN, algebra real | construir os quatro campos para o Genuine concreto |
| GREEN-CERT | existe um `SignedGreenCertificate` concreto para a carta Genuine | OPEN_BRIDGE | GREEN-FIN-SIGNED esta fechado; faltam positividade uniforme/limite, anulacao do fluxo em zeros e identificacao/cancelamento do endpoint interno pelo traco | provar primeiro a positividade finita sem absorver o bordo por definicao |
| BRIDGE-GEN-BRANCH | zero Genuine implica saturacao da norma do ramo | OPEN_BRIDGE | GREEN-CERT ou outra identidade analitica independente | obter pelo teorema `SignedGreenCertificate.toGenuineBranchBridge` sem postular a instancia |
| RH-COND-CP | dada uma instancia de `GenuineBranchBridge`, todo zero no semiplano positivo possui parte real `1/2` e anula o tilt | KERNEL_CHECKED | BRIDGE-GEN-BRANCH, BRANCH-HALF-CP | teorema condicional compilado; nao confundir com uma instancia da ponte |
| CHP-001 | a carta bracketada e a unica funcao analitica em `Re(s)>-1` que coincide com `(1-p^(1-s))*genuineDirichlet(s)` em `Re(s)>1` | KERNEL_CHECKED | GEN-CP-BRACKET-COMMON, GEN-CP-BRACKET-HOLO, preconexidade do semiplano, principio da identidade | usar na equivalencia de zeros sem pressupor holomorfia da expressao Genuine totalizada fora de `Re(s)>1` |
| CHP-002 | o fator `1-p^(1-s)` nao zera no interior do critical strip; mais forte, todo zero do fator satisfaz `Re(s)=1` | KERNEL_CHECKED | modulo de `Complex.cpow` em base positiva e `Real.rpow` estrito | usado na construcao e zero-equivalencia do quociente Cp |
| CHP-003 | os quocientes `cpGenuineQuotient p` construidos por cameras primas distintas coincidem na faixa e definem um Genuine canonico independente de `p` | KERNEL_CHECKED | GEN-CP-CROSS, GEN-CP-FACTOR-REG, cancelamento em corpo | concluido sem identificacao externa com zeta |
| HIL-001 | sintese possui vetor de Riesz ponderado | PAPER_ARGUMENT | somabilidade dos pesos | construir espaco |
| HIL-002 | `P_syn` e projecao ortogonal autoadjunta | PAPER_ARGUMENT | HIL-001 | formalizar API mathlib |
| NUM-001 | dez vales nos dez primeiros gammas | NUMERICAL | truncamento intervalar | manter fora da cadeia de prova |
| DIR-001 | kernel do manometro transversal e `delta=0` | PAPER_ARGUMENT | Hardy/frame | auditar fontes formais |
| BRG-001 | incidencia Genuine implica pressao transversal nula | OPEN_BRIDGE | HIL-002, DIR-001 | decompor em identidades locais |
| SPC-001 | Genuine completado e determinante secular de `H_CP` | OPEN_BRIDGE | CHP-001 | construir problema de fronteira |
| SPC-002 | `H_CP` e autoadjunto em dominio fixo | OPEN_BRIDGE | SPC-001 | indices de deficiencia/fronteira |
| RH-001 | todo zero Genuine esta na linha critica | BLOQUEADO | BRG-001 ou SPC-001+SPC-002 | nao enunciar como provado |

O checkpoint matematico mais recente do nucleo ativo foi compilado pelo GitHub
Actions no commit `3326ae95321c9e3e3f0477f347a0ccf6f3ca8c02`, run
`29673514330`, job `88156612420`.
Modulos mantidos apenas em `CPFormal.ResearchReserve` nao fazem parte dessa
certificacao. Consulte `AUDIT.md`.
