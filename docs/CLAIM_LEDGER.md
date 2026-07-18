# Ledger de afirmacoes — checkpoint 0.7.0 Genuine-first

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
| CHP-001 | carta e fator vezes Genuine | PAPER_ARGUMENT | reindexacao e analise | formalizar primeiro finito |
| CHP-002 | fator da carta nao zera no critical strip | PAPER_ARGUMENT | modulo complexo | formalizar apos CHP-001 |
| HIL-001 | sintese possui vetor de Riesz ponderado | PAPER_ARGUMENT | somabilidade dos pesos | construir espaco |
| HIL-002 | `P_syn` e projecao ortogonal autoadjunta | PAPER_ARGUMENT | HIL-001 | formalizar API mathlib |
| NUM-001 | dez vales nos dez primeiros gammas | NUMERICAL | truncamento intervalar | manter fora da cadeia de prova |
| DIR-001 | kernel do manometro transversal e `delta=0` | PAPER_ARGUMENT | Hardy/frame | auditar fontes formais |
| BRG-001 | incidencia Genuine implica pressao transversal nula | OPEN_BRIDGE | HIL-002, DIR-001 | decompor em identidades locais |
| SPC-001 | Genuine completado e determinante secular de `H_CP` | OPEN_BRIDGE | CHP-001 | construir problema de fronteira |
| SPC-002 | `H_CP` e autoadjunto em dominio fixo | OPEN_BRIDGE | SPC-001 | indices de deficiencia/fronteira |
| RH-001 | todo zero Genuine esta na linha critica | BLOQUEADO | BRG-001 ou SPC-001+SPC-002 | nao enunciar como provado |

O checkpoint mais recente do nucleo ativo foi compilado pelo GitHub Actions no
commit `52afc4ffa81f0d62ed732b86de3c4c7f3537284a`, run `29640821068`.
Modulos mantidos apenas em `CPFormal.ResearchReserve` nao fazem parte dessa
certificacao. Consulte `AUDIT.md`.
