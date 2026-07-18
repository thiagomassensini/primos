# Ledger de afirmacoes — versao 0.2.0 Genuine-first

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
| FIN-001 | soma das pernas de um par e duas vezes o centro | LEAN_STATEMENT | inteiros | compilar |
| FIN-002 | segunda diferenca e invariante por `r -> -r` | LEAN_STATEMENT | grupo aditivo | compilar |
| FIN-003 | bracket saturado e aditivo | LEAN_STATEMENT | FIN-002 | compilar |
| CAR-001 | shifts multiplicativos primos comutam | LEAN_STATEMENT | multiplicacao natural | compilar |
| CAR-002 | horizontal de uma base e soma/sombra das verticais restantes | VISION | fatoracao unica | escolher enunciado finito |
| XOR-001 | XOR de um par de gemeos detecta evento de carry | VISION/AMBIGUOUS | semantica do XOR | fixar operandos e codominio |
| GEN-001 | `legs - (legs - coefficient*center) = coefficient*center` | LEAN_STATEMENT | anel comutativo | compilar |
| GEN-002 | lei Genuine finita ponderada para centros arbitrarios | LEAN_STATEMENT | GEN-001, somas finitas | compilar |
| GEN-C2-001 | bracket C2 local deixa duas copias do centro | LEAN_STATEMENT | GEN-001 | compilar |
| GEN-C2-002 | canal C2 finito direto menos brackets deixa centros | LEAN_STATEMENT | GEN-002 | compilar |
| GEN-CP-001 | offsets balanceados excluem zero e respeitam o semialcance | LEAN_STATEMENT | intervalos inteiros finitos | compilar |
| GEN-CP-002 | bracket Cp local deixa `p-1` copias do centro | LEAN_STATEMENT | GEN-001, GEN-CP-001 | compilar |
| GEN-CP-003 | canal Cp finito direto menos brackets deixa centros | LEAN_STATEMENT | GEN-002, GEN-CP-002 | compilar |
| GEN-BIJ-C2 | pernas impares `n>=3` estao em bijecao com incidencias `(centro multiplo de 4, perna)` | LEAN_STATEMENT | aritmetica modular | compilar; depois ligar a profundidade `v_2` |
| GEN-DEP-C2 | `max(v_2(n-1),v_2(n+1)) = v_2(adjacentCenter(n))` para `n` impar, `n>=3` | LEAN_STATEMENT | GEN-BIJ-C2, valoracao 2-adica | compilar; usar na reindexacao ponderada |
| GEN-BIJ-CP | residuos nao nulos correspondem unicamente aos offsets balanceados | OPEN_BRIDGE | primo impar, aritmetica modular | formalizar bijecao |
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

`LEAN_STATEMENT` nao sera promovido automaticamente a `KERNEL_CHECKED`: o
executavel Lean foi instalado, mas o sandbox bloqueou sua localizacao interna
antes da elaboracao. Consulte `AUDIT.md`.
