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

O proximo refinamento finito e caracterizar essa caixa de pernas diretamente
como os impares entre `3` e `4M+1`, provar sua cardinalidade `2M` e entao
transportar a construcao para Cp.

## Fase 3 — pesos, series e caudas

Objetos:

- `n ^ (-s)` em `Complex`;
- correntes `J_{p,m,j}(s)`;
- normalizadores intrinsecos de carry;
- somas parciais e caudas.

Teoremas-alvo:

- representacao integral da segunda diferenca;
- majorante uniforme `O(m^(-sigma-2))` em compactos;
- somabilidade para a regiao declarada;
- convergencia localmente uniforme;
- holomorfia da carta;
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

O arquivo `Analytic/Chart.lean` contem apenas a logica abstrata
`chart = factor * genuine`; a instancia CP concreta ainda deve ser construida.

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
