# CPFormal

Formalizacao limpa, incremental e auditavel da geometria de carry, brackets e
cartas primas, seguindo a ordem **Genuine first**.

## Regra central

O projeto nunca usa `sorry`, `axiom` ou um zero conhecido para fabricar o
operador que deveria explica-lo. Uma afirmacao so recebe o estado
`KERNEL_CHECKED` depois que `lake build` termina sem erros.

## Nucleo ativo

- pares simetricos e segunda diferenca centrada;
- bracket saturado finito e sua aditividade;
- comutacao dos shifts multiplicativos, primeiro esqueleto da planura;
- offsets balanceados da camera Cp;
- lei abstrata finita
  `canal direto - brackets = centros sobreviventes`;
- instancias locais e finitas para C2 e Cp;
- bijecao C2 entre pernas impares e incidencias centro-perna;
- igualdade entre profundidade efetiva da perna e profundidade do centro C2;
- reindexacao ponderada C2 com bordo `extras - faltantes` explicito;
- caixas C2 nos centros `4,8,...,4M` com cobertura exata e bordo vazio;
- identificacao dessas pernas com `3,5,...,4M+1` e cardinalidade `2M`;
- bijecao Cp entre offsets balanceados e residuos nao nulos modulo primo;
- cardinalidade `p-1` da camera balanceada Cp;
- bijecao global Cp entre inteiros nao multiplos de `p` e incidencias
  `(centro multiplo de p, offset balanceado)`;
- existencia e unicidade da decomposicao `n = centro + offset`;
- unicidade da perna balanceada que produz carry em cada carta Cp;
- igualdade entre a maior profundidade das pernas e a profundidade `v_p` do
  centro canonico;
- reindexacao ponderada Cp com bordo `extras - faltantes` explicito e corolario
  de cobertura exata;
- caixas Cp alinhadas nos centros `p,2p,...,Mp`, com todas as `p-1` pernas
  balanceadas de cada centro, cardinalidade `M(p-1)` e bordo vazio;
- peso critico de carry `p^(-k)`, amplitude `p^(-k/2)` e identidade
  `amplitude^2 = massa`, transportados sem bordo pela bijecao Cp;
- massa quadratica do operador de ramo definida pela serie
  `(p-1) * sum_{k>=1} p^(-2 k sigma)`;
- forma fechada da serie e criterio exato, para `sigma > 0`,
  `branchNormSq p sigma = 1 <-> sigma = 1/2`;
- tilt transversal de todas as `p-1` pernas da carta Cp e sua decomposicao
  exata como metade da soma dos brackets dos pares `±a`;
- sinal estrito do tilt, para centro fora da camera: negativo abaixo de
  `sigma=1/2`, nulo em `sigma=1/2` e positivo acima;
- rigidez canonica `tilt = 0 <-> sigma = 1/2` no semiplano `sigma>0`, e
  equivalencia entre tilt nulo e defeito nulo da norma;
- interface explicita, ainda sem instancia, para a ponte
  `zero Genuine -> saturacao do ramo`;
- ledger de afirmacoes, mapa de dependencias e caixa de ideias.

Os modulos projetivo e Hilbert--Polya permanecem preservados em
`CPFormal.ResearchReserve`, mas nao sao importados pelo nucleo ativo.

## Principio Genuine first

1. cancelamento finito literal;
2. bijecao carry entre pernas e centros;
3. pesos por profundidade;
4. passagem a series e controle de cauda;
5. identidade da carta e normalizador;
6. somente depois, zeros e pontes globais.

## Como executar

Com `elan` instalado:

```bash
bash scripts/audit.sh
```

Sem acesso ao compilador, a verificacao que nao imita o kernel e:

```bash
bash scripts/static_audit.sh
```

O projeto esta fixado em Lean/mathlib `v4.32.0`. Consulte `docs/AUDIT.md`
para o estado exato da verificacao pelo kernel neste ambiente.

## Integracao continua

`.github/workflows/lean.yml` executa a auditoria estatica e `lake build
--wfail` num runner oficial do GitHub Actions. Um selo verde desse workflow
permite promover os lemas compilados de `LEAN_STATEMENT` para
`KERNEL_CHECKED`; ele nao promove automaticamente pontes matematicas ainda
marcadas como abertas no ledger.

O checkpoint mais recente do nucleo ativo passou por essa verificacao no
commit `4ed11cfed623a94982a7ba3316f5a290c16fb4c9`, workflow run
`29647362054`. A certificacao cobre os imports de `CPFormal.lean`;
`CPFormal.ResearchReserve` permanece fora dela.

## Ordem de leitura

1. `docs/WORKING_AGREEMENT.md`
2. `docs/FORMALIZATION_PLAN.md`
3. `docs/CLAIM_LEDGER.md`
4. `docs/RELEASE_0.10.0.md`
5. `docs/VISION_INBOX.md`
6. `CPFormal/Genuine/FiniteCancellation.lean`
7. `CPFormal/Genuine/C2.lean`
8. `CPFormal/Genuine/Cp.lean`
9. `CPFormal/Carry/C2Adjacent.lean`
10. `CPFormal/Carry/C2Depth.lean`
11. `CPFormal/Carry/C2WeightedReindex.lean`
12. `CPFormal/Carry/C2AlignedBox.lean`
13. `CPFormal/Carry/CpBalancedResidue.lean`
14. `CPFormal/Carry/CpGlobalIncidence.lean`
15. `CPFormal/Carry/CpDepth.lean`
16. `CPFormal/Carry/CpWeightedReindex.lean`
17. `CPFormal/Carry/CpAlignedBox.lean`
18. `CPFormal/Carry/CpBranchWeight.lean`
19. `CPFormal/Analytic/CpBranchNorm.lean`
20. `CPFormal/Analytic/CpTilt.lean`
21. `CPFormal/Analytic/CpTiltRigidity.lean`
