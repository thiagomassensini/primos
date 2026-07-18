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

O nucleo ativo passou por essa verificacao no commit
`2a29c850389c888c6f1b5bde2dcb899fd261b559`. A certificacao cobre os imports
de `CPFormal.lean`; `CPFormal.ResearchReserve` permanece fora dela.

## Ordem de leitura

1. `docs/WORKING_AGREEMENT.md`
2. `docs/FORMALIZATION_PLAN.md`
3. `docs/CLAIM_LEDGER.md`
4. `docs/RELEASE_0.2.0.md`
5. `docs/VISION_INBOX.md`
6. `CPFormal/Genuine/FiniteCancellation.lean`
7. `CPFormal/Genuine/C2.lean`
8. `CPFormal/Genuine/Cp.lean`
9. `CPFormal/Carry/C2Adjacent.lean`
10. `CPFormal/Carry/C2Depth.lean`
