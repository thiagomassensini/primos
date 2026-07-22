# Checkpoint 0.4.0 — intervalo C2 e primeira ponte Cp

Este checkpoint torna explicita a caixa aritmetica C2 e inicia o transporte
Genuine-first para cameras primas impares.

## Resultados C2 verificados pelo kernel

- os indices pares da enumeracao de pernas sao pernas esquerdas;
- os indices impares sao pernas direitas;
- a caixa puxada das incidencias e literalmente `3,5,...,4M+1`;
- pertencer a caixa equivale a estar abaixo de `4M+1` dentro do tipo das
  pernas impares `n>=3`;
- a caixa possui exatamente `2M` pernas.

## Resultados Cp verificados pelo kernel

Para primo impar `p`:

- cada offset balanceado determina um residuo nao nulo de `ZMod p`;
- `ZMod.valMinAbs` leva cada residuo nao nulo ao offset balanceado canonico;
- as duas transformacoes sao inversas;
- a camera balanceada possui exatamente `p-1` pernas.

Arquivos principais:

- `CPFormal/Carry/C2AlignedBox.lean`;
- `CPFormal/Carry/CpBalancedResidue.lean`.

## Evidencia de compilacao

- repositorio privado: `thiagomassensini/primos`;
- branch: `agent/lean-kernel-audit`;
- pull request: `#1` (rascunho);
- checkpoint C2: commit `b6cdb634a1bbb25eb56709e964d9738e4d001e26`,
  run `29636657680`;
- checkpoint Cp: commit `211e2a09fa5312c5fb851de9f4a71f05209b0b24`,
  run `29637023211`;
- resultado: `lake build --wfail` concluido com sucesso nos dois checkpoints.

## O que continua aberto

Ainda falta a bijecao global entre inteiros nao multiplos de `p` e incidencias
centro--offset, o transporte da profundidade `v_p`, as caixas Cp alinhadas e a
passagem analitica. Nao ha aqui identidade com zeta, certificacao de zeros,
operador de Hilbert--Polya ou prova da RH.
