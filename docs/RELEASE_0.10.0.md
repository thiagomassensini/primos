# Checkpoint 0.10.0 — rigidez de sinal do tilt Cp

Este checkpoint fecha a hipotese `TiltRigidityAt` no dominio natural em que
todas as pernas da carta permanecem positivas.

## Decomposicao em pares

Para a camera balanceada `A_p`, o kernel verificou a invariancia
`a in A_p <-> -a in A_p` e a identidade

```text
Theta_delta^(p)(c)
  = (1/2) * sum_{a in A_p}
      [(c-a)^(-delta) + (c+a)^(-delta) - 2c^(-delta)].
```

O fator `1/2` aparece porque cada par `±a` ocorre duas vezes na soma completa.
Nao ha truncamento, limite ou argumento numerico nessa identidade.

## Sinal de cada bracket

Se `c>halfRange(p)`, todas as pontas `c±a` sao positivas. Para cada offset
nao nulo:

- `delta>0`: `x^(-delta)` e estritamente convexa, logo o bracket e positivo;
- `-1<delta<0`: `x^(-delta)` e estritamente concava, logo o bracket e
  negativo;
- `delta=0`: o bracket e zero.

Como a camera de um primo impar e nao vazia, o sinal estrito sobrevive na
soma global.

## Rigidez na meia abscissa

Com `delta=sigma-1/2`, a hipotese `sigma>0` garante `delta>-1`. Portanto os
tres casos acima cobrem todo o dominio e o kernel conclui

```text
cpTiltAtSigma p sigma center = 0
  <-> sigma = 1/2
```

para primo impar e `center>halfRange(p)`. Foi construida uma prova canonica de
`TiltRigidityAt p center`, e tambem foi verificado

```text
branchDefect p sigma = 0
  <-> cpTiltAtSigma p sigma center = 0.
```

## O que permanece aberto

Esse resultado fecha a seta `tilt nulo -> meia abscissa`. Ele nao prova que
um zero Genuine produz tilt nulo. A estrutura `GenuineBranchBridge`, cujo
campo exige `genuine(s)=0 -> branchNormSq(p,Re(s))=1`, permanece sem instancia.

## Evidencia de compilacao

- repositorio privado: `thiagomassensini/primos`;
- branch: `agent/lean-kernel-audit`;
- pull request: `#1` (rascunho);
- commit matematico: `4ed11cfed623a94982a7ba3316f5a290c16fb4c9`;
- workflow run: `29647362054`;
- job verde: `88087733439`;
- resultado: auditoria estatica e `lake build --wfail` concluidos com sucesso.

## Endpoints principais

- `Analytic.Cp.cpLegTilt`;
- `Analytic.Cp.cpPairTilt`;
- `Analytic.Cp.cpTilt_eq_half_sum_pair`;
- `Analytic.Cp.cpPairTilt_pos_of_delta_pos`;
- `Analytic.Cp.cpPairTilt_neg_of_neg_one_lt_delta`;
- `Analytic.Cp.cpTilt_pos_of_delta_pos`;
- `Analytic.Cp.cpTilt_neg_of_neg_one_lt_delta`;
- `Analytic.Cp.tiltRigidityAt_of_halfRange_lt_center`;
- `Analytic.Cp.cpTiltAtSigma_eq_zero_iff_half`;
- `Analytic.Cp.branchDefect_eq_zero_iff_cpTiltAtSigma_eq_zero_of_admissible_center`.
