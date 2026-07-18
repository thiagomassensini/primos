# Checkpoint 0.5.0 — bijecao global centro--offset Cp

Este checkpoint fecha a ponte combinatoria global das cameras primas impares.

## Enunciado verificado pelo kernel

Fixe um primo impar `p`. Para cada inteiro `n` tal que `p` nao divide `n`,
existe um unico par `(c,a)` com:

- `p` divide o centro `c`;
- `a` pertence aos offsets balanceados nao nulos da camera Cp;
- `n = c + a`.

O offset `a` e o representante balanceado da classe de `n` em `ZMod p`; o
centro canonico e `c=n-a`.

## Endpoints Lean

- `Carry.Cp.Nonmultiple`;
- `Carry.Cp.Incidence`;
- `Carry.Cp.offsetOfNonmultiple`;
- `Carry.Cp.centerOfNonmultiple`;
- `Carry.Cp.dvd_centerOfNonmultiple`;
- `Carry.Cp.nonmultipleEquivIncidence`;
- `Carry.Cp.existsUnique_incidence`.

Arquivo principal: `CPFormal/Carry/CpGlobalIncidence.lean`.

## Evidencia de compilacao

- repositorio privado: `thiagomassensini/primos`;
- branch: `agent/lean-kernel-audit`;
- pull request: `#1` (rascunho);
- commit matematico: `e8b9cf7cedf15e7917d7837bb50bb6412d048ccb`;
- workflow run: `29638936254`;
- job: `88066026811`;
- resultado: auditoria estatica e `lake build --wfail` concluidos com sucesso.

## Relacao com a formalizacao antiga

`Library/Lean/GlobalDecomposition.lean` ja usava, em C2, o padrao de um
endereco global com avaliacao e existencia unica. O novo arquivo reaproveita
essa arquitetura conceitual, mas a prova Cp e independente e usa a bijecao
balanceada por `ZMod.valMinAbs` verificada no checkpoint anterior.

## O que continua aberto

O proximo passo e transportar a profundidade `v_p` da perna para o centro
canonico e construir caixas Cp alinhadas. Ainda nao ha aqui serie infinita,
identidade com zeta ou funcoes L, certificacao de zeros, operador
Hilbert--Polya autoadjunto ou prova da RH.
