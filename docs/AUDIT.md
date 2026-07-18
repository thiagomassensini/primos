# Auditoria Genuine-first

## Verificacoes realizadas

- projeto isolado em diretorio novo;
- toolchain e mathlib fixados na mesma versao;
- busca textual por `sorry` e `axiom` prevista antes de cada release;
- cadeia final da RH nao foi declarada como teorema concreto;
- zeros numericos nao aparecem no codigo Lean;
- interfaces condicionais deixam as pontes como campos obrigatorios.
- `scripts/static_audit.sh` verifica imports locais, sintaxe dos scripts e a
  ausencia textual de `sorry`/`axiom` local sem fingir que substitui o kernel.

## Estado do toolchain

- Elan e Lean `v4.32.0` foram instalados isoladamente em `.elan/`;
- a arvore de dependencias da mathlib foi baixada e o manifesto foi criado;
- o sandbox impede `IO.appPath`, usado pelo Lean para localizar o proprio
  executavel;
- por isso o `lake build` falhou antes da elaboracao dos arquivos do projeto,
  com `error: failed to locate application`.

O bloqueio local foi contornado de forma auditavel pelo GitHub Actions, sem
alterar o executavel nem as regras do sandbox.

Primeiro comando obrigatorio num ambiente Lean:

```bash
bash scripts/audit.sh
```

Auditoria estrutural, utilizavel mesmo quando o compilador estiver bloqueado:

```bash
bash scripts/static_audit.sh
```

Se houver erro de elaboracao, o estado continua `LEAN_STATEMENT` ate a correcao
e nova compilacao completa.

## GitHub Actions

O workflow `.github/workflows/lean.yml` usa `leanprover/lean-action@v1` num
runner `ubuntu-latest`, roda primeiro `scripts/static_audit.sh` e depois
`lake build --wfail`. O workflow e uma alternativa limpa ao compilador local
quando o sandbox impede a inicializacao do Lean.

## Certificacao do nucleo ativo

- repositorio privado: `thiagomassensini/primos`;
- pull request de auditoria: `#1`;
- branch: `agent/lean-kernel-audit`;
- commit certificado: `2a29c850389c888c6f1b5bde2dcb899fd261b559`;
- workflow run: `29634840124` (`Lean kernel audit`, run number 9);
- resultado: `success` em `lake build --wfail`;
- Lean: `v4.32.0`;
- mathlib: revisao fixada pelo `lake-manifest.json`.

## Checkpoint ponderado C2

- commit certificado: `0cc016b69419b811cbf12867f46605280ecdf7db`;
- workflow run: `29635654651` (`Lean kernel audit`, run number 17);
- job: `88057413962` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`;
- novo alvo compilado: `CPFormal.Carry.C2WeightedReindex`.

Esse checkpoint certifica a bijecao finita, o transporte do peso de
profundidade e a identidade

```text
direct = expected + extra - missing.
```

Ele nao certifica uma escolha concreta de caixas infinitas, convergencia,
identidade com zeta, equivalencia de zeros ou RH.

## Checkpoint de caixa alinhada C2

- commit certificado: `45b7fe8bb761117609054f0b448c8c11db375b78`;
- workflow run: `29636078858` (`Lean kernel audit`, run number 20);
- job: `88058546887` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`;
- novo alvo compilado: `CPFormal.Carry.C2AlignedBox`.

Esse checkpoint define concretamente os centros `4,8,...,4M`, inclui as duas
pernas de cada centro e prova que a caixa de pernas transportada pela bijecao
recupera exatamente essas incidencias. Portanto os Finsets de extras e de
faltantes sao ambos vazios e a reindexacao ponderada nao possui termo de
bordo.

## Checkpoint de intervalo impar C2

- commit certificado: `b6cdb634a1bbb25eb56709e964d9738e4d001e26`;
- workflow run: `29636657680` (`Lean kernel audit`, run number 25);
- job: `88060082966` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`.

O kernel verificou que a caixa de pernas puxada das incidencias e literalmente
a enumeracao `2k+3`, para `k<2M`. Em particular, seus elementos sao exatamente
os impares de `3` a `4M+1` e sua cardinalidade e `2M`.

## Checkpoint de residuos balanceados Cp

- commit certificado: `211e2a09fa5312c5fb851de9f4a71f05209b0b24`;
- workflow run: `29637023211` (`Lean kernel audit`, run number 27);
- job: `88061047891` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`;
- novo alvo compilado: `CPFormal.Carry.CpBalancedResidue`.

Para primo impar `p`, o kernel verificou a equivalencia entre offsets
balanceados e residuos nao nulos de `ZMod p`. A inversa usa
`ZMod.valMinAbs`, e a camera possui cardinalidade `p-1`.

## Checkpoint da bijecao global Cp

- commit certificado: `e8b9cf7cedf15e7917d7837bb50bb6412d048ccb`;
- workflow run: `29638936254` (`Lean kernel audit`, run number 34);
- job: `88066026811` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`;
- novo alvo compilado: `CPFormal.Carry.CpGlobalIncidence`.

Para primo impar `p`, o kernel verificou que todo inteiro nao divisivel por
`p` possui um unico offset balanceado `a`; o numero `c=n-a` e divisivel por
`p`, e a correspondencia `n <-> (c,a)` e uma equivalencia. Tambem foi
elaborada diretamente a forma existencial unica `∃! (c,a), n=c+a` dentro do
tipo de incidencias.

O alvo compilado e `CPFormal.lean`, isto e, o nucleo Genuine-first. O modulo
`CPFormal.ResearchReserve` e seus imports espectrais/projetivos nao foram
promovidos por esse run.
