# Auditoria do bootstrap 0.2.0 Genuine-first

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

O alvo compilado e `CPFormal.lean`, isto e, o nucleo Genuine-first. O modulo
`CPFormal.ResearchReserve` e seus imports espectrais/projetivos nao foram
promovidos por esse run.
