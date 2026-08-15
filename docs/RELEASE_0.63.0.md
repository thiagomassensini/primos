# CPFormal v0.63.0 — tilt cofinal e gate exato do carrier C3

## Estado da release

- release pai: `v0.62.0`;
- tag anotada: `v0.63.0`;
- Lean e Mathlib: `v4.32.0`;
- Zenodo concept DOI estável: `10.5281/zenodo.21483474`.

Esta release consolida três resultados posteriores à correção semântica de
`v0.62.0`. Ela não altera a definição de zero e não introduz a meia-abscissa
como hipótese de anulação.

## Proveniência mínima

O módulo `CpMinimalProvenanceQuotient` constrói o quociente canônico que
preserva simultaneamente o readout coarse e a informação Green. A construção
não escolhe pseudoinversa nem representante e identifica exatamente a
proveniência apagada pelo quociente coarse.

## Não compensação da cauda de tilt

Para todo parâmetro no strip aberto com parte real diferente de `1 / 2`, o
primeiro centro C3 completo domina estritamente todos os centros de tilt
posteriores. A constante explícita é

```math
\rho=\frac34\left(\frac65\right)^{3/2},
\qquad \rho^2=\frac{243}{250}<1.
```

Logo a série cofinal dos blocos de tilt não se autocancela fora do equilíbrio.
O teorema é anterior a qualquer hipótese de zero.

## Ledger exato do carrier

Para o tilt cofinal `W_infinity`, o remainder do carrier `R_infinity` e o
fator não nulo da câmera C3, Lean prova universalmente

```math
1+W_\infty(s)+R_\infty(s)
=a_3(s)\,\mathrm{Genuine}(s).
```

Consequentemente, no strip,

```math
1+R_\infty(s)=-W_\infty(s)
\quad\Longleftrightarrow\quad
\mathrm{Genuine}(s)=0.
```

Isso identifica o gate restante sem escondê-lo: proibir globalmente essa
compensação é equivalente à não anulação forte no strip. A release não declara
essa equivalência como prova do lado ainda aberto.

## Escopo lógico

A release prova que a cauda de centros completos do próprio tilt não apaga o
defeito central. Ela também prova que completude celular, `C0` e simples
reassociação escalar não fornecem, sozinhas, uma ortogonalidade do carrier.
Uma conclusão adicional precisa usar coerência do estado completo, endpoint e
bulk, e não redefinir zero como compatibilidade de massa.

## Verificação

O artefato publicável é o commit exato de `main` que passa:

```bash
bash scripts/static_audit.sh
lake build --wfail
```

A tag e a GitHub Release são criadas somente depois do workflow Lean verde
nesse mesmo SHA. A release do GitHub é o evento de arquivamento consumido pela
integração do Zenodo.
