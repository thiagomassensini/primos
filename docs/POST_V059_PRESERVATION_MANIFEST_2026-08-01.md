# Manifesto de preservacao pos-v0.59 — 2026-08-01

## Autoridade e escopo

Este manifesto registra a reconciliacao executada depois do checkpoint
`v0.59.0`. Ele separa tres obrigacoes:

1. preservar literalmente fontes, branches, tags e heads de pull requests;
2. incorporar em `main` todo conteudo matematico verde e nao circular;
3. manter fora do nucleo ativo workflows obsoletos e formulacoes vacuas,
   conservando-os no historico e no bundle completo.

A base auditada foi `main` em
`865e757addd1ce1d8723a5ae0c8013571413e2f6`. O checkpoint matematico
`v0.59.0` aponta para
`48e0c3766c4929b9e9613577d2adab1fed0f204c`; a PR #41 corrigiu e verificou a
publicacao sem reescrever esse tag.

## Verificacao da v0.59.0

- Lean no `main`: run `30689940527`, 8.859 jobs, verde;
- guard de preservacao v0.55: run `30689940523`, verde;
- publisher/repair v0.59: run `30689940512`, verde;
- corpo da release byte-identico a `docs/RELEASE_0.59.0.md`;
- seis assets presentes, baixados e validados por SHA-256;
- Zenodo concept DOI: `10.5281/zenodo.21483474`;
- Zenodo version DOI da v0.59.0: `10.5281/zenodo.21736226`.

## Pull requests e heads reavaliados

Os SHAs abaixo foram relidos no GitHub imediatamente antes desta integracao.
Nenhuma branch foi apagada ou atualizada com force-push.

| PR | Head auditado | Destino de preservacao |
|---|---|---|
| #26 | `68724075d7d44f7c6efb6cfabfc70030bb295945` | conteudo Lean ja ativo e importado por #39/v0.59; branch preservada |
| #31 | `9038d18de17a9008a93c04385fcabab3e4d3b6c4` | fronteira de confinamento ja ativa; nenhuma instancia global declarada |
| #32 | `f21517a027b2ef130102f5c72ab979e88b305dea` | fronteira C2 ja ativa; a ativacao continua equivalente ao gate global |
| #35/#36 | `bd417489d22f2d9cb38b7577432eccf9f5e0ded7` | JSON unico recuperado em `ops/v0.56.0-preservation-confirmed.json`; branches preservadas |
| #38 | `449ecb768d798dbe547dfda38ccb85552d6311d7` | workflow historico preservado, mas nao ativado: sua exigencia `immutable=true` nao corresponde ao repositorio; o fallback SHA-256 ativo o substitui |
| #40 | `2041ea48ea6f0aa40c293b619fd5e8d9d10ef83e` | conteudo finito reaproveitado e reparado nesta integracao; branch original preservada |
| #42 | `7f43f9fc3a42915a7f71f02fe2629b96bcde1ba7` | normalizacao de cancelamento incorporada; a fonte de prefixo vacua foi substituida por uma construcao ativa explicita; branch original preservada |

Os heads #26, #31, #32, #35, #36 e #38 ja estavam alcançaveis no bundle
completo v0.59. Os heads posteriores #40/#42 entram no bundle completo v0.60,
junto com suas formulacoes historicas e com o reparo ativo.

## Arquivo raw byte-exato

As 22 fontes entregues na sessao interrompida estao em
`docs/recovered/2026-08-01/raw/`:

- 7 uploads diretos, incluindo o companion Python;
- 11 documentos de contexto adicionais;
- 4 drafts Lean.

Cada arquivo raw e byte-identico a sua fonte no workspace. O manifesto
`raw/SHA256SUMS.txt` e a autoridade criptografica. As copias legiveis no nivel
superior podem normalizar whitespace ou corrigir comentarios; elas nao
substituem o arquivo literal.

O registro operacional unico da PR #35/#36 tambem foi recuperado. Ele confirma
a v0.56.0 e o DOI Zenodo `10.5281/zenodo.21735211`.

## Conteudo matematico promovido

`CpNativeGpreFiniteTowerCollapse` fecha a extracao adjunta finita de cada
coordenada de proveniencia. Seus rotulos naturais historicamente chamados
`towerPrime` e `arithmeticPrime` nao contem prova de primalidade: esta camada
e valida para rotulos de base naturais e, em particular, para toda base
material inteira `b>1` usada pela teoria do carry.

`CpNativeGpreTfvdCommutatorTowerSource` fecha uma especializacao adicional,
finita e camera-a-camera, para observaveis primos. A aresta analitica `n` e
colocada na celula positiva `p*(n+1)` e no nivel material distinto `n+1`; o
kernel prova a atividade da coordenada e identifica o momento do prefixo com o
bulk Green log-jet finito. Isto remove a condicao impossivel dos drafts, que
exigia simultaneamente coeficiente nulo e atividade na celula zero.

Os quatro escalares do wedge sao os canais ordinario/log-jet em `s` e no ponto
refletido. Nao representam quatro pernas geometricas. A C2 alinhada continua
com raio `1`, uma perna de cada lado; o parametro nativo `4` nao a transforma
numa C4 geometrica.

## Fronteira que permanece aberta

A integracao nao declara nem deriva:

- um unico estado comum para todas as bases ou cameras primas;
- cota uniforme desses estados e passagem ao limite infinito;
- `genuineContinuation s = 0 -> cpTiltAtSigma ... = 0`;
- `GenuineStrongNonvanishingInStrip` ou `RiemannHypothesis`;
- um intertwiner `GREEN-NATCAM-INTERTWINER`.

O ponto cego global e a energia positiva continuam resultados distintos e
compilados: todo zero Genuine apaga simultaneamente as cameras naturais nao
degeneradas e, para cada base fixa, sua sequencia de resultantes finitas tende
a zero, enquanto uma serie Green refletida construida independentemente
permanece estritamente positiva no mesmo `s`. O novo momento finito le o bulk
radial vezes o pareamento Green; ele nao identifica a energia positiva isolada
com um estado comum. Construir essa identificacao ainda e a obrigacao tipada,
nao uma hipotese implicita.

## Resultado de preservacao

Nao foi encontrado modulo Lean de pesquisa historico unico e verde fora da
arvore ativa, excetuados os dois modulos posteriores #40/#42 agora integrados.
Workflows verificadores obsoletos permanecem alcançaveis por suas branches e
pelos bundles; nao sao executados como autoridade atual. O publisher v0.60
voltará a capturar todas as branches, tags e refs `pull/*/head`, restaurar o
bundle em mirror limpo, executar `git fsck --full --strict` e comparar o
manifesto de refs antes da release.
