# CPFormal v0.60.0 — Fontes G_pre finitas explicitas e preservacao raw completa

## Estado da release

- release pai: `v0.59.0`;
- tag anotada planejada: `v0.60.0`;
- Zenodo concept DOI estavel: `10.5281/zenodo.21483474`.

O workflow da release cria a tag somente no commit exato de `main` que passou
pela auditoria estatica, pelos testes numericos, pelo kernel Lean e pela
restauracao do bundle completo. A publicacao da GitHub Release e o evento
consumido pela integracao Zenodo para atribuir o DOI imutavel desta versao.

## O carry continua anterior aos observaveis

A teoria estrutural permanece quantificada sobre toda base inteira `b>1`.
Primos aparecem em certas cameras Cp e nos readouts Green como observaveis do
mesmo carrier; eles nao originam a massa critica, a meia-abscissa ou a
persistencia do carry.

O kernel ja separa os escopos:

```text
base material e carry:                 b >= 2
cartas naturais analiticas:            b >= 2
cameras naturais nao degeneradas:      b >= 3
especializacao Green Cp desta release: p : Nat.Primes
```

A C2 alinhada continua sendo o detector local de raio `1`, com uma perna de
cada lado. Sua implementacao pelo parametro nativo `4` nao a identifica com
uma C4 geometrica de duas pernas por lado.

## Extracao finita base-neutra

O novo modulo `CpNativeGpreFiniteTowerCollapse` fatora literalmente cada
coordenada tipada de proveniencia `G_pre` em:

```text
kernel aritmetico/canto/orientacao/role
  * perfil material da torre.
```

Ele constroi a fonte adjunta no nivel material e prova que o inner product com
o perfil da mesma base e tempo recupera exatamente o readout real. A identidade
vale para uma coordenada, para uma fibra finita e para pesos complexos
arbitrarios escolhidos antes da leitura. Peso zero produz readout zero.

Os campos legados `towerPrime` e `arithmeticPrime` sao rotulos `ℕ`; eles nao
carregam um certificado de primalidade. Portanto esta extracao nao restringe o
carry aos primos.

## Fonte TFVD--log-jet--Green nao vacua

O modulo `CpNativeGpreTfvdCommutatorTowerSource` aplica a extracao ao wedge
refletido ordinario/log-jet. A formulacao dos drafts #40/#42 exigia uma
coordenada ativa na celula zero, mas o proprio kernel prova que toda coordenada
nativa nessa celula e zero. A release nao conserva essa contradicao como
premissa ativa.

O reparo construtivo usa, para a aresta analitica `n`:

```text
celula nativa = p * (n + 1)
nivel material = n + 1.
```

O Lean prova que a coordenada canonica e ativa para todo observavel primo `p`,
tempo `tau` e aresta `n`. Em seguida, prova sem atlas assumido que a soma finita
das fontes tem como momento exatamente o trace normalizado do comutador e,
para `3*M` arestas, exatamente o bulk Green log-jet finito existente.

Os quatro valores usados no wedge sao o canal ordinario e o log-jet em `s`,
mais os dois canais no parametro refletido. Eles nao sao quatro pernas
geometricas. O resultado e finito e camera-a-camera.

## Ponto cego global sem perda de energia

O checkpoint anterior permanece ativo. Para `s` na faixa critica:

```text
genuineContinuation s = 0
  <-> todas as cameras naturais b >= 3 sao cegas em s.
```

Nesse locus, para cada base fixa, a sequencia de resultantes finitas converge a
zero; essa afirmacao nao e uniforme em `b`. Ao mesmo tempo,
`infiniteReflectedGreenEnergy_pos` mantem uma serie Green refletida construida
independentemente estritamente positiva. A nova fonte finita explicita realiza
o bulk radial vezes o pareamento Green dentro de cada camera; ela nao identifica
a energia positiva isolada nem as fontes de cameras distintas como um unico
estado pre-compressao.

## Preservacao sem perda

Esta release incorpora:

- as normalizacoes verdes mais recentes dos PRs #40/#42;
- o reparo nao vacuo da fonte de comutador;
- o registro unico `ops/v0.56.0-preservation-confirmed.json`, incluindo o DOI
  Zenodo `10.5281/zenodo.21735211`;
- as 22 fontes recuperadas em forma byte-exata sob
  `docs/recovered/2026-08-01/raw/`, com manifesto SHA-256;
- o manifesto pos-v0.59 de branches, PRs, resultados ativos e workflows
  historicos deliberadamente nao reativados.

Nenhuma branch historica e apagada. O publisher busca todas as branches, tags
e refs de heads de pull requests, constroi um bundle completo, restaura um
mirror limpo, executa `git fsck --full --strict`, compara os manifests de refs
e publica seis assets protegidos por SHA-256.

## O que esta release nao afirma

Esta release nao prova:

- que as fontes finitas de cameras diferentes formem um unico estado;
- uma cota uniforme ou passagem ao limite desses estados;
- que um zero Genuine anule o tilt, o bulk ou o fluxo Green;
- `GenuineStrongNonvanishingInStrip`;
- `RiemannHypothesis` da Mathlib;
- o `GREEN-NATCAM-INTERTWINER`;
- um operador de Hilbert--Polya.

Ela prova uma etapa de proveniencia genuinamente nova: cada bulk Green log-jet
finito da especializacao Cp e um momento nativo de uma fonte explicita,
construida das arestas antes da leitura e apoiada em coordenadas positivas e
distintas. A meia-abscissa continua vindo da convexidade/concavidade do carry;
nenhum estado e escolhido a partir da conclusao.

## Protocolo de publicacao

Antes de publicar, o workflow `v0.60.0` executa:

```bash
bash scripts/static_audit.sh

python -m unittest -v \
  experiments/test_c2_real_rotation_operator.py \
  experiments/test_c2_real_rotation_minimal.py \
  experiments/test_cp_branch_tilt_operator.py

lake build --wfail
```

Somente depois de todos os checks verdes e da restauracao integral do bundle o
workflow cria a tag anotada no `main` auditado, publica a release com o corpo
deste arquivo e verifica por attestation ou por download mais SHA-256 os seis
assets de recuperacao.
