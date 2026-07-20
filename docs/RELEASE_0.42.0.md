# Checkpoint 0.42 — sintese escalar e setor fechado de proveniencia

## Coracao

O checkpoint 0.27 provou que comprimir as portas antes do pareamento produz
interferencia off-diagonal. O 0.42 abre agora essa compressao por completo.

Para uma familia finita `z_0,...,z_(M-1)`, a sintese escalar e

```text
S_M(z) = sum_{m<M} z_m.
```

O kernel escalado da sintese foi definido sem divisao por

```text
K_M(z)_m = M * z_m - S_M(z).
```

O kernel prova literalmente

```text
sum_{m<M} K_M(z)_m = 0.
```

Sua primitiva causal de prefixos comeca e termina em zero:

```text
P_M(z,0) = 0,
P_M(z,k+1) - P_M(z,k) = K_M(z)_k,
P_M(z,M) = 0.
```

Portanto a informacao invisivel ao mostrador escalar nao desaparece. Ela e
um fluxo fechado, com proveniencia coordenada preservada.

## Ledger de pareamento

Para duas familias `f` e `g`, o kernel verifica a identidade exata

```text
M * conj(S_M(f)) * S_M(g)
  + sum_m conj(K_M(f)_m) * K_M(g)_m
= M^2 * sum_m conj(f_m) * g_m.
```

O lado direito pareia primeiro o mesmo registro com o mesmo registro e so
depois sintetiza. O primeiro termo do lado esquerdo e o observavel escalar;
o segundo e todo o setor que esse observador nao ve.

A versao Wronskiana vale para quatro portas arbitrarias:

```text
M * W_scalar + W_kernel = M^2 * W_diagonal.
```

Combinando-a com a decomposicao do 0.27,

```text
W_scalar = W_diagonal + W_offDiagonal,
```

obtem-se o ledger novo

```text
M * W_offDiagonal + W_kernel
  = (M^2 - M) * W_diagonal.
```

Assim o off-diagonal deixa de ser uma caixa-preta: ele e determinado pela
diagonal e pelo fluxo fechado da sintese.

## Reencontro com a segunda diferenca

Usando o 0.41, a porta angular finita foi aberta sem alias:

```text
finiteCanonicalAngularTrace(M,s)
  = 1
    + sum_{k<M} centeredSecondDifference(
        dirichletTerm(s), alignedCenter(3,k), 1)
    - positiveDirichletValue(s,3M).
```

Ou seja, a sintese escalar observada e literalmente a soma dos mesmos
brackets de segunda diferenca, com a semente `1` e o endpoint externo que ja
eram conhecidos. Nenhum novo operador foi introduzido.

## Ledger angular--Green

Para os blocos angulares em `s` e `s#`, defina `K_ang` pelo mesmo kernel
escalado. O kernel prova

```text
M * ScalarAngularPairing + K_ang
  = M^2 * AngularDiagonal

  = M^2 * (GreenPairing + LocalTrioCorrection).
```

Como

```text
ScalarAngularPairing = GreenPairing + GreenCorrection,
```

a correcao total satisfaz a identidade exata

```text
M * GreenCorrection + K_ang
  = (M^2-M) * GreenPairing
    + M^2 * LocalTrioCorrection.
```

Essa e a nova forma tipada do gate escalar--diagonal. A interferencia entre
blocos foi substituida por um campo fechado com primitiva e endpoints
literais; a correcao local do trio permanece separada.

## Genuine-first

Num unico zero de `genuineContinuation` no strip, o observavel escalar ja
convergia a zero. O 0.42 registra tambem, para qualquer camera prima `p`,

```text
cpRadialDifference(p,delta) * ScalarAngularPairing(M,s) -> 0,
```

equivalentemente,

```text
cpRadialDifference(p,delta)
  * (GreenPairing + GreenCorrection) -> 0.
```

Essa afirmacao nao transforma soma zero em vetor zero. Quando duas sinteses
finitas zeram, o kernel prova que o pareamento diagonal inteiro migra para o
setor fechado:

```text
KernelPairing = M^2 * DiagonalPairing.
```

Isso e exatamente a conservacao de proveniencia exigida desde o 0.27.

## Fronteira rigorosa

O checkpoint nao prova que `K_ang`, a diagonal ou a correcao local zeram. Ele
tambem nao declara uma instancia de `GenuineOneSidedAngularGreenBridge`.

O proximo gate ficou mais estruturado: aplicar somacao por partes a primitiva
fechada `P_M` e verificar se o termo de bulk assim produzido se combina com
`LocalTrioCorrection` e com os bordos Genuine ja certificados. Esse passo
deve controlar o coeficiente radial da correcao, sem identificar por definicao
um zero escalar com anulacao coordenada.

## Teoremas principais

- `finitePortSynthesisKernelValue_sum_eq_zero`;
- `finitePortSynthesisKernelPrefix_succ`;
- `finitePortSynthesisKernelPrefix_cutoff`;
- `finitePortSynthesis_pairing_ledger`;
- `finiteScalarPortWronskian_synthesis_ledger`;
- `finiteOffDiagonalPortWronskian_synthesis_ledger`;
- `finitePortSynthesisKernelPairing_of_syntheses_eq_zero`;
- `finiteCanonicalAngularTrace_eq_secondDifferenceSynthesis_sub_outer`;
- `finiteCanonicalAngularScalarPairing_synthesis_green_ledger`;
- `finiteCanonicalAngularGreenCorrection_synthesis_ledger`;
- `finiteCanonicalAngularRadialGreenBudget_tendsto_zero_of_genuine_zero`.

## Arquivos

- `CPFormal/Analytic/CpFiniteScalarSynthesis.lean`;
- `CPFormal.lean`;
- `docs/SOURCE_MAP.md`.

## Validacao

O modulo nao contem lacunas de prova nem axiomas locais. A auditoria integral
e a evidencia remota serao registradas depois do build e do workflow final.
