# Checkpoint 0.40 — intertwiner CP–Genuine–Green

## Correcao de continuidade

O `cpBlockGradient` foi introduzido na construcao finita do Green por uma
telescopagem de `p` diferencas consecutivas. Embora essa definicao estivesse
correta, faltava no kernel a seta que a reconduzia explicitamente ao operador
Genuine ja construido. Isso deixava a aparencia enganosa de dois operadores:
um bracketado e outro de gradientes.

O checkpoint 0.40 fecha exatamente essa lacuna. Nao ha um segundo operador.

## Identidade universal

Para uma funcao arbitraria `f : ℤ → R`, com valores em qualquer anel
comutativo, definimos entre dois centros Cp consecutivos:

```text
resolvedGradient
  = (centerBlock_{n+1} - centerBlock_n)
    - (bracket_{n+1} - bracket_n).
```

A identidade Genuine finita ja certificada,

```text
bracket = centerBlock - p * center,
```

produz agora, por subtracao nos dois centros,

```text
resolvedGradient = p * (center_{n+1} - center_n).
```

Esse e o teorema
`cpGenuineResolvedGradient_eq_p_mul_alignedCenterGradient`. Ele antecede
Dirichlet, continuacao, zeros, limites, normalizacao radial e TFVD.

## Identificacao com o Green existente

Para o monomio de Dirichlet, a telescopagem do bloco prova

```text
cpBlockGradient = center_{n+1} - center_n.
```

Depois da normalizacao natural pelo tamanho do bloco,

```text
cpGenuineGreenGradient
  = p⁻¹ * resolvedGradient
  = cpBlockGradient.
```

A igualdade e coordenada a coordenada, nao apenas depois de somar. O fator
`p` e nao nulo porque `p` e primo.

O kernel transporta essa igualdade por toda a cadeia:

```text
bracket Genuine
  -> residual diferenciado
  -> gradiente Green normalizado
  -> Wronskiano finito
  -> normalizacao radial
  -> fluxo orientado
  -> diagonal TFVD.
```

Em particular, foram provados:

- `finiteGenuineCpGreenFlux_eq_finiteCpGreenFlux`;
- `finiteOrientedGenuineCpGreenFlux_eq_finiteOrientedCpGreenFlux`;
- `finiteOrientedGenuineCpGreenFlux_eq_tfvdDiagonal`;
- `finiteBracketCoupledCpGreenFlux_eq_genuineOriented_add_boundary`.

A ultima igualdade escreve o fluxo acoplado literalmente como a parte real
do Green Genuine orientado mais o bordo bracketado independente ja
certificado.

## O que fica corrigido

- `cpBlockGradient` nao e mais uma primitiva sem proveniencia;
- o Green finito nao usa um operador exterior ao Genuine;
- a normalizacao radial preserva a identificacao;
- a diagonal TFVD e exatamente o mesmo Green Genuine, bloco por bloco;
- nao e preciso provar o Genuine novamente;
- nenhuma zeta ou simetria de zeros entrou na prova.

## Fronteira rigorosa

Este checkpoint fecha a identidade dos operadores. Ele nao transforma, por
definicao, um zero de uma sintese escalar numa anulacao coordenada a
coordenada. Assim, nas interfaces dos checkpoints 0.38–0.39, o campo ainda
aberto deve ser lido somente como fechamento da correcao nao radial ao passar
da sintese escalar para o pareamento diagonal — nunca como uma hipotese de que
o Green seria outro operador ou de que o Genuine precisaria ser provado de
novo.

Essa separacao preserva o fio logico Genuine-first sem declarar uma conclusao
analitica que o kernel ainda nao recebeu.

## Arquivos

- `CPFormal/Analytic/CpGenuineGreenIntertwiner.lean`
- `CPFormal/Analytic/CpFiniteGreen.lean`
- `CPFormal.lean`

## Validacao

```text
lake build --wfail
Build completed successfully (8710 jobs).
```

O modulo novo nao contem `sorry`, `admit` ou axiomas locais.
