# Checkpoint 0.27.0 — ponte TFVD finita e obstrucao off-diagonal

Este checkpoint substitui a identificacao informal do log-jet escalar por
uma ponte finita tipada. Os alvos compilados sao
`CPFormal.Analytic.CpFiniteTfvdBridge` e
`CPFormal.Analytic.CpFinitePortWronskian`.

## Coordenada enriquecida da valvula

Cada bloco retém explicitamente

```text
(block, throughFlow, bracketFlow).
```

Para escala `kappa != 0`, peso `omega != 0` e arestas `(left,right)`, a
codificacao e

```text
throughFlow = -(left+right)/kappa
bracketFlow = omega*(right-left)/kappa.
```

O kernel provou que `tfvdDecode` recupera literalmente `(left,right)`. O
indice `block` tambem e preservado por reducao definicional. A normalizacao
dos documentos, `kappa=sqrt(2)`, foi definida e provada nao nula.

## Leitura angular e as duas portas

A leitura linear

```text
(3*kappa/2)*throughFlow - (kappa/(2*omega))*bracketFlow
```

foi definida sem referencia a `Phi`, `Psi` ou Green. O kernel verificou

```text
readout(encode(left,right)) = -(left+2*right).
```

Aplicando essa identidade aos dois primeiros gradientes de cada bloco
canonico, obtemos exatamente

```text
readout(TFVD_Dirichlet_port_M) = Phi_M,
readout(TFVD_logDirichlet_port_M) = Psi_M.
```

As igualdades valem para todo corte, todo parametro complexo e qualquer
familia de pesos `omega_m != 0`. Logo os pesos entram na coordenada de
curvatura e sao desfeitos pelo retorno; `Psi_M` nao e calibrado depois.

## O Wronskiano escalar nao e automaticamente Green

Foi formalizada a entrada de Wronski entre os blocos `m,n`. Ao formar o
Wronskiano depois da sintese escalar aparecem todos os pares:

```text
W_scalar = sum_m sum_n wedge(m,n)
         = W_diagonal + W_offDiagonal.
```

O termo off-diagonal foi definido como a soma explicita sobre entradas com
`m != n`, nao como um residual. Um witness de dois blocos foi kernel-checked
com

```text
W_offDiagonal = 1,
W_scalar != W_diagonal.
```

Portanto uma igualdade direta entre o Wronskiano das somas escalares
`Phi_M/Psi_M` e o fluxo Green diagonal e falsa sem estrutura adicional. A
projecao ortogonal/proveniencia nao e decoracao: ela determina que o
pareamento deve ocorrer coordenada por coordenada antes da sintese.

## Proximo nucleo minimo

Construir o pareamento refletido diretamente no portador TFVD enriquecido e
comparar sua diagonal, bloco a bloco, com o `finiteOrientedCpGreenFlux` ja
formalizado. Depois disso existem dois gates separados:

1. provar a identidade diagonal TFVD--Green;
2. provar uma hipotese aritmetica/ortogonal que elimine a interferencia se a
   formulacao final insistir na compressao escalar.

Nenhum dos dois gates foi postulado neste checkpoint.

## Escopo rigoroso

Este checkpoint ainda nao:

- prova a igualdade da diagonal TFVD com o fluxo Green Cp;
- prova que o off-diagonal se anula para as portas aritmeticas reais;
- prova a identidade Wronskiana global ou sua passagem ao limite;
- prova que zeros Genuine anulam o fluxo Green;
- identifica o Genuine com `riemannZeta`;
- constroi operador Hilbert--Polya;
- prova a Hipotese de Riemann.

## Evidencia do kernel

- commit matematico: `60d8885e8959066a1f035651e7a573cc2c80edb0`;
- workflow run: `29711460431` (`Lean kernel audit`);
- job: `88255906393` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`.
