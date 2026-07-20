# Checkpoint 0.31.0 — comutador log-jet Cp e cobordo finito

Este checkpoint formaliza o comutador anunciado no 0.30. O novo modulo
compilado e `CPFormal.Analytic.CpFiniteLogJetCommutator`.

## Dois transportes independentes

Para o campo natural log-pesado

```text
H_s(N) = log(N) * N^(-s),
```

o kernel constroi o bloco diretamente por uma soma de `p` diferencas:

```text
B_p(J_s)(n)
  = sum_{r<p} (H_s(p(n+1)+r+1) - H_s(p(n+1)+r)).
```

Separadamente, ja existiam o gradiente horizontal ordinario

```text
G_s(n) = (n+2)^(-s) - (n+1)^(-s)
```

e o gradiente log-jet `J_s`. Portanto o comutador nao e definido como um
residual escolhido para fazer a identidade fechar.

## Regra multiplicativa finita

A identidade

```text
log(ab) = log(a) + log(b)
```

junto da multiplicatividade dos monomios de Dirichlet produz a regra exata

```text
H_s(ab)
  = a^(-s) H_s(b)
      + log(a) a^(-s) b^(-s).
```

O teorema

```text
cpLogBlockGradient_eq_eigenvalue_mul_logJet_add_logScale
```

aplica essa regra aos dois endpoints do bloco e prova

```text
B_p(J_s)
  = p^(-s) J_s + log(p) p^(-s) G_s.
```

## Coracao do checkpoint

O objeto `cpLogJetCommutator` compara os dois transportes:

```text
[B_p, log](n,s)
  := B_p(J_s)(n) - p^(-s) J_s(n).
```

Para toda camera prima, o teorema

```text
cpPrimeLogJetCommutator_identity
```

verifica literalmente

```text
[B_p, log](n,s)
  = log(p) p^(-s) G_s(n).
```

Assim o canal adicional nao cria uma nova direcao horizontal: ele e
colinear com `G_s` em cada aresta. O unico dado novo e o coeficiente radial
primo-local `log(p) p^(-s)`.

## Normalizacao radial

Depois de aplicar o mesmo normalizador de fase usado no Green, o teorema

```text
phaseNormalizedCpLogJetCommutator_eq_radial_logScale
```

prova, com `delta = Re(s)-1/2`, que

```text
N_p(s) [B_p, log](n,s)
  = log(p) p^(-delta) G_s(n).
```

O fator que multiplica o gradiente e real. Isso separa formalmente o gerador
radial primo do fluxo horizontal antes de qualquer wedge refletido.

## Cobordo em cutoff finito

Somando as primeiras `M` arestas, o gradiente ordinario telescopa. O teorema

```text
finiteCpLogJetCommutator_eq_boundary
```

fecha a identidade

```text
sum_{n<M} [B_p, log](n,s)
  = log(p) p^(-s) * (V_s(M) - V_s(0)).
```

Esse e um bordo literal, construido pelos dois endpoints. Nao e uma
definicao residual.

## Relacao controlada com os documentos C2

O documento do canal Lambda foi usado somente como pista estrutural para o
coeficiente primo exato `log p`. Nenhuma identificacao com o canal global
`Lambda`, nenhuma inversao de Dirichlet, estimativa de Richardson ou
passagem ao limite foi importada para o kernel.

A teoria de defeitos motivou manter separado o cobordo que foi realmente
provado. O checkpoint nao identifica o defeito log-jet--Green do 0.30 com o
comutador atual. Essa comparacao continua sendo uma obrigacao tipada.

## Consequencia estrutural

```text
bloco Cp aplicado ao log-jet
        = transporte espectral do log-jet
          + canal radial primo sobre G_s

canal radial primo por aresta
        = log(p) p^(-s) G_s

soma em cutoff finito
        = log(p) p^(-s) * bordo de vertices
```

## Proximo nucleo minimo

Construir o wedge refletido induzido pelo comutador e compara-lo, mantendo
as tres proveniencias residuais, com `canonicalLogJetGreenDefectTriple` do
0.30. O objetivo e decidir por teorema se alguma parcela do defeito e esse
cobordo, sobra como termo de cutoff ou constitui um canal adicional.

## Escopo rigoroso

Este checkpoint ainda nao:

- identifica o defeito do 0.30 com o comutador;
- prova que o defeito log-jet--Green telescopa ou se anula;
- reagrupa todos os cutoffs por trios;
- prova cancelamento da interferencia escalar off-diagonal;
- prova que zeros Genuine anulam o fluxo Green;
- passa ao limite infinito;
- identifica o Genuine com `riemannZeta`;
- constroi operador Hilbert--Polya;
- prova a Hipotese de Riemann.

## Evidencia do kernel

- commit matematico: `ef4746908bcc584dab68b9a0bef80b79dbdc40c1`;
- workflow run: `29718608657` (`Lean kernel audit`);
- job: `88276624441` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`;
- nenhum `sorry`, `admit` ou axioma local.
