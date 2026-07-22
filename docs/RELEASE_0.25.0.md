# Checkpoint 0.25.0 — porta angular finita da camera canonica

Este checkpoint constroi o primeiro dos dois tracos exigidos pela lei de
porta Green. O novo alvo compilado e `CPFormal.Analytic.CpAngularPort`.

## Definicao independente de Phi

No bloco `m` da camera `p=3`, a corrente de gradientes recebe os pesos
residuais `1,2,0`:

```text
angularBlock_m
  = -sum_{r=0}^2 ((r+1) mod 3) * gradient(3m+r).
```

O traco finito `finiteCanonicalAngularTrace M s` e a soma dos primeiros `M`
blocos. Sua definicao nao menciona a carta bracketada, o Genuine ou zeros.
O kernel verificou tambem que o peso local coincide com o peso global
`n mod 3` usado na formula da porta angular.

## Telescopagem finita exata

Abrindo um bloco, o kernel obteve

```text
angularBlock_m
  = f(3m+1) + f(3m+2) - 2*f(3m+3),

bracket_m
  = f(3m+2) - 2*f(3m+3) + f(3m+4).
```

Somar os blocos faz os endpoints internos telescoparem. Para todo `M` e todo
`s : Complex`, sem hipotese analitica,

```text
finiteBracketedDirichletChart 3 M s
  = finiteCanonicalAngularTrace M s
      + positiveDirichletValue s (3*M).
```

O ultimo termo e literalmente `(3M+1)^(-s)`. Assim a diferenca entre porta e
carta nao foi definida como residual: ela foi calculada e e um unico bordo
externo explicito.

## Passagem ao limite Genuine-first

Para `Re(s)>0`, a norma do bordo e `(3M+1)^(-Re(s))`, logo ele converge a
zero. Com a convergencia bracketada ja formalizada em `Re(s)>-1`, o kernel
verificou

```text
finiteCanonicalAngularTrace M s
  -> bracketedDirichletChart 3 s.
```

Somente depois dessa identidade independente, a equivalencia de zeros da
carta fornece o corolario:

```text
genuineContinuation s = 0 e s na faixa critica
  -> finiteCanonicalAngularTrace M s -> 0.
```

## Fronteira honesta para Psi

Os documentos de retorno distinguem duas camadas:

- o TFVD fornece um retorno geometrico finito e um traco enriquecido;
- a descida aritmetica global continua bloqueada porque o quociente atual
  apaga proveniencia ainda vista pela perna `A`.

Por isso este checkpoint nao define `Psi` a partir de `Phi` nem escolhe um
residual para forcar o Wronskiano. O proximo nucleo minimo e construir um
`Psi_M` finito a partir do retorno/through-flow independente e provar a
identidade de fronteira antes de qualquer limite.

## Escopo rigoroso

Este checkpoint ainda nao:

- constroi o traco de fluxo `Psi`;
- prova uma identidade Wronskiana de porta;
- prova que o fluxo Green acoplado se anula nos zeros Genuine;
- constroi uma instancia concreta de `SignedGreenCertificate`;
- identifica o Genuine com `riemannZeta`;
- constroi operador Hilbert--Polya;
- prova a Hipotese de Riemann.

## Evidencia do kernel

- commit matematico: `995e0943697b74cc522d965231e90339f52b94fb`;
- workflow run: `29708436603` (`Lean kernel audit`);
- job: `88249048235` (`Build CPFormal`);
- resultado: `success` em auditoria estatica e `lake build --wfail`.

