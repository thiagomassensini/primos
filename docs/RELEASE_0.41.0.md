# Checkpoint 0.41 — identidade de segunda diferenca do Genuine continuado

## Correcao de identidade

Os brackets `C2`, `Cp`, o tilt transversal e a carta analitica ja eram
construidos com a mesma curvatura discreta, mas essa origem comum permanecia
distribuida entre modulos diferentes. Em particular, a definicao curta de
`genuineContinuation` escondia a serie concreta que ela normaliza.

O checkpoint 0.41 torna essa cadeia literal no kernel. Isso nao cria um novo
operador: identifica exatamente onde a mesma segunda diferenca e usada e onde
entram somas, carriers e normalizacoes adicionais.

## Primitiva comum

Para uma funcao `f : Z -> R`, a segunda diferenca centrada e

```text
centeredSecondDifference(f,c,r)
  = f(c-r) - 2*f(c) + f(c+r).
```

O bracket local `C2` e exatamente o raio `1`:

```text
C2.bracket(f,c) = centeredSecondDifference(f,c,1).
```

Para primo impar `p`, o bracket `Cp` soma todos os raios balanceados
`1,...,(p-1)/2`:

```text
Cp.bracket(p,f,c)
  = sum_{r=1}^{(p-1)/2} centeredSecondDifference(f,c,r)
  = saturatedBracket((p-1)/2,f,c).
```

Na menor camera prima impar, `p = 3`, existe somente o raio `1`. Portanto

```text
Cp.bracket(3,f,c)
  = centeredSecondDifference(f,c,1)
  = C2.bracket(f,c).
```

Essa ultima igualdade identifica o stencil local. Ela nao identifica as
genealogias globais `C2` e `Cp`, seus conjuntos de centros ou seus pesos de
carry.

## O tilt e o mesmo bracket sobre outro perfil

Defina o perfil transversal, com `delta = sigma - 1/2`, por

```text
transversePowerProfile(delta,c)(a) = (c+a)^(-delta).
```

O kernel prova

```text
cpPairTilt(delta,c,r)
  = centeredSecondDifference(
      transversePowerProfile(delta,c),0,r),

cpTilt(p,delta,c)
  = Cp.bracket(p,transversePowerProfile(delta,c),0).
```

Para primo impar, isso tambem e a soma saturada das segundas diferencas
transversais. O tilt e, assim, uma especializacao literal do bracket local.
Ele nao e o bracket do monomio complexo completo `n^(-s)` e nao e o operador
de ramo; esses objetos continuam ligados por teoremas proprios.

## Da carta ao quociente Genuine

Aplicando a mesma primitiva ao monomio

```text
dirichletTerm(s,n) = n^(-s),
```

a carta de uma camera prima impar fica

```text
bracketedDirichletChart(p,s)
  = seedSum(p,dirichletTerm(s))
    + sum_k sum_{r=1}^{(p-1)/2}
        centeredSecondDifference(
          dirichletTerm(s), alignedCenter(p,k), r).
```

Seu fator e

```text
cpChartFactor(p,s) = 1 - p^(1-s),
```

e o quociente da camera e

```text
cpGenuineQuotient(p,s)
  = bracketedDirichletChart(p,s) / cpChartFactor(p,s).
```

As identidades cruzadas entre cameras ja provadas permitem escolher `p = 3`
como representante canonico no strip. Como a semente dessa camera e `1` e ha
somente o raio `1`, a formula explicita do objeto e

```text
genuineContinuation(s)
  = (1 + sum_k centeredSecondDifference(
          dirichletTerm(s), alignedCenter(3,k), 1))
      / (1 - 3^(1-s)).
```

No Lean, `sum_k` acima e a soma infinita `tsum`. A leitura analitica da serie
usa a somabilidade ja provada para `re(s) > -1`; dentro do strip critico, o
fator da camera nao zera.

Portanto a cadeia formal agora e

```text
bracket C2
  -> segunda diferenca centrada de raio 1
  -> bracket Cp saturado em raios
  -> tilt sobre o perfil transversal
  -> carta bracketada sobre n^(-s)
  -> quociente da camera
  -> genuineContinuation.
```

## Cancelamento de um zero

Na faixa critica, o fator `1 - 3^(1-s)` e nao nulo. Assim o kernel tambem
reescreve um zero Genuine como o cancelamento literal da semente pela serie:

```text
genuineContinuation(s) = 0
  <-> sum_k centeredSecondDifference(
        dirichletTerm(s), alignedCenter(3,k), 1) = -1.
```

Para qualquer camera prima impar, os cortes finitos construidos pelos mesmos
brackets convergem a

```text
cpChartFactor(p,s) * genuineContinuation(s).
```

Isso registra a identidade da farinha discreta sem substituir a carta por um
alias ou esconder a semente no quociente.

## Fronteira rigorosa

Este checkpoint nao:

- identifica a segunda diferenca local com o operador Green inteiro;
- identifica o bracket com o Laplaciano Green, que possui carrier, pesos e
  convencao de sinal adicionais;
- transforma o setor grosso de primeira diferenca em curvatura de segunda
  ordem;
- especializa os teoremas `Cp` de primo impar em `p = 2`;
- identifica globalmente as genealogias `C2` e `Cp` a partir da igualdade do
  stencil local em `p = 3`;
- identifica `genuineContinuation` com `riemannZeta`;
- usa equacao funcional, simetria de zeros ou qualquer resultado sobre Zeta;
- prova a Hipotese de Riemann.

A camera `C2` continua especial: seus centros, sua profundidade inicial e
seus pesos de carry nao sao obtidos substituindo `p = 2` nas definicoes de
uma camera prima impar.

## Teoremas principais

- `C2.bracket_eq_centeredSecondDifference`;
- `C2.bracket_operator_eq_centeredSecondDifference`;
- `Cp.bracket_operator_eq_saturatedBracket`;
- `Cp.bracket_three_eq_centeredSecondDifference`;
- `Cp.bracket_three_eq_c2Bracket`;
- `cpPairTilt_eq_centeredSecondDifference`;
- `cpTilt_eq_genuineBracket`;
- `cpTilt_eq_saturatedBracket`;
- `bracketedDirichletChart_eq_centeredSecondDifferenceSeries`;
- `genuineContinuation_eq_centeredSecondDifferenceSeries`;
- `finiteChart_dirichlet_tendsto_factor_mul_genuineContinuation_on_strip`;
- `genuineContinuation_zero_iff_centeredSecondDifferenceSeries_eq_neg_one`.

## Arquivos

- `CPFormal/Analytic/CpGenuineSecondDifferenceIdentity.lean`;
- `CPFormal.lean`.

## Validacao local

```text
lake build --wfail
Build completed successfully (8711 jobs).
```

O modulo novo nao contem `sorry`, `admit` ou axiomas locais.

## Evidencia remota

- commit matematico: `bd46a2702efa96af60d2920e8679f6ba1fa39df6`;
- head SHA auditado: `83d1f1647e5cbe5f7a6c5e42d625df89b660acb5`;
- workflow run: `29740610203` (`Lean kernel audit`);
- job: `88346306316` (`Build CPFormal`);
- auditoria estatica: **success**;
- elaboracao pelo kernel: **success**.
