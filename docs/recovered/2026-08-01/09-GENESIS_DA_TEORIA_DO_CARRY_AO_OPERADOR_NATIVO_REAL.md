---
title: "Gênesis da teoria — do carry ao operador nativo real"
aliases:
  - "Mapa do gênesis da teoria"
  - "Carry, tilt, Genuine e operador real"
tags:
  - carry
  - C2
  - tilt
  - operador-nativo
  - Genuine-First
  - Lean4
status: "mapa de proveniência formal"
repositorios:
  - "thiagomassensini/formalizacao_C2"
  - "thiagomassensini/primos"
checkpoint_primos: "7d8d0b345b329935674edc24e5ac08ad9f7b5804"
data: 2026-07-31
---

# Gênesis da teoria — do carry ao operador nativo real

## Mapa formal da origem da linha crítica, da norma quadrática, do tilt, do Genuine e da invariância de câmeras

> [!IMPORTANT]
> Este documento reconstrói a genealogia da teoria usando apenas os repositórios
> `formalizacao_C2` e `primos`.
>
> O objetivo é localizar o nascimento de cada ideia e apontar o **nome exato da
> declaração Lean** e o **arquivo em que ela está provada**.
>
> A ordem adotada é **Genuine First**: primeiro vêm carry, endereços, pesos,
> cancelamento, bracket, norma, tilt e o representante comum das câmeras.
> A apresentação real do operador é então identificada como outra roupa fiel da
> mesma leitura.

---

# 1. A cadeia inteira em uma página

O encadeamento correto não começa em uma função externa nem em uma reta escolhida
por antecedência. Ele começa na aritmética posicional:

```text
representação posicional
        ↓
evento de carry
        ↓
profundidade k
        ↓
massa b⁻ᵏ
        ↓
amplitude deformada b⁻ᵏˢⁱᵍᵐᵃ
        ↓ energia quadrática
compatibilidade: b⁻²ᵏˢⁱᵍᵐᵃ = b⁻ᵏ
        ↓
sigma = 1/2
        ↓
estado real em R², com fase livre
        ↓
segunda diferença centrada
        ↓
câmera finita e resultante
        ↓
fechamento de bordo
        ↓
zero do operador nativo real
```

Em paralelo, a rota das cartas é:

```text
endereços de carry
        ↓
cancelamento lateral finito
        ↓
carta bracketada Genuine
        ↓
normalização de cada câmera
        ↓
representante Genuine comum
        ↓
escolha convencional da câmera 3 para nomeá-lo
        ↓
empacotamento fiel R² → C
        ↓
identidade entre fechamento primitivo real e zero Genuine
```

A síntese matemática é:

\[
\boxed{
\forall b,c>1,\qquad
\operatorname{CompatCarry}_b(\sigma)
\iff
\operatorname{CompatCarry}_c(\sigma)
\iff
\sigma=\frac12.
}
\]

Depois:

\[
\boxed{
\operatorname{CompatCarry}_b(\sigma)
\iff
\operatorname{CompatEnergiaReal}(\sigma,t).
}
\]

E, para uma largura de câmera natural arbitrária:

\[
\boxed{
\operatorname{ZeroNativo}_{c}(\sigma,t)
\iff
\left(\sigma=\frac12\right)
\land
\operatorname{Ressonância}_{c}(t).
}
\]

Portanto:

\[
\boxed{
\text{carry global}
\longrightarrow
\text{domínio quadrático comum}
\longrightarrow
\sigma=\frac12
\longrightarrow
\text{câmeras como leituras do mesmo fenômeno}.
}
\]

---

# 2. Os dois repositórios e seus papéis

## 2.1. `formalizacao_C2`: o laboratório do gênesis

O repositório [`thiagomassensini/formalizacao_C2`](https://github.com/thiagomassensini/formalizacao_C2)
contém a primeira forma explícita da geometria binária:

- profundidade efetiva determinada por \(n-1\) e \(n+1\);
- endereço único de uma perna;
- peso diádico \(2^{-k}\);
- cancelamento lateral por bracket;
- norma quadrática de ramo;
- barreira em \(\sigma=\frac12\);
- tilt como detector de sinal do deslocamento radial.

Os arquivos centrais são:

```text
LeanC2/Foundations/Dyadic.lean
LeanC2/Operators/FiniteCancellation.lean
LeanC2/Operators/BranchBarrier.lean
LeanC2/Operators/Tilt.lean
LeanC2/Operators/CenterGaussianTilt.lean
```

## 2.2. `primos`: a generalização e a costura operatorial

O repositório [`thiagomassensini/primos`](https://github.com/thiagomassensini/primos)
generaliza a origem C2 para:

- qualquer base posicional \(b>1\);
- pesos e amplitudes sem hipótese de primalidade;
- estado rotacional inteiramente real em \(\mathbb R^2\);
- câmera aditiva definida para qualquer largura natural;
- fatoração universal do conjunto de zeros;
- independência das câmeras normalizadas;
- crosswalk bidirecional entre o Primitivo real e o Genuine.

O checkpoint principal deste mapa é:

```text
thiagomassensini/primos
commit 7d8d0b345b329935674edc24e5ac08ad9f7b5804
```

Algumas extensões posteriores de `primos/main` são registradas separadamente,
especialmente a continuação para câmeras naturais pares, ímpares, primas e
compostas.

---

# 3. Gênesis C2: profundidade, endereço e peso

## 3.1. A profundidade efetiva nasce dos dois vizinhos

Arquivo:

[`LeanC2/Foundations/Dyadic.lean`](https://github.com/thiagomassensini/formalizacao_C2/blob/main/LeanC2/Foundations/Dyadic.lean)

Definições:

```lean
def v2 (n : Nat) : Nat :=
  padicValNat 2 n

def keff (n : Nat) : Nat :=
  max (v2 (n - 1)) (v2 (n + 1))
```

Para uma perna ímpar \(n\), a câmera C2 observa os dois possíveis centros:

\[
n-1
\qquad\text{e}\qquad
n+1.
\]

A profundidade efetiva é o maior número de fatores \(2\) presente nesses dois
vizinhos:

\[
\boxed{
k_{\mathrm{eff}}(n)
=
\max\bigl(v_2(n-1),v_2(n+1)\bigr).
}
\]

Isso é o primeiro aparecimento da geometria vertical: o inteiro ímpar é uma
perna; um de seus vizinhos é o centro carregado; a valuation desse centro
determina a profundidade.

## 3.2. Endereços canônicos

Ainda em `Dyadic.lean`:

```lean
inductive BranchSign
  | minus
  | plus

def descendant (k : Nat) (epsilon : BranchSign) (m : Int) : Int :=
  (2 : Int) ^ k * m + epsilon.toInt
```

O endereço C2 tem a forma:

\[
n=2^k m+\varepsilon,
\qquad
\varepsilon\in\{-1,+1\},
\qquad
m\ \text{ímpar}.
\]

Teoremas centrais:

```lean
keff_left_leg_shift
keff_right_leg_shift
keff_left_leg
keff_right_leg
bracket_bijection_odd_ge_three_exists
```

Os teoremas `keff_left_leg` e `keff_right_leg` provam que, em um endereço
válido,

\[
k_{\mathrm{eff}}(2^k m-1)=k,
\qquad
k_{\mathrm{eff}}(2^k m+1)=k.
\]

A existência do endereço de toda perna ímpar \(n\ge3\) aparece em:

```lean
theorem bracket_bijection_odd_ge_three_exists
```

## 3.3. Peso diádico e lei local de halving

Definições:

```lean
def dyadicWeight (k : Nat) : ℚ :=
  ((2 : ℚ) ^ k)⁻¹

def directLegWeight (n : Nat) : ℚ :=
  dyadicWeight (keff n)
```

Logo:

\[
w_k=2^{-k}.
\]

Teoremas:

```lean
halving_law_of_address
halving_law_odd_ge_three
```

O primeiro prova:

```lean
theorem halving_law_of_address
    (h : IsC2LegAddress n k epsilon m) :
    directLegWeight n = dyadicWeight k
```

Em linguagem matemática:

\[
\boxed{
n=2^k m+\varepsilon
\quad\Longrightarrow\quad
w(n)=2^{-k}.
}
\]

O segundo agrega existência, unicidade do endereço e igualdade do peso para
toda perna ímpar admissível.

### Significado

A massa não é colocada depois no operador. Ela já acompanha a perna porque a
perna possui um endereço de carry e esse endereço possui profundidade \(k\).

---

# 4. Gênesis C2: cancelamento lateral e nascimento do Genuine bracketado

Arquivo:

[`LeanC2/Operators/FiniteCancellation.lean`](https://github.com/thiagomassensini/formalizacao_C2/blob/main/LeanC2/Operators/FiniteCancellation.lean)

## 4.1. Centro, pernas e bracket

```lean
def c2Center (k m : Nat) : Nat :=
  2 ^ k * m
```

O par de pernas é:

\[
2^k m-1,
\qquad
2^k m+1.
\]

O bracket local é:

\[
\mathcal B_{k,m}(f)
=
2^{-k}
\left[
f(2^k m-1)+f(2^k m+1)-2f(2^k m)
\right].
\]

Objetos Lean:

```lean
directLegTerm
directPairTerm
bracketTerm
centerRemainderTerm
```

## 4.2. Cancelamento lateral local

Teorema:

```lean
theorem local_lateral_cancellation
    (f : Nat → R) {k m : Nat}
    (hk : 2 ≤ k) (hm : Odd m) :
    directPairTerm f k m - bracketTerm f k m =
      centerRemainderTerm f k m
```

Essa é a primeira identidade local central da rota:

\[
\boxed{
\text{duas pernas diretas}
-
\text{bracket}
=
\text{resto central}.
}
\]

O bracket não inventa informação. Ele reorganiza exatamente as duas pernas e
deixa explícita a contribuição do centro.

## 4.3. Cancelamento em famílias finitas

Teoremas:

```lean
finite_lateral_cancellation
rectangular_lateral_cancellation
rectangular_lateral_cancellation_double
rectangular_lateral_cancellation_geometric
```

A versão retangular organiza endereços:

\[
2\le k\le K,
\qquad
m\le M,
\qquad
m\ \text{ímpar}.
\]

Assim, o cancelamento local é somado sem perda sobre um corte finito inteiro.

## 4.4. Forma geométrica do resto central

Teorema:

```lean
centerRemainderTerm_eq_geometric
```

A contribuição restante é escrita como:

\[
2\cdot 2^{-k}\,f(2^k m).
\]

Depois aparecem as fatorações:

```lean
centerGeometricDoubleSum_factorized
centerGeometricDoubleSum_factorized_multiplicative
rectangular_lateral_cancellation_factorized_multiplicative
```

### Papel no gênesis

Aqui nasce a estrutura Genuine First:

```text
pernas com peso de carry
        ↓
bracket centrado
        ↓
cancelamento lateral exato
        ↓
canal central explícito
```

A carta Genuine não aparece como um objeto arbitrário acrescentado de fora.
Ela emerge da reorganização exata das incidências de carry.

---

# 5. Gênesis C2: norma quadrática e barreira em 1/2

Arquivo:

[`LeanC2/Operators/BranchBarrier.lean`](https://github.com/thiagomassensini/formalizacao_C2/blob/main/LeanC2/Operators/BranchBarrier.lean)

## 5.1. Peso quadrático deformado

```lean
def branchWeightSigma (σ : ℝ) : ℝ :=
  (2 : ℝ) ^ (-2 * σ)
```

Defina:

\[
q(\sigma)=2^{-2\sigma}.
\]

A norma quadrática C2 é:

```lean
def branchNormSqSigma (σ : ℝ) : ℝ :=
  2 * ∑' j : ℕ, branchWeightSigma σ ^ (j + 2)
```

Portanto:

\[
\boxed{
\mathcal N_{C2}(\sigma)
=
2\sum_{j\ge0}q(\sigma)^{j+2}.
}
\]

O fator \(2\) corresponde às duas pernas. O início em profundidade \(2\)
corresponde à convenção original da geometria C2 dessa formalização.

## 5.2. Forma fechada

Teorema:

```lean
branchNormSq_closed_form
```

Para \(\sigma>0\):

\[
\boxed{
\mathcal N_{C2}(\sigma)
=
\frac{2q(\sigma)^2}{1-q(\sigma)}.
}
\]

## 5.3. Saturação na meia abscissa

Teoremas:

```lean
branchWeightSigma_half
branchNormSq_half
```

Em \(\sigma=\frac12\):

\[
q\left(\frac12\right)=2^{-1}=\frac12,
\]

e:

\[
\mathcal N_{C2}\left(\frac12\right)
=
\frac{2(1/2)^2}{1-1/2}
=
1.
\]

## 5.4. A barreira completa

Teoremas:

```lean
branchNormSq_lt_one_of_half_lt
branchNormSq_gt_one_of_pos_of_lt_half
branchNormSq_barrier_lt_one
branchNormSq_barrier_eq_one
branchNormSq_barrier_gt_one
branchNormSq_barrier
```

O teorema central é:

```lean
theorem branchNormSq_barrier_eq_one
    {σ : ℝ} (hσ : 0 < σ) :
    branchNormSqSigma σ = 1 ↔
      σ = (1 : ℝ) / 2
```

A tricotomia completa é:

\[
\boxed{
\begin{aligned}
\mathcal N_{C2}(\sigma)<1
&\iff
\sigma>\frac12,\\[2mm]
\mathcal N_{C2}(\sigma)=1
&\iff
\sigma=\frac12,\\[2mm]
\mathcal N_{C2}(\sigma)>1
&\iff
0<\sigma<\frac12.
\end{aligned}
}
\]

### O que isso prova conceitualmente

A linha crítica já surge no laboratório C2 como **barreira de saturação
quadrática**:

- à direita, a compressão é excessiva e a norma fica abaixo de \(1\);
- no centro, a energia fecha exatamente;
- à esquerda, a massa quadrática excede \(1\).

Não é o zero de uma função que escolhe \(1/2\). A norma do carry já separa os
três regimes antes da passagem ao operador.

## 5.5. Independência da fase

O mesmo arquivo define wrappers em \(s=\sigma+it\):

```lean
branchWeightSigmaT
branchNormSqSigmaT
branchWeightSigmaT_indep_t
branchNormSqSigmaT_indep_t
```

O Lean registra literalmente que a norma depende apenas de \(\sigma\), não de
\(t\).

---

# 6. Gênesis C2: o tilt como detector de deslocamento radial

Arquivo:

[`LeanC2/Operators/Tilt.lean`](https://github.com/thiagomassensini/formalizacao_C2/blob/main/LeanC2/Operators/Tilt.lean)

## 6.1. Segunda diferença de raio 1

```lean
def bracket2 (f : ℝ → ℝ) (c : ℝ) : ℝ :=
  f (c - 1) + f (c + 1) - 2 * f c
```

Isto é:

\[
\Delta^2 f(c)
=
f(c-1)+f(c+1)-2f(c).
\]

## 6.2. Tilt radial

```lean
def tilt (δ x : ℝ) : ℝ :=
  Real.rpow x (-δ)

def tiltBracket (δ c : ℝ) : ℝ :=
  bracket2 (tilt δ) c
```

O deslocamento relevante é:

\[
\delta=\sigma-\frac12.
\]

Logo, o campo de tilt é:

\[
x\longmapsto x^{-\delta}.
\]

## 6.3. Sinais dos dois lados

Teoremas:

```lean
tiltBracket_zero
tiltBracket_neg_of_neg_one_lt
tiltBracket_pos_of_pos
bracket_tilt_zero
bracket_tilt_pos
bracket_tilt_neg
```

Para centro \(c>1\):

\[
\delta>0
\Longrightarrow
\operatorname{TiltBracket}(\delta,c)>0,
\]

enquanto:

\[
-1<\delta<0
\Longrightarrow
\operatorname{TiltBracket}(\delta,c)<0.
\]

A prova usa:

- convexidade estrita de \(x^{-\delta}\) quando \(\delta>0\);
- concavidade estrita quando \(-1<\delta<0\).

## 6.4. Zero exato do tilt

Teorema:

```lean
theorem bracket_tilt_zero_iff_delta_zero
    {δ c : ℝ}
    (hδlow : -1 < δ) (hc : 1 < c) :
    bracket2 (tilt δ) c = 0 ↔ δ = 0
```

Portanto:

\[
\boxed{
\operatorname{TiltBracket}
\left(\sigma-\frac12,c\right)=0
\iff
\sigma=\frac12.
}
\]

A versão normalizada é:

```lean
normalizedTiltCurvature
normalizedTiltCurvature_zero_iff_delta_zero
```

A normalização remove o decaimento principal em \(c\), mas preserva sinais e
zeros.

## 6.5. Papel lógico do tilt

O tilt é um detector local e independente da mesma coordenada radial já
selecionada pela norma:

```text
norma quadrática:
    saturação = 1  ↔  sigma = 1/2

tilt:
    curvatura = 0  ↔  sigma = 1/2
```

Esses dois mecanismos se encontram no mesmo locus porque ambos medem o
deslocamento transversal da compressão do carry. O tilt confirma e torna
visível a rigidez por convexidade; ele não é uma hipótese necessária no corpo
curto do teorema terminal do operador.

## 6.6. Empacotamento center-Gaussian posterior

Arquivo:

[`LeanC2/Operators/CenterGaussianTilt.lean`](https://github.com/thiagomassensini/formalizacao_C2/blob/main/LeanC2/Operators/CenterGaussianTilt.lean)

Teorema principal de rigidez do fator:

```lean
centerGaussianTiltFactor_eq_one_iff_delta_zero
```

Ele preserva a mesma informação:

\[
\operatorname{fator}=1
\iff
\delta=0.
\]

É uma continuação do detector de tilt, não a origem da linha crítica.

---

# 7. Da geometria C2 à lei posicional para qualquer base

A generalização decisiva está em:

[`CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean)

O próprio módulo isola a rigidez:

- antes de qualquer hipótese de primalidade;
- antes de qualquer empacotamento em coordenadas não reais;
- usando somente massa de carry, amplitude e energia quadrática.

## 7.1. Massa e amplitude gerais

As definições de origem ficam em:

[`CPFormal/Carry/CpBranchWeight.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Carry/CpBranchWeight.lean)

Objetos:

```lean
criticalMass
criticalAmplitude
branchAmplitude
branchMassWeight
```

Para base \(b>1\) e profundidade \(k>0\):

\[
\mu_{b,k}=b^{-k},
\]

\[
\alpha_{b,k}=b^{-k/2},
\]

\[
\alpha_{b,k}(\sigma)=b^{-k\sigma}.
\]

Teoremas básicos:

```lean
criticalAmplitude_sq_eq_mass
branchAmplitude_sq_eq_massWeight
branchAmplitude_half
branchMassWeight_half
```

Em particular:

\[
\boxed{
\alpha_{b,k}^{\,2}=\mu_{b,k}.
}
\]

## 7.2. Rigidez local sem primalidade

Teorema:

```lean
theorem branchAmplitude_sq_eq_criticalMass_iff_of_one_lt
    (b k : ℕ) (hb : 1 < b) (hk : 0 < k) (sigma : ℝ) :
    (branchAmplitude b sigma k) ^ 2 = criticalMass b k ↔
      sigma = (1 : ℝ) / 2
```

A conta formalizada é:

\[
\left(b^{-k\sigma}\right)^2=b^{-k}
\]

\[
b^{-2k\sigma}=b^{-k}
\]

e, como \(b>1\) e \(k>0\):

\[
-2k\sigma=-k
\iff
\boxed{\sigma=\frac12}.
\]

Isso vale para:

- base par;
- base ímpar;
- base prima;
- base composta.

## 7.3. Compatibilidade em todas as profundidades

Definição:

```lean
def PositionalCarryMassCompatible (b : ℕ) (sigma : ℝ) : Prop :=
  ∀ k : ℕ, 0 < k →
    (branchAmplitude b sigma k) ^ 2 = criticalMass b k
```

Teorema:

```lean
theorem positionalCarryMassCompatible_iff
    (b : ℕ) (hb : 1 < b) (sigma : ℝ) :
    PositionalCarryMassCompatible b sigma ↔
      sigma = (1 : ℝ) / 2
```

Assim:

\[
\boxed{
\operatorname{CompatCarry}_b(\sigma)
\iff
\sigma=\frac12.
}
\]

Uma única profundidade positiva já força a recíproca; a condição global
confirma a compatibilidade em toda a torre.

---

# 8. Norma quadrática geral dos pesos do carry

Ainda em:

[`CpPositionalCarryQuadraticRigidity.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean)

## 8.1. Razão de ramo

Defina:

\[
q_b(\sigma)=b^{-2\sigma}.
\]

Com \(b-1\) pernas e profundidades positivas, a norma de ramo é:

\[
\mathcal N_b(\sigma)
=
(b-1)\sum_{k\ge1}b^{-2k\sigma}.
\]

Teorema da forma fechada:

```lean
branchNormSq_eq_closed_of_one_lt
```

\[
\boxed{
\mathcal N_b(\sigma)
=
(b-1)\frac{q_b(\sigma)}{1-q_b(\sigma)}.
}
\]

## 8.2. Saturação

Teoremas:

```lean
normalizedGeometricMass_eq_one_iff_of_one_lt
branchRatio_eq_inv_iff_of_one_lt
branchNormSq_eq_one_iff_of_one_lt
```

A sequência é:

\[
(b-1)\frac{q}{1-q}=1
\iff
q=\frac1b,
\]

e:

\[
b^{-2\sigma}=\frac1b=b^{-1}
\iff
\sigma=\frac12.
\]

Logo:

```lean
theorem branchNormSq_eq_one_iff_of_one_lt
    (b : ℕ) (hb : 1 < b)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    branchNormSq b sigma = 1 ↔
      sigma = (1 : ℝ) / 2
```

Em notação:

\[
\boxed{
\mathcal N_b(\sigma)=1
\iff
\sigma=\frac12.
}
\]

## 8.3. Independência de base

Teorema exato:

```lean
theorem branchNormSq_eq_one_base_independent
    (b c : ℕ) (hb : 1 < b) (hc : 1 < c)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    branchNormSq b sigma = 1 ↔
      branchNormSq c sigma = 1
```

Localização direta:

[`branchNormSq_eq_one_base_independent`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean#L286-L295)

Portanto:

\[
\boxed{
\forall b,c>1,\qquad
\mathcal N_b(\sigma)=1
\iff
\mathcal N_c(\sigma)=1
\iff
\sigma=\frac12.
}
\]

### O que permanece quando a base muda

Os valores individuais dos pesos mudam:

\[
2^{-k},\ 3^{-k},\ 4^{-k},\ 10^{-k},\ldots
\]

mas o equilíbrio entre massa e energia não muda. A invariante é o expoente
admissível:

\[
\boxed{\sigma=\frac12}.
\]

Primos podem ser usados como câmeras mínimas não redundantes. Eles não causam
a rigidez.

---

# 9. Fatoração multibase do tilt

Arquivos:

```text
CPFormal/Analytic/CpTilt.lean
CPFormal/Analytic/CpTiltRigidity.lean
```

Links:

- [`CpTilt.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpTilt.lean)
- [`CpTiltRigidity.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpTiltRigidity.lean)

## 9.1. Definição

Para offsets balanceados \(A_p\):

\[
\Theta_{p,\delta}(c)
=
\sum_{a\in A_p}(c+a)^{-\delta}
-
(p-1)c^{-\delta}.
\]

No Lean:

```lean
cpTilt
cpTiltAtSigma
```

com:

\[
\delta=\sigma-\frac12.
\]

## 9.2. Contribuição por perna e por par

Definições:

```lean
cpLegTilt
cpPairTilt
```

O bracket simétrico de um par é:

\[
P_{\delta,c}(a)
=
(c-a)^{-\delta}
+
(c+a)^{-\delta}
-
2c^{-\delta}.
\]

Teoremas de reindexação:

```lean
neg_mem_balancedOffsets_iff
sum_balancedOffsets_neg
cpTilt_eq_sum_leg
cpLegTilt_add_neg
```

## 9.3. Fatoração exata do tilt

Teorema:

```lean
theorem cpTilt_eq_half_sum_pair
    (p : ℕ) (hpodd : Odd p) (delta center : ℝ) :
    cpTilt p delta center =
      ((1 : ℝ) / 2) *
        ∑ a ∈ balancedOffsets p,
          cpPairTilt delta center a
```

Portanto:

\[
\boxed{
\Theta_{p,\delta}(c)
=
\frac12
\sum_{a\in A_p}
\left[
(c-a)^{-\delta}
+
(c+a)^{-\delta}
-
2c^{-\delta}
\right].
}
\]

O fator \(\frac12\) surge porque a soma balanceada contém \(a\) e \(-a\);
cada par é contado duas vezes.

## 9.4. Sinais e aniquilação

Teoremas:

```lean
cpPairTilt_pos_of_delta_pos
cpPairTilt_neg_of_neg_one_lt_delta
cpTilt_pos_of_delta_pos
cpTilt_neg_of_neg_one_lt_delta
tiltRigidityAt_of_halfRange_lt_center
cpTiltAtSigma_eq_zero_iff_half
```

O último prova, para uma câmera balanceada prima ímpar e um centro admissível:

```lean
theorem cpTiltAtSigma_eq_zero_iff_half
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {sigma center : ℝ} (hsigma : 0 < sigma)
    (hcenter : (halfRange p : ℝ) < center) :
    cpTiltAtSigma p sigma center = 0 ↔
      sigma = (1 : ℝ) / 2
```

Localização:

[`cpTiltAtSigma_eq_zero_iff_half`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpTiltRigidity.lean#L336-L350)

## 9.5. Ponte norma–tilt

Teorema:

```lean
branchDefect_eq_zero_iff_cpTiltAtSigma_eq_zero_of_admissible_center
```

Ele prova:

\[
\boxed{
\operatorname{DefeitoNorma}_p(\sigma)=0
\iff
\operatorname{Tilt}_p(\sigma,c)=0.
}
\]

Como ambos equivalem a \(\sigma=\frac12\):

\[
\boxed{
\mathcal N_p(\sigma)=1
\iff
\Theta_{p,\sigma-1/2}(c)=0
\iff
\sigma=\frac12.
}
\]

### Escopo exato

A prova local do **sinal do tilt balanceado** usa a geometria de pares de uma
câmera prima ímpar.

A prova da **rigidez quadrática global** não usa primalidade.

Isso não é contradição:

- a lei radial é universal em \(b>1\);
- o tilt balanceado é uma realização local específica dessa lei;
- outras larguras podem possuir outra forma local de carta sem alterar o
  domínio quadrático comum.

---

# 10. A linha crítica explicada pela teoria

A linha \(\sigma=\frac12\) aparece em quatro níveis compatíveis.

## 10.1. Nível local de massa

Uma profundidade \(k\) tem massa:

\[
\mu_{b,k}=b^{-k}.
\]

## 10.2. Nível de amplitude

A amplitude deformada é:

\[
\alpha_{b,k}(\sigma)=b^{-k\sigma}.
\]

## 10.3. Nível de energia quadrática

A energia é o quadrado da amplitude:

\[
\alpha_{b,k}(\sigma)^2=b^{-2k\sigma}.
\]

Compatibilidade com a massa exige:

\[
b^{-2k\sigma}=b^{-k}.
\]

Então:

\[
\boxed{\sigma=\frac12}.
\]

## 10.4. Nível da norma global

Somando todas as profundidades e todas as pernas:

\[
\mathcal N_b(\sigma)=1
\iff
\sigma=\frac12.
\]

## 10.5. Nível do detector de curvatura

Escrevendo:

\[
\delta=\sigma-\frac12,
\]

o tilt satisfaz:

\[
\delta<0
\Rightarrow
\Theta<0,
\qquad
\delta=0
\Rightarrow
\Theta=0,
\qquad
\delta>0
\Rightarrow
\Theta>0.
\]

### Conclusão

\[
\boxed{
\frac12
\text{ não é um parâmetro inserido para confinar zeros.}
}
\]

Ele é a única solução da conservação quadrática entre:

- massa posicional do carry;
- amplitude do ramo;
- energia do estado;
- saturação global da norma.

O operador recebe essa casca já fixada e conserva sua origem.

---

# 11. Crosswalk: da massa posicional ao estado real

Arquivo:

[`CPFormal/Analytic/CpQuadraticDomainCrosswalk.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpQuadraticDomainCrosswalk.lean)

Teorema:

```lean
theorem positionalCarryMassCompatible_iff_realEnergyCompatible
    (b : ℕ) (hb : 1 < b) (sigma time : ℝ) :
    PositionalCarryMassCompatible b sigma ↔
      NativeCarryRealPlaneMassCompatible sigma time
```

A costura correta é uma equivalência de **domínios admissíveis**.

Ela não afirma a igualdade ponto a ponto:

\[
b^{-k}=n^{-1}.
\]

Essas são quantidades indexadas por variáveis diferentes.

O que o Lean prova é:

\[
\boxed{
\operatorname{CompatCarry}_b(\sigma)
\iff
\operatorname{CompatEnergiaReal}(\sigma,t).
}
\]

Como ambos os lados equivalem a \(\sigma=\frac12\):

\[
\boxed{
\forall b>1,\qquad
\operatorname{CompatCarry}_b(\sigma)
\iff
\operatorname{CompatEnergiaReal}(\sigma,t)
\iff
\sigma=\frac12.
}
\]

O tempo permanece completamente livre nessa equivalência.

---

# 12. O operador nativo/primitivo não precisa de plano complexo

Arquivo:

[`CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean)

O cabeçalho do próprio módulo registra que o scanner primitivo é formalizado
sem introduzir um campo escalar complexo.

## 12.1. Espaço real

```lean
abbrev NativeCarryRealPlane := ℝ × ℝ
```

Cada estado é um par real:

\[
u=(x,y).
\]

## 12.2. Energia quadrática

```lean
def nativeCarryRealPlaneEnergy
    (u : NativeCarryRealPlane) : ℝ :=
  u.1 ^ 2 + u.2 ^ 2
```

Logo:

\[
E(x,y)=x^2+y^2.
\]

## 12.3. Direção de rotação

```lean
def nativeCarryRealDirection (theta : ℝ) :
    NativeCarryRealPlane :=
  (Real.cos theta, Real.sin theta)
```

Teorema:

```lean
nativeCarryRealPlaneEnergy_direction
```

\[
\cos^2\theta+\sin^2\theta=1.
\]

## 12.4. Estado real deformado

```lean
def nativeCarryRealPlaneSampleAt
    (sigma t : ℝ) (n : ℤ) :
    NativeCarryRealPlane
```

Para \(n>0\):

\[
\boxed{
u_{\sigma,t}(n)
=
n^{-\sigma}
\bigl(
\cos(-t\log n),
\sin(-t\log n)
\bigr).
}
\]

Equivalentemente:

\[
u_{\sigma,t}(n)
=
n^{-\sigma}R(-t\log n)e_1.
\]

## 12.5. Energia independente da fase

Teorema:

```lean
theorem nativeCarryRealPlaneEnergy_sampleAt
    (sigma t : ℝ) {n : ℤ} (hn : 0 < n) :
    nativeCarryRealPlaneEnergy
        (nativeCarryRealPlaneSampleAt sigma t n) =
      (n : ℝ) ^ (-2 * sigma)
```

Portanto:

\[
\boxed{
\|u_{\sigma,t}(n)\|^2=n^{-2\sigma}.
}
\]

O parâmetro \(t\) gira o vetor, mas desaparece da energia.

Na casca crítica:

```lean
nativeCarryRealPlaneEnergy_sample
```

\[
\boxed{
\left\|u_{\frac12,t}(n)\right\|^2=n^{-1}.
}
\]

## 12.6. Domínio de energia real

Definição:

```lean
def NativeCarryRealPlaneMassCompatible
    (sigma t : ℝ) : Prop :=
  ∀ n : ℤ, 1 < n →
    nativeCarryRealPlaneEnergy
        (nativeCarryRealPlaneSampleAt sigma t n) =
      ((n : ℝ))⁻¹
```

Teorema:

```lean
theorem nativeCarryRealPlaneMassCompatible_iff
    (sigma t : ℝ) :
    NativeCarryRealPlaneMassCompatible sigma t ↔
      sigma = (1 : ℝ) / 2
```

A prova já pode usar \(n=2\):

\[
2^{-2\sigma}=2^{-1}
\iff
\sigma=\frac12.
\]

### Resultado conceitual

```text
sigma = coordenada radial
t     = coordenada angular
```

O carry fixa a primeira. A ressonância investiga a segunda.

---

# 13. A câmera finita é apenas aditiva

Ainda em `CpNativeCarryRealPlaneBracket.lean`.

## 13.1. Definição genérica

```lean
def nativeCarryFiniteSaturatedChart
    {A : Type*} [AddCommGroup A]
    (p M : ℕ) (f : ℤ → A) : A :=
  seed + soma dos brackets centrados
```

A exigência algébrica é somente:

```lean
[AddCommGroup A]
```

Portanto, a câmera:

- não precisa de multiplicação entre estados;
- não precisa de divisão;
- não precisa de um plano não real;
- não precisa de primalidade para ser definida.

## 13.2. Fórmula

Se:

\[
h_c=\left\lfloor\frac{c-1}{2}\right\rfloor,
\qquad
q_{c,k}=c(k+1),
\]

então:

\[
\boxed{
\begin{aligned}
R_{c,M}(\sigma,t)
&=
\sum_{n=1}^{h_c}u_{\sigma,t}(n)\\
&\quad+
\sum_{k=0}^{M-1}
\sum_{r=1}^{h_c}
\left[
u_{\sigma,t}(q_{c,k}-r)
-2u_{\sigma,t}(q_{c,k})
+u_{\sigma,t}(q_{c,k}+r)
\right].
\end{aligned}
}
\]

Definição Lean:

```lean
nativeCarryRealPlaneFiniteChartAt
```

A versão já crítica é:

```lean
nativeCarryRealPlaneFiniteChart
```

## 13.3. Zero vetorial detectado pela energia

Teoremas:

```lean
nativeCarryRealPlaneEnergy_eq_zero_iff
nativeCarryRealPlaneFiniteChart_energy_eq_zero_iff
```

Eles provam:

\[
\boxed{
E(R_{c,M})=0
\iff
R_{c,M}=(0,0).
}
\]

Não existe uma segunda espécie de zero escondida fora do plano real.

## 13.4. Zero finito admissível

Definição:

```lean
NativeCarryRealPlaneAdmissibleFiniteZero
```

Teorema:

```lean
nativeCarryRealPlaneAdmissibleFiniteZero_iff
```

\[
\boxed{
\operatorname{ZeroFinito}(c,M,\sigma,t)
\iff
\sigma=\frac12
\land
E\left(R_{c,M}\left(\frac12,t\right)\right)=0.
}
\]

Mais uma vez, o bracket não escolhe \(\sigma\) depois do cancelamento. O domínio
do carry chega antes.

---

# 14. O operador nativo real no limite

Arquivo:

[`CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean)

## 14.1. Fechamento de bordo

```lean
def NativeCarryRealOperatorBoundaryClosesAt
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  Tendsto
    (fun cutoff : ℕ =>
      nativeCarryRealPlaneFiniteChartAt
        camera cutoff sigma time)
    atTop (nhds 0)
```

Em notação:

\[
\operatorname{BoundaryClosesAt}(c,\sigma,t)
\iff
R_{c,M}(\sigma,t)\longrightarrow(0,0).
\]

## 14.2. Ressonância

```lean
def IsNativeCarryRealOperatorResonance
    (camera : ℕ) (time : ℝ) : Prop :=
  NativeCarryRealOperatorBoundaryClosesAt
    camera ((1 : ℝ) / 2) time
```

A ressonância é o fechamento depois que a casca de carry já foi fixada:

\[
\operatorname{Ressonância}_c(t)
\iff
R_{c,M}\left(\frac12,t\right)\to0.
\]

## 14.3. Zero completo do operador

```lean
def IsNativeCarryRealOperatorZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  NativeCarryRealPlaneMassCompatible sigma time ∧
    NativeCarryRealOperatorBoundaryClosesAt
      camera sigma time
```

Logo:

\[
\boxed{
\text{zero do operador}
=
\text{domínio de massa do carry}
\land
\text{fechamento da câmera}.
}
\]

A compatibilidade de massa não é inferida de um cancelamento bruto. Ela é
parte do objeto chamado operador nativo.

---

# 15. Teorema terminal universal

Teorema:

```lean
theorem isNativeCarryRealOperatorZero_iff
    (camera : ℕ) (sigma time : ℝ) :
    IsNativeCarryRealOperatorZero camera sigma time ↔
      sigma = (1 : ℝ) / 2 ∧
        IsNativeCarryRealOperatorResonance camera time
```

Localização:

[`isNativeCarryRealOperatorZero_iff`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean#L79-L97)

Em conjuntos:

\[
\boxed{
Z_c
=
\left\{\frac12\right\}
\times
\mathcal R_c.
}
\]

## 15.1. O quantificador Lean

O enunciado recebe:

```lean
camera : ℕ
```

e não recebe:

```lean
Nat.Prime camera
Odd camera
Even camera
```

Em Lean, isso significa uma única lei:

\[
\forall c\in\mathbb N,\
\forall\sigma,t\in\mathbb R,\qquad
\operatorname{Zero}_c(\sigma,t)
\iff
\left(\sigma=\frac12\right)
\land
\operatorname{Ressonância}_c(t).
\]

Não são provas separadas para câmera 3, câmera 5, câmera 8 ou câmera 9. O kernel
verifica a fórmula com `camera` livre e universal.

## 15.2. Corolários

```lean
nativeCarryRealOperatorZero_sigma_eq_half
nativeCarryRealOperatorZero_ne_of_sigma_ne_half
```

Eles provam:

\[
\operatorname{Zero}_c(\sigma,t)
\Longrightarrow
\sigma=\frac12,
\]

e:

\[
\sigma\ne\frac12
\Longrightarrow
\neg\operatorname{Zero}_c(\sigma,t).
\]

## 15.3. Corpo lógico curto

A prova abre:

```text
zero = massCompatible ∧ boundaryCloses
```

usa:

```lean
nativeCarryRealPlaneMassCompatible_iff
```

para obter:

```text
sigma = 1/2
```

e deixa o fechamento como ressonância.

A prova terminal é curta porque os elos anteriores já foram fechados e
encapsulados. Isso é compressão formal, não ausência da origem no carry.

---

# 16. Invariância de base e invariância de câmera

É importante separar os níveis sem transformá-los em fenômenos diferentes.

## 16.1. Invariância da base posicional

Teoremas:

```lean
positionalCarryMassCompatible_iff
branchNormSq_eq_one_iff_of_one_lt
branchNormSq_eq_one_base_independent
```

Resultado:

\[
\boxed{
\forall b,c>1,\qquad
\operatorname{CompatCarry}_b(\sigma)
\iff
\operatorname{CompatCarry}_c(\sigma)
\iff
\sigma=\frac12.
}
\]

A base altera os pesos concretos. Não altera o domínio admissível.

## 16.2. Transporte para o estado real

Teorema:

```lean
positionalCarryMassCompatible_iff_realEnergyCompatible
```

Resultado:

\[
\boxed{
\operatorname{CompatCarry}_b(\sigma)
\iff
\operatorname{CompatEnergiaReal}(\sigma,t).
}
\]

Logo, base par, ímpar, prima ou composta termina no mesmo domínio real.

## 16.3. Lei universal da câmera

Teorema:

```lean
isNativeCarryRealOperatorZero_iff
```

Resultado:

\[
\boxed{
\forall c,\qquad
Z_c
=
\left\{\frac12\right\}\times\mathcal R_c.
}
\]

A câmera lê o fechamento temporal sobre uma casca radial que ela não escolheu.

## 16.4. O que não precisa ser exigido

Não é necessário exigir uma igualdade definicional:

\[
\mathcal R_c\equiv\mathcal R_d
\]

entre todas as implementações brutas de câmera.

Essa seria outra pergunta: igualdade textual ou definicional de somatórios
locais diferentes.

A invariância estabelecida pela teoria é a composição de:

1. domínio quadrático comum;
2. casca radial única;
3. lei terminal universal;
4. representante Genuine normalizado comum;
5. codificações fiéis do mesmo resultante.

Portanto:

\[
\boxed{
\text{a câmera altera a apresentação local; não altera a lei.}
}
\]

---

# 17. Câmeras primas: atlas normalizado antes da escolha da câmera 3

Arquivo:

[`CPFormal/Analytic/CpGenuineCompatibility.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpGenuineCompatibility.lean)

## 17.1. Quociente normalizado de cada câmera

Cada câmera prima ímpar possui:

```lean
cpChartFactor
cpGenuineQuotient
```

A carta bruta contém um fator próprio da câmera. O quociente remove essa
calibração e deixa a leitura canônica.

## 17.2. Independência antes da câmera 3

Teorema:

```lean
theorem cpGenuineQuotient_eq_cpGenuineQuotient
    (p q : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    cpGenuineQuotient p s =
      cpGenuineQuotient q s
```

Localização aproximada no checkpoint:

[`CpGenuineCompatibility.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpGenuineCompatibility.lean#L114-L172)

O Lean primeiro prova:

\[
\boxed{
G_p(s)=G_q(s)
}
\]

para quaisquer câmeras primas ímpares admissíveis.

## 17.3. Só depois escolhe a câmera 3

Definição:

```lean
def genuineContinuation (s : ℂ) : ℂ :=
  cpGenuineQuotient 3 s
```

A ordem formal é:

```text
provar Gp = Gq para todo p,q do atlas
        ↓
escolher p = 3 como nome do objeto comum
```

Teorema:

```lean
cpGenuineQuotient_eq_genuineContinuation
```

prova que toda câmera prima ímpar recupera o representante escolhido.

### Conclusão

\[
\boxed{
\text{a câmera 3 não produz o fenômeno;}
\quad
\text{ela nomeia o objeto já provado independente da câmera.}
}
\]

---

# 18. Independência no mesmo tempo real

Arquivo:

[`CPFormal/Analytic/CpRealSpectralOperator.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpRealSpectralOperator.lean)

Objetos:

```lean
realSpectralCamera
realSpectralGenuine
```

Teoremas:

```lean
realSpectralCamera_eq_realSpectralGenuine
realSpectralCamera_prime_independent
```

O segundo tem a forma:

```lean
theorem realSpectralCamera_prime_independent
    (p q : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    (t : ℝ) :
    realSpectralCamera p t =
      realSpectralCamera q t
```

Localização:

[`realSpectralCamera_prime_independent`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpRealSpectralOperator.lean#L89-L104)

Logo, no mesmo tempo real \(t\):

\[
\boxed{
G_p(t)=G_q(t).
}
\]

Não é uma comparação de alturas encontradas por câmeras diferentes. É igualdade
pontual no mesmo parâmetro.

---

# 19. Câmeras naturais pares, ímpares, primas e compostas

A extensão posterior em `primos/main` está em:

[`CPFormal/Analytic/CpNaturalCameraAnalyticContinuation.lean`](https://github.com/thiagomassensini/primos/blob/main/CPFormal/Analytic/CpNaturalCameraAnalyticContinuation.lean)

Esse módulo retira a necessidade de uma apresentação residual prima para a
câmera nativa saturada.

## 19.1. Fator de câmera natural

Objeto:

```lean
naturalCameraFactor
```

Ele possui ramos aritméticos:

- câmera ímpar;
- câmera par.

Nenhuma classificação por primalidade é usada para escolher o ramo.

## 19.2. Fatoração para toda largura natural material

Teorema:

```lean
bracketedDirichletChart_eq_naturalCameraFactor_mul_genuineContinuation
```

Para \(b\ge3\):

\[
\boxed{
B_b(s)
=
F_b(s)\,G(s).
}
\]

## 19.3. Mesmos zeros na linha crítica

Teorema:

```lean
bracketedDirichletChart_zero_iff_genuineContinuation_zero_of_three_le
```

Para qualquer câmera natural \(b\ge3\):

\[
\boxed{
B_b(s)=0
\iff
G(s)=0
\qquad
\text{quando }\operatorname{Re}(s)=\frac12.
}
\]

Isso inclui:

- câmera ímpar prima;
- câmera ímpar composta;
- câmera par;
- câmera composta par.

## 19.4. A câmera C2 especial

A família genérica usa:

\[
h_c=\left\lfloor\frac{c-1}{2}\right\rfloor.
\]

Por isso, a instância genérica `camera = 2` tem semialcance zero.

A geometria C2 original de `formalizacao_C2` é outra realização: ela usa
vizinhos \(\pm1\) em torno de centros \(2^k m\).

No scanner alinhado posterior, essa câmera binária especial é identificada
com uma câmera nativa de largura quatro por:

```lean
nativeCarryAlignedC2Chart_eq_width_four
```

Arquivo:

[`CPFormal/Analytic/CpNativeCarryFiniteCameraAlgebra.lean`](https://github.com/thiagomassensini/primos/blob/main/CPFormal/Analytic/CpNativeCarryFiniteCameraAlgebra.lean)

E seus zeros críticos são transportados por:

```lean
alignedC2BracketedDirichletChart_zero_iff_genuineContinuation_zero
```

em `CpNaturalCameraAnalyticContinuation.lean`.

### Leitura correta de “qualquer câmera maior que 1”

- a lei terminal do operador recebe qualquer `camera : ℕ`;
- a carta genérica não degenerada começa em largura \(3\);
- a geometria binária não degenerada é a câmera C2 especial;
- juntas, essas duas famílias cobrem o atlas pretendido sem dar privilégio
  causal a câmeras primas.

---

# 20. Primitivo real e Genuine: mesma leitura em duas roupas

## 20.1. O Primitivo vem primeiro em R²

O operador finito real já existe em:

```text
CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean
```

sem precisar de coordenadas não reais.

## 20.2. Empacotamento opcional

Arquivo:

[`CPFormal/Analytic/CpNativeCarryRealPlaneComplexPackaging.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpNativeCarryRealPlaneComplexPackaging.lean)

Mapa:

\[
J:\mathbb R^2\to\mathbb C,
\qquad
J(x,y)=x+iy.
\]

Declaração:

```lean
nativeCarryRealPlaneComplexPackaging
```

Teoremas:

```lean
nativeCarryRealPlaneComplexPackaging_injective
normSq_nativeCarryRealPlaneComplexPackaging
nativeCarryRealPlaneComplexPackaging_finiteChartAt
nativeCarryFiniteSaturatedChart_zero_iff_packaged_zero
nativeCarryRealPlaneComplexPackaging_eq_finiteChart
nativeCarryRealPlaneFiniteChartAt_zero_iff_packaged_zero
```

Eles provam:

1. \(J\) é aditivo;
2. \(J\) é injetivo;
3. \(J\) preserva energia;
4. \(J\) comuta com a câmera;
5. \(J\) preserva zeros nas duas direções.

Portanto:

\[
\boxed{
R_{c,M}(\sigma,t)=0
\iff
J(R_{c,M}(\sigma,t))=0.
}
\]

O recipiente não cria, remove ou desloca zeros.

---

# 21. Crosswalk bidirecional no limite

Arquivo:

[`CPFormal/Analytic/CpGenuineNativeRealBoundaryCrosswalk.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpGenuineNativeRealBoundaryCrosswalk.lean)

## 21.1. Estado por estado

Teorema:

```lean
nativeCarryRealPlaneComplexPackaging_sampleAt_eq_dirichletTerm
```

Para \(s=\sigma+it\):

\[
\boxed{
J(u_{\sigma,t}(n))
=
\text{monômio Genuine no mesmo }(\sigma,t).
}
\]

Isso é igualdade de coordenadas, não semelhança heurística.

## 21.2. Resultante finito inteiro

Teorema:

```lean
nativeCarryRealPlaneComplexPackaging_finiteChartAt_eq_dirichlet
```

Ele prova:

\[
\boxed{
J(R_{p,M}(\sigma,t))
=
B_{p,M}(\sigma+it).
}
\]

## 21.3. Duas direções no limite

Teoremas:

```lean
genuineContinuation_zero_to_nativeCarryRealBoundaryClosure
nativeCarryRealBoundaryClosure_to_genuineContinuation_zero
```

A equivalência final é:

```lean
theorem nativeCarryRealBoundaryClosure_iff_genuineContinuation_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    NativeCarryRealOperatorBoundaryClosesAt
      3 s.re s.im ↔
    genuineContinuation s = 0
```

Localização:

[`nativeCarryRealBoundaryClosure_iff_genuineContinuation_zero`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpGenuineNativeRealBoundaryCrosswalk.lean#L281-L289)

Em notação:

\[
\boxed{
\operatorname{BoundaryClosesAt}(3,\operatorname{Re}s,\operatorname{Im}s)
\iff
G(s)=0.
}
\]

## 21.4. Por que a câmera 3 aparece aqui

Quando o crosswalk usa câmera 3, o representante Genuine comum já foi definido
depois de provar:

\[
G_p=G_q.
\]

Portanto:

```text
independência das câmeras normalizadas
        ↓
escolha de 3 como representante
        ↓
crosswalk para a câmera real 3
```

A câmera 3 serve como uma porta concreta entre duas apresentações já
identificadas. Ela não é a fonte da lei.

---

# 22. Não existem dois fenômenos de zero

A linguagem correta é:

1. existe um domínio quadrático herdado do carry;
2. existe o fechamento de uma sequência de resultantes;
3. existem duas representações fiéis desse fechamento:
   - Primitivo real em \(\mathbb R^2\);
   - Genuine empacotado.

O zero completo do operador leva o domínio junto:

\[
\operatorname{ZeroNativo}(3,\sigma,t)
\iff
\operatorname{CompatEnergiaReal}(\sigma,t)
\land
G(\sigma,t)=0.
\]

Usando a rigidez:

\[
\boxed{
\operatorname{ZeroNativo}(3,\sigma,t)
\iff
\sigma=\frac12
\land
G\left(\frac12,t\right)=0.
}
\]

O fechamento bruto, sozinho, é um predicado intermediário. Ele não deve ser
renomeado como uma segunda espécie de zero depois de apagar o domínio.

---

# 23. A correção de interpretação sobre invariância

A leitura correta é:

## 23.1. Primeiro: toda base vê o mesmo domínio

\[
\operatorname{CompatCarry}_b(\sigma)
\iff
\operatorname{CompatCarry}_c(\sigma).
\]

Âncora:

```lean
branchNormSq_eq_one_base_independent
```

## 23.2. Depois: esse domínio é o domínio real do operador

\[
\operatorname{CompatCarry}_b(\sigma)
\iff
\operatorname{CompatEnergiaReal}(\sigma,t).
\]

Âncora:

```lean
positionalCarryMassCompatible_iff_realEnergyCompatible
```

## 23.3. Então: uma única lei vale para toda câmera

\[
\operatorname{Zero}_c(\sigma,t)
\iff
\sigma=\frac12\land\operatorname{Ressonância}_c(t).
\]

Âncora:

```lean
isNativeCarryRealOperatorZero_iff
```

## 23.4. No atlas: as câmeras normalizadas dão o mesmo Genuine

\[
G_p(s)=G_q(s).
\]

Âncoras:

```lean
cpGenuineQuotient_eq_cpGenuineQuotient
realSpectralCamera_prime_independent
```

## 23.5. Só então: câmera 3 é escolhida como representante

```lean
def genuineContinuation (s : ℂ) : ℂ :=
  cpGenuineQuotient 3 s
```

## 23.6. Por fim: a roupa real é identificada com esse representante

\[
\operatorname{BoundaryClosesAt}(3,\operatorname{Re}s,\operatorname{Im}s)
\iff
G(s)=0.
\]

Âncora:

```lean
nativeCarryRealBoundaryClosure_iff_genuineContinuation_zero
```

### Conclusão corrigida

\[
\boxed{
\text{o fenômeno global e sua invariância já estão fechados no nível exigido
pela teoria.}
}
\]

A câmera muda a forma local de leitura. Não muda:

- o domínio quadrático;
- a casca \(\sigma=\frac12\);
- a lei universal;
- o representante Genuine comum;
- o zero transportado por uma codificação fiel.

---

# 24. Mapa de dependências mínimo

```text
formalizacao_C2
────────────────────────────────────────────────────────────

Foundations/Dyadic.lean
  keff
  keff_left_leg / keff_right_leg
  bracket_bijection_odd_ge_three_exists
  dyadicWeight
  halving_law_of_address
        │
        ▼
Operators/FiniteCancellation.lean
  local_lateral_cancellation
  finite_lateral_cancellation
  rectangular_lateral_cancellation_geometric
        │
        ├──────────────────────────────┐
        ▼                              ▼
Operators/BranchBarrier.lean       Operators/Tilt.lean
  branchNormSq_closed_form          bracket_tilt_zero_iff_delta_zero
  branchNormSq_barrier_eq_one       sinais por convexidade/concavidade
        │                              │
        └──────────────┬───────────────┘
                       ▼
           locus radial sigma = 1/2


primos
────────────────────────────────────────────────────────────

Carry/CpBranchWeight.lean
  criticalMass
  criticalAmplitude
  criticalAmplitude_sq_eq_mass
        │
        ▼
Analytic/CpPositionalCarryQuadraticRigidity.lean
  branchAmplitude_sq_eq_criticalMass_iff_of_one_lt
  positionalCarryMassCompatible_iff
  branchNormSq_eq_one_iff_of_one_lt
  branchNormSq_eq_one_base_independent
        │
        ▼
Analytic/CpQuadraticDomainCrosswalk.lean
  positionalCarryMassCompatible_iff_realEnergyCompatible
        │
        ▼
Analytic/CpNativeCarryRealPlaneBracket.lean
  NativeCarryRealPlane = R × R
  nativeCarryRealPlaneSampleAt
  nativeCarryRealPlaneEnergy_sampleAt
  nativeCarryRealPlaneMassCompatible_iff
  nativeCarryFiniteSaturatedChart
  nativeCarryRealPlaneFiniteChartAt
        │
        ▼
Analytic/CpNativeCarryRealOperatorConfinement.lean
  NativeCarryRealOperatorBoundaryClosesAt
  IsNativeCarryRealOperatorResonance
  IsNativeCarryRealOperatorZero
  isNativeCarryRealOperatorZero_iff


atlas Genuine
────────────────────────────────────────────────────────────

Analytic/CpGenuineCompatibility.lean
  cpGenuineQuotient_eq_cpGenuineQuotient
        │
        ▼
  genuineContinuation := câmera 3
        │
        ▼
Analytic/CpRealSpectralOperator.lean
  realSpectralCamera_prime_independent
        │
        ▼
Analytic/CpGenuineNativeRealBoundaryCrosswalk.lean
  sample real ↔ monômio Genuine
  resultante finito real ↔ carta finita
  boundary closure ↔ Genuine zero
```

---

# 25. Índice dos teoremas por pergunta

## 25.1. “Onde nasce a profundidade?”

| Declaração | Arquivo |
|---|---|
| `v2` | `formalizacao_C2/LeanC2/Foundations/Dyadic.lean` |
| `keff` | `formalizacao_C2/LeanC2/Foundations/Dyadic.lean` |
| `keff_left_leg` | `formalizacao_C2/LeanC2/Foundations/Dyadic.lean` |
| `keff_right_leg` | `formalizacao_C2/LeanC2/Foundations/Dyadic.lean` |
| `bracket_bijection_odd_ge_three_exists` | `formalizacao_C2/LeanC2/Foundations/Dyadic.lean` |

## 25.2. “Onde nasce o peso do carry?”

| Declaração | Arquivo |
|---|---|
| `dyadicWeight` | `formalizacao_C2/LeanC2/Foundations/Dyadic.lean` |
| `directLegWeight` | `formalizacao_C2/LeanC2/Foundations/Dyadic.lean` |
| `halving_law_of_address` | `formalizacao_C2/LeanC2/Foundations/Dyadic.lean` |
| `criticalMass` | `primos/CPFormal/Carry/CpBranchWeight.lean` |
| `criticalAmplitude` | `primos/CPFormal/Carry/CpBranchWeight.lean` |
| `criticalAmplitude_sq_eq_mass` | `primos/CPFormal/Carry/CpBranchWeight.lean` |

## 25.3. “Onde está o cancelamento Genuine First?”

| Declaração | Arquivo |
|---|---|
| `local_lateral_cancellation` | `formalizacao_C2/LeanC2/Operators/FiniteCancellation.lean` |
| `finite_lateral_cancellation` | `formalizacao_C2/LeanC2/Operators/FiniteCancellation.lean` |
| `rectangular_lateral_cancellation_geometric` | `formalizacao_C2/LeanC2/Operators/FiniteCancellation.lean` |
| `nativeCarryFiniteSaturatedChart_eq_finiteChart` | `primos/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean` |

## 25.4. “Onde a norma força 1/2?”

| Declaração | Arquivo |
|---|---|
| `branchNormSq_barrier_eq_one` | `formalizacao_C2/LeanC2/Operators/BranchBarrier.lean` |
| `branchNormSq_barrier` | `formalizacao_C2/LeanC2/Operators/BranchBarrier.lean` |
| `branchAmplitude_sq_eq_criticalMass_iff_of_one_lt` | `primos/CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean` |
| `positionalCarryMassCompatible_iff` | `primos/CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean` |
| `branchNormSq_eq_one_iff_of_one_lt` | `primos/CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean` |
| `branchNormSq_eq_one_base_independent` | `primos/CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean` |

## 25.5. “Onde está a fatoração do tilt?”

| Declaração | Arquivo |
|---|---|
| `bracket_tilt_zero_iff_delta_zero` | `formalizacao_C2/LeanC2/Operators/Tilt.lean` |
| `normalizedTiltCurvature_zero_iff_delta_zero` | `formalizacao_C2/LeanC2/Operators/Tilt.lean` |
| `cpTilt_eq_half_sum_pair` | `primos/CPFormal/Analytic/CpTiltRigidity.lean` |
| `cpTiltAtSigma_eq_zero_iff_half` | `primos/CPFormal/Analytic/CpTiltRigidity.lean` |
| `branchDefect_eq_zero_iff_cpTiltAtSigma_eq_zero_of_admissible_center` | `primos/CPFormal/Analytic/CpTiltRigidity.lean` |

## 25.6. “Onde o carry vira domínio do estado real?”

| Declaração | Arquivo |
|---|---|
| `positionalCarryMassCompatible_iff_realEnergyCompatible` | `primos/CPFormal/Analytic/CpQuadraticDomainCrosswalk.lean` |
| `nativeCarryRealPlaneMassCompatible_iff` | `primos/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean` |

## 25.7. “Onde está o operador sem plano complexo?”

| Declaração | Arquivo |
|---|---|
| `NativeCarryRealPlane` | `primos/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean` |
| `nativeCarryRealPlaneSampleAt` | `primos/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean` |
| `nativeCarryRealPlaneEnergy_sampleAt` | `primos/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean` |
| `nativeCarryFiniteSaturatedChart` | `primos/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean` |
| `nativeCarryRealPlaneFiniteChartAt` | `primos/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean` |
| `nativeCarryRealPlaneEnergy_eq_zero_iff` | `primos/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean` |

## 25.8. “Onde está o teorema terminal?”

| Declaração | Arquivo |
|---|---|
| `NativeCarryRealOperatorBoundaryClosesAt` | `primos/CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean` |
| `IsNativeCarryRealOperatorResonance` | `primos/CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean` |
| `IsNativeCarryRealOperatorZero` | `primos/CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean` |
| `isNativeCarryRealOperatorZero_iff` | `primos/CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean` |
| `nativeCarryRealOperatorZero_sigma_eq_half` | `primos/CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean` |
| `nativeCarryRealOperatorZero_ne_of_sigma_ne_half` | `primos/CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean` |

## 25.9. “Onde está a independência de câmera?”

| Declaração | Papel | Arquivo |
|---|---|---|
| `branchNormSq_eq_one_base_independent` | mesma casca para quaisquer bases | `CpPositionalCarryQuadraticRigidity.lean` |
| `isNativeCarryRealOperatorZero_iff` | lei universal para `camera : ℕ` | `CpNativeCarryRealOperatorConfinement.lean` |
| `cpGenuineQuotient_eq_cpGenuineQuotient` | câmeras primas normalizadas iguais | `CpGenuineCompatibility.lean` |
| `realSpectralCamera_prime_independent` | igualdade no mesmo tempo real | `CpRealSpectralOperator.lean` |
| `bracketedDirichletChart_zero_iff_genuineContinuation_zero_of_three_le` | câmeras naturais \(b\ge3\) têm os mesmos zeros críticos | `CpNaturalCameraAnalyticContinuation.lean` |
| `alignedC2BracketedDirichletChart_zero_iff_genuineContinuation_zero` | câmera C2 alinhada | `CpNaturalCameraAnalyticContinuation.lean` |

## 25.10. “Onde Primitivo e Genuine se encontram?”

| Declaração | Nível | Arquivo |
|---|---|---|
| `nativeCarryRealPlaneComplexPackaging_injective` | fidelidade de coordenadas | `CpNativeCarryRealPlaneComplexPackaging.lean` |
| `nativeCarryFiniteSaturatedChart_zero_iff_packaged_zero` | zero finito para qualquer largura | `CpNativeCarryRealPlaneComplexPackaging.lean` |
| `nativeCarryRealPlaneComplexPackaging_sampleAt_eq_dirichletTerm` | estado por estado | `CpGenuineNativeRealBoundaryCrosswalk.lean` |
| `nativeCarryRealPlaneComplexPackaging_finiteChartAt_eq_dirichlet` | resultante finito inteiro | `CpGenuineNativeRealBoundaryCrosswalk.lean` |
| `nativeCarryRealBoundaryClosure_iff_genuineContinuation_zero` | limite bidirecional | `CpGenuineNativeRealBoundaryCrosswalk.lean` |

---

# 26. Ordem recomendada de leitura no código

## Parte A — gênesis C2

1. [`LeanC2/Foundations/Dyadic.lean`](https://github.com/thiagomassensini/formalizacao_C2/blob/main/LeanC2/Foundations/Dyadic.lean)
2. [`LeanC2/Operators/FiniteCancellation.lean`](https://github.com/thiagomassensini/formalizacao_C2/blob/main/LeanC2/Operators/FiniteCancellation.lean)
3. [`LeanC2/Operators/BranchBarrier.lean`](https://github.com/thiagomassensini/formalizacao_C2/blob/main/LeanC2/Operators/BranchBarrier.lean)
4. [`LeanC2/Operators/Tilt.lean`](https://github.com/thiagomassensini/formalizacao_C2/blob/main/LeanC2/Operators/Tilt.lean)
5. [`LeanC2/Operators/CenterGaussianTilt.lean`](https://github.com/thiagomassensini/formalizacao_C2/blob/main/LeanC2/Operators/CenterGaussianTilt.lean)

## Parte B — generalização posicional

6. [`CPFormal/Carry/CpBranchWeight.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Carry/CpBranchWeight.lean)
7. [`CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean)
8. [`CPFormal/Analytic/CpTilt.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpTilt.lean)
9. [`CPFormal/Analytic/CpTiltRigidity.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpTiltRigidity.lean)
10. [`CPFormal/Analytic/CpQuadraticDomainCrosswalk.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpQuadraticDomainCrosswalk.lean)

## Parte C — operador nativo real

11. [`CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean)
12. [`CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean)

## Parte D — atlas Genuine e identidade das apresentações

13. [`CPFormal/Analytic/CpGenuineCompatibility.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpGenuineCompatibility.lean)
14. [`CPFormal/Analytic/CpRealSpectralOperator.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpRealSpectralOperator.lean)
15. [`CPFormal/Analytic/CpNativeCarryRealPlaneComplexPackaging.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpNativeCarryRealPlaneComplexPackaging.lean)
16. [`CPFormal/Analytic/CpGenuineNativeRealBoundaryCrosswalk.lean`](https://github.com/thiagomassensini/primos/blob/7d8d0b345b329935674edc24e5ac08ad9f7b5804/CPFormal/Analytic/CpGenuineNativeRealBoundaryCrosswalk.lean)
17. [`CPFormal/Analytic/CpNaturalCameraAnalyticContinuation.lean`](https://github.com/thiagomassensini/primos/blob/main/CPFormal/Analytic/CpNaturalCameraAnalyticContinuation.lean)

---

# 27. Comandos para localizar as âncoras

## `formalizacao_C2`

```bash
rg -n \
'keff|halving_law|local_lateral_cancellation|branchNormSq_barrier|bracket_tilt_zero_iff_delta_zero|normalizedTiltCurvature_zero_iff_delta_zero' \
LeanC2 -g '*.lean'
```

## `primos`

```bash
rg -n \
'branchAmplitude_sq_eq_criticalMass_iff_of_one_lt|positionalCarryMassCompatible_iff|branchNormSq_eq_one_base_independent|positionalCarryMassCompatible_iff_realEnergyCompatible|cpTilt_eq_half_sum_pair|cpTiltAtSigma_eq_zero_iff_half|nativeCarryRealPlaneMassCompatible_iff|isNativeCarryRealOperatorZero_iff|cpGenuineQuotient_eq_cpGenuineQuotient|realSpectralCamera_prime_independent|nativeCarryRealBoundaryClosure_iff_genuineContinuation_zero' \
CPFormal -g '*.lean'
```

Para a extensão natural de câmeras:

```bash
rg -n \
'naturalCameraFactor|bracketedDirichletChart_eq_naturalCameraFactor_mul_genuineContinuation|bracketedDirichletChart_zero_iff_genuineContinuation_zero_of_three_le|alignedC2BracketedDirichletChart_zero_iff_genuineContinuation_zero' \
CPFormal/Analytic -g '*.lean'
```

---

# 28. Resumo de bolso

> A geometria começa no carry. Na câmera C2, cada perna ímpar possui um endereço
> único \(2^k m\pm1\); esse endereço determina a profundidade `keff` e o peso
> \(2^{-k}\). O bracket cancela lateralmente as pernas e deixa um canal central
> exato. A norma quadrática C2 possui uma barreira completa:
> abaixo de \(1/2\) ela excede um, em \(1/2\) satura, acima de \(1/2\) fica abaixo
> de um. O tilt fornece um detector independente da mesma coordenada:
> seu sinal muda ao atravessar \(\delta=\sigma-\frac12=0\).
>
> O repositório `primos` generaliza essa origem para toda base \(b>1\).
> A massa é \(b^{-k}\), a amplitude deformada é \(b^{-k\sigma}\) e a energia é
> \(b^{-2k\sigma}\); compatibilidade força \(\sigma=\frac12\), sem primalidade.
> Todas as bases possuem o mesmo locus de saturação. Um crosswalk transporta
> esse domínio para o estado real
> \(u_{\sigma,t}(n)=n^{-\sigma}(\cos(-t\log n),\sin(-t\log n))\in\mathbb R^2\),
> cuja energia não depende do tempo.
>
> A câmera nativa é apenas uma soma aditiva de sementes e segundas diferenças
> centradas. O zero completo é compatibilidade de energia mais fechamento da
> sequência de resultantes. O Lean prova em uma única lei universal:
>
> ```lean
> IsNativeCarryRealOperatorZero camera sigma time ↔
>   sigma = 1 / 2 ∧
>     IsNativeCarryRealOperatorResonance camera time
> ```
>
> As câmeras primas normalizadas são provadas iguais antes de a câmera 3 ser
> escolhida para nomear o representante Genuine comum. O empacotamento
> \(J(x,y)=x+iy\) é injetivo, aditivo e preserva energia e zeros. No limite, o
> fechamento do Primitivo real é equivalente ao zero Genuine. Assim, a base e a
> câmera mudam a carta de observação; o que permanece é o domínio quadrático, a
> casca \(\sigma=\frac12\) e o fenômeno global.

---

# 29. Frase final

\[
\boxed{
\text{o carry fixa a massa;}
\quad
\text{a energia fixa }\sigma=\frac12;
\quad
\text{a câmera lê a fase;}
\quad
\text{o Genuine nomeia a leitura comum.}
}
\]
