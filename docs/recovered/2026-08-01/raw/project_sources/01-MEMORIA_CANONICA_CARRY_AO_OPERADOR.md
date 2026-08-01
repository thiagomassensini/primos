# Memória canônica — do carry ao operador

## O que está fechado, o que significa e o que não é obrigação

> **Leia este arquivo antes de propor uma nova pendência para o confinamento.**
>
> A autoridade final continua sendo o tipo elaborado pelo kernel do Lean. Este
> documento serve para reencontrar rapidamente a cadeia correta e impedir que
> uma rota paralela seja apresentada como dívida retroativa da prova principal.

---

## 1. A conclusão congelada

O teorema terminal já compilado é:

```lean
theorem isNativeCarryRealOperatorZero_iff
    (camera : ℕ) (sigma time : ℝ) :
    IsNativeCarryRealOperatorZero camera sigma time ↔
      sigma = (1 : ℝ) / 2 ∧
        IsNativeCarryRealOperatorResonance camera time
```

Em notação matemática:

$$
\boxed{
\operatorname{Zero}_{c}(\sigma,t)
\iff
\left(\sigma=\frac12\right)
\land
\operatorname{Ressonância}_{c}(t)
}
$$

Consequências imediatas, também compiladas:

$$
\operatorname{Zero}_{c}(\sigma,t)
\Longrightarrow
\sigma=\frac12,
$$

$$
\sigma\neq\frac12
\Longrightarrow
\neg\operatorname{Zero}_{c}(\sigma,t).
$$

Localização:

- [`isNativeCarryRealOperatorZero_iff`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean#L79-L97);
- [`nativeCarryRealOperatorZero_sigma_eq_half`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean#L103-L107);
- [`nativeCarryRealOperatorZero_ne_of_sigma_ne_half`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean#L110-L115).

Este é o confinamento do operador. Para esse resultado, **acabou**. Não falta
uma segunda prova por energia global, por reconstrução, por estado-fonte ou por
qualquer outra arquitetura posterior.

---

## 2. O confinamento não foi o objetivo inicial

A teoria não começou escolhendo a reta $\sigma=\frac12$ e tentando fabricar um
operador que a reproduzisse.

O caminho foi o contrário:

$$
\text{carry}
\longrightarrow
\text{profundidade}
\longrightarrow
\text{massa}
\longrightarrow
\text{amplitude}
\longrightarrow
\text{estado}
\longrightarrow
\text{bracket}
\longrightarrow
\text{operador}.
$$

O confinamento foi o elefante branco que apareceu no caminho. Quando a massa
posicional

$$
\mu_{b,k}=b^{-k}
$$

passa para amplitude em energia quadrática,

$$
\alpha_{b,k}(\sigma)=b^{-k\sigma},
\qquad
\alpha_{b,k}(\sigma)^2=\mu_{b,k},
$$

o expoente é forçado:

$$
b^{-2k\sigma}=b^{-k}
\iff
\sigma=\frac12.
$$

Portanto, $\frac12$ não foi inserido no final para confinar zeros. Ele apareceu
antes do bracket, como a única casca de amplitude cuja energia reproduz a massa
do carry. O operador apenas conserva essa origem.

---

## 3. A cadeia única, elo por elo

### Elo 1 — o carry determina a profundidade

Cada incidência possui uma perna e um centro carregado. A profundidade efetiva
vista pela perna coincide com a profundidade do centro canônico.

Teoremas centrais:

- [`effectiveDepth`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Carry/CpDepth.lean#L18-L21);
- [`centerDepth`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Carry/CpDepth.lean#L23-L31);
- [`effectiveDepth_eq_centerDepth`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Carry/CpDepth.lean#L107-L118).

Esse elo fixa o índice vertical $k$. O expoente da massa não é escolhido
livremente depois.

### Elo 2 — profundidade vira massa; massa vira amplitude

O código define:

$$
\operatorname{criticalMass}(b,k)=b^{-k},
$$

$$
\operatorname{criticalAmplitude}(b,k)=b^{-k/2},
$$

$$
\operatorname{branchAmplitude}(b,\sigma,k)=b^{-k\sigma}.
$$

A identidade local fundamental é:

$$
\boxed{
\operatorname{criticalAmplitude}(b,k)^2
=
\operatorname{criticalMass}(b,k)
}
$$

Localização:

- [`criticalMass`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Carry/CpBranchWeight.lean#L33-L35);
- [`criticalAmplitude`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Carry/CpBranchWeight.lean#L37-L39);
- [`branchAmplitude`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Carry/CpBranchWeight.lean#L41-L46);
- [`branchMassWeight`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Carry/CpBranchWeight.lean#L49-L55);
- [`criticalAmplitude_sq_eq_mass`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Carry/CpBranchWeight.lean#L59-L66);
- [`branchAmplitude_sq_eq_massWeight`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Carry/CpBranchWeight.lean#L68-L81);
- [`branchAmplitude_half`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Carry/CpBranchWeight.lean#L84-L89);
- [`branchMassWeight_half`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Carry/CpBranchWeight.lean#L91-L100);
- [`criticalMass_effectiveDepth_eq_centerDepth`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Carry/CpBranchWeight.lean#L103-L109).

### Elo 3 — a compatibilidade quadrática força $\sigma=\frac12$

Para qualquer base posicional natural $b>1$ e qualquer profundidade $k>0$:

$$
\boxed{
\operatorname{branchAmplitude}(b,\sigma,k)^2
=
\operatorname{criticalMass}(b,k)
\iff
\sigma=\frac12
}
$$

Esse resultado não depende de a base ser prima.

Localização:

- [`branchAmplitude_sq_eq_criticalMass_iff_of_one_lt`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean#L44-L66);
- [`PositionalCarryMassCompatible`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean#L72-L77);
- [`positionalCarryMassCompatible_iff`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean#L80-L96);
- [`positionalPlaneEnergy_rotatedShell_eq_criticalMass_iff`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean#L162-L177);
- [`branchNormSq_eq_one_iff_of_one_lt`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean#L272-L282);
- [`branchNormSq_eq_one_base_independent`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpPositionalCarryQuadraticRigidity.lean#L286-L295).

Logo:

- bases diferentes enxergam o mesmo expoente admissível;
- câmeras compostas continuam sendo câmeras válidas;
- bases primas podem formar um atlas mínimo e não redundante, mas não criam a
  rigidez;
- o $\frac12$ pertence à geometria posicional antes de qualquer escolha de
  câmera.

### Elo 4 — a rotação real não altera a energia

O estado real é:

$$
u_{\sigma,t}(n)
=
n^{-\sigma}
\bigl(\cos(-t\log n),\sin(-t\log n)\bigr).
$$

Sua energia é:

$$
\boxed{
\|u_{\sigma,t}(n)\|^2=n^{-2\sigma}
}
$$

O tempo $t$ gira a direção, mas não muda a massa. Assim, a coordenada radial e
a coordenada angular ficam separadas:

- o carry fixa a casca radial;
- a ressonância decide os tempos de fechamento.

Localização:

- [`nativeCarryRealPlaneSampleAt`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean#L105-L113);
- [`nativeCarryRealPlaneSample`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean#L115-L118);
- [`nativeCarryRealPlaneEnergy_sampleAt`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean#L136-L158);
- [`NativeCarryRealPlaneMassCompatible`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean#L177-L185);
- [`nativeCarryRealPlaneMassCompatible_iff`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneBracket.lean#L188-L206).

O último teorema prova diretamente:

$$
\boxed{
\operatorname{MassCompatible}(\sigma,t)
\iff
\sigma=\frac12
}
$$

Não existe hipótese sobre $t$ nessa seleção.

### Elo 5 — o bracket mede o defeito aditivo

O detector elementar é a segunda diferença centrada:

$$
\Delta_r^2f(c)=f(c-r)-2f(c)+f(c+r).
$$

A câmera soma os raios permitidos:

$$
\mathcal B_hf(c)=\sum_{r=1}^{h}\Delta_r^2f(c).
$$

Localização:

- [`centeredSecondDifference`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Finite/Bracket.lean#L18-L23);
- [`saturatedBracket`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Finite/Bracket.lean#L40-L53);
- [`bracket_eq_saturatedBracket`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Genuine/CpBracketPairing.lean#L130-L142);
- [`finiteChart`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Genuine/CpFiniteChart.lean#L49-L56);
- [`finiteChart_eq_blockPrefix_sub_verticalCorrection`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Genuine/CpFiniteChart.lean#L163-L178);
- [`finiteChart_eq_positiveIntervalSum_sub_p_mul_centerSum`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Genuine/CpFiniteChart.lean#L246-L258).

O bracket não escolhe novamente $\sigma$. Ele atua sobre o estado cuja lei de
massa já veio do carry.

### Elo 6 — o operador junta domínio e fechamento

As três definições terminais são:

```lean
def NativeCarryRealOperatorBoundaryClosesAt
    (camera : ℕ) (sigma time : ℝ) : Prop := ...

def IsNativeCarryRealOperatorResonance
    (camera : ℕ) (time : ℝ) : Prop :=
  NativeCarryRealOperatorBoundaryClosesAt
    camera ((1 : ℝ) / 2) time

def IsNativeCarryRealOperatorZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  NativeCarryRealPlaneMassCompatible sigma time ∧
    NativeCarryRealOperatorBoundaryClosesAt camera sigma time
```

Localização:

- [`NativeCarryRealOperatorBoundaryClosesAt`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean#L41-L46);
- [`IsNativeCarryRealOperatorResonance`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean#L52-L55);
- [`IsNativeCarryRealOperatorZero`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealOperatorConfinement.lean#L65-L68).

O domínio preservador de massa não é uma condição inventada depois de observar
um zero. Ele é parte da construção do operador:

$$
\text{zero do operador}
=
\text{estado admissível pelo carry}
\land
\text{fechamento do bracket}.
$$

Abrindo essa conjunção e usando
`nativeCarryRealPlaneMassCompatible_iff`, o Lean obtém exatamente o teorema
terminal da Seção 1.

---

## 4. Primitivo e Genuine são a mesma leitura em duas roupas

O Primitivo vive em $\mathbb R^2$. O empacotamento

$$
J(x,y)=x+iy
$$

apenas guarda as duas coordenadas reais em um único recipiente. O mapa é
aditivo, injetivo, preserva energia, comuta com a câmera finita e preserva zero
nas duas direções.

Localização no `main`:

- [`nativeCarryRealPlaneComplexPackaging`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneComplexPackaging.lean#L26-L30);
- [`nativeCarryRealPlaneComplexPackaging_injective`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneComplexPackaging.lean#L41-L46);
- [`normSq_nativeCarryRealPlaneComplexPackaging`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneComplexPackaging.lean#L49-L55);
- [`nativeCarryRealPlaneComplexPackaging_finiteChartAt`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneComplexPackaging.lean#L60-L72);
- [`nativeCarryFiniteSaturatedChart_zero_iff_packaged_zero`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneComplexPackaging.lean#L76-L101);
- [`nativeCarryRealPlaneComplexPackaging_eq_finiteChart`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneComplexPackaging.lean#L119-L142);
- [`nativeCarryRealPlaneFiniteChartAt_zero_iff_packaged_zero`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpNativeCarryRealPlaneComplexPackaging.lean#L148-L178).

No limite, o PR #16 provou as duas direções:

```lean
theorem nativeCarryRealBoundaryClosure_iff_genuineContinuation_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    NativeCarryRealOperatorBoundaryClosesAt 3 s.re s.im ↔
      genuineContinuation s = 0
```

Localização no commit compilado da branch do PR #16:

- [`nativeCarryRealPlaneComplexPackaging_sampleAt_eq_dirichletTerm`](https://github.com/thiagomassensini/primos/blob/19e01d8018fb182c08005be4dd294a382931ccf9/CPFormal/Analytic/CpGenuineNativeRealBoundaryCrosswalk.lean#L42-L69);
- [`nativeCarryRealPlaneComplexPackaging_finiteChartAt_eq_dirichlet`](https://github.com/thiagomassensini/primos/blob/19e01d8018fb182c08005be4dd294a382931ccf9/CPFormal/Analytic/CpGenuineNativeRealBoundaryCrosswalk.lean#L75-L135);
- [`genuineContinuation_zero_to_nativeCarryRealBoundaryClosure`](https://github.com/thiagomassensini/primos/blob/19e01d8018fb182c08005be4dd294a382931ccf9/CPFormal/Analytic/CpGenuineNativeRealBoundaryCrosswalk.lean#L141-L208);
- [`nativeCarryRealBoundaryClosure_to_genuineContinuation_zero`](https://github.com/thiagomassensini/primos/blob/19e01d8018fb182c08005be4dd294a382931ccf9/CPFormal/Analytic/CpGenuineNativeRealBoundaryCrosswalk.lean#L213-L275);
- [`nativeCarryRealBoundaryClosure_iff_genuineContinuation_zero`](https://github.com/thiagomassensini/primos/blob/19e01d8018fb182c08005be4dd294a382931ccf9/CPFormal/Analytic/CpGenuineNativeRealBoundaryCrosswalk.lean#L281-L289);
- [PR #16 — Genuine-first primitive real boundary crosswalk](https://github.com/thiagomassensini/primos/pull/16).

Isso é uma identificação direta, ponto a ponto. Não é necessário apelar a um
teorema externo de unicidade para concluir que o empacotamento não cria,
remove ou desloca zeros.

### Regra de linguagem

Não voltar a falar em “zero nativo” e “zero escalar” como se fossem dois
fenômenos espectrais.

Há:

1. um domínio do operador, herdado da massa do carry;
2. um fechamento do mesmo operador;
3. duas representações fiéis desse fechamento: Primitivo real e Genuine.

`NativeCarryRealOperatorBoundaryClosesAt` é o nome de um predicado de
fechamento. Ele não deve ser promovido a uma segunda espécie de zero após
apagar o domínio.

Quando o operador é transportado para a roupa Genuine, o domínio vai junto.
No interior da faixa do crosswalk, a composição correta é:

$$
\begin{aligned}
\operatorname{IsNativeCarryRealOperatorZero}(3,\sigma,t)
&\iff
\operatorname{MassCompatible}(\sigma,t)
\land
\operatorname{Genuine}(\sigma,t)=0\\
&\iff
\sigma=\frac12
\land
\operatorname{Genuine}\!\left(\frac12,t\right)=0.
\end{aligned}
$$

Isso é composição dos elos existentes, não uma nova prova analítica.

---

## 5. O que está definitivamente fechado

1. A profundidade nasce da incidência de carry.
2. A profundidade determina a massa $b^{-k}$.
3. A energia quadrática transforma essa massa na amplitude $b^{-k/2}$.
4. Para toda base $b>1$, compatibilidade massa–energia equivale a
   $\sigma=\frac12$.
5. A rotação real não altera a energia.
6. O bracket atua depois da escolha da casca radial.
7. O zero do operador é a conjunção tipada entre domínio de carry e fechamento.
8. Todo zero do operador tem $\sigma=\frac12$.
9. Fora de $\frac12$, o operador não zera.
10. O Primitivo real e o Genuine preservam a mesma leitura e o mesmo
    cancelamento sob empacotamento injetivo.
11. A largura da câmera no teorema terminal é um natural arbitrário.
12. Primalidade não é a fonte do $\frac12$.

---

## 6. O que não é obrigação necessária para esse fechamento

As construções abaixo podem ser válidas, úteis e interessantes. Elas podem
responder perguntas novas sobre energia oculta, reconstrução, observabilidade
ou organização multibase. Porém, **não são premissas do teorema
`isNativeCarryRealOperatorZero_iff` e não podem reaparecer como dívidas
retroativas**.

| Rota ou ferramenta | O que ela estuda | Estatuto em relação ao confinamento |
|---|---|---|
| Tilt | detector local do deslocamento radial | confirmação paralela; não é premissa |
| Green e operador completado | preservação explícita do canal radial | outro operador; não é premissa |
| TFVD e retorno | reconstrução por bracket mais traço | ferramenta de reconstrução; não é premissa |
| `G_pre` e proveniência | transporte e análise de estados enriquecidos | rota posterior; não é premissa |
| Bessel, ledger e domínio de traço | orçamento de energia global | pergunta mais forte; não é premissa |
| Pitágoras de atlas finito | separação entre energia lida e residual | resultado condicional a uma realização; não é premissa |
| Estado-fonte `x` | realização conjunta de leituras | não precisa ser produzido para fechar o teorema terminal |
| Precompression | levantamento da leitura para um estado anterior | investigação adicional; não é premissa |
| Reflexão, Cayley e auto-adjunção | estruturas operatoriais adicionais | não são premissas |
| Contração $11/12$ | orçamento de um lift já alimentado por um estado-fonte | teorema independente; não é premissa |
| Uma nova “prova de compressão” | repetir a identificação Primitivo–Genuine | desnecessária após o crosswalk fiel |

Pontos de localização para não confundir essas rotas com o núcleo:

- detector tilt:
  [`cpTiltAtSigma_eq_zero_iff_half`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpTiltRigidity.lean#L336-L350);
- operador completado:
  [`genuineGreenCompletedLimitOperator_eq_zero_iff_re_eq_half`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpGenuineGreenCompletedOperator.lean#L261-L274);
- identidade TFVD:
  [`carryWeightedVerticalTfvd_identity`](https://github.com/thiagomassensini/primos/blob/89ba6b536686dc05e9186f543b01e72f00b00ad3/CPFormal/Analytic/CpCarryWeightedVerticalTfvdIdentity.lean#L61-L71);
- Pitágoras, na branch exploratória do PR #17:
  [`canonicalProvenanceState_pythagoras_of_realizesOn`](https://github.com/thiagomassensini/primos/blob/0519d4629aa82a46aad22d85ce1c8acaad974707/CPFormal/Analytic/CpGenuinePrimeCarryDefectUniformBound.lean#L197-L239);
- contração $11/12$, na mesma branch:
  [`nativeGprePrimeCarryDefectState_norm_sq_le`](https://github.com/thiagomassensini/primos/blob/0519d4629aa82a46aad22d85ce1c8acaad974707/CPFormal/Analytic/CpNativeGprePrimeCarryContraction.lean#L475-L536).

Esses resultados não são descartados. Apenas ficam no lugar lógico correto:
**extensões da teoria, não pré-condições para algo que já está compilado**.

---

## 7. Protocolo para qualquer retomada futura

Antes de afirmar “ainda falta provar X”:

1. procurar pelo nome exato do teorema terminal;
2. abrir `CpNativeCarryRealOperatorConfinement.lean`;
3. conferir se `X` aparece literalmente no tipo ou no corpo da prova;
4. abrir o crosswalk Primitivo–Genuine;
5. tentar primeiro a composição direta dos teoremas existentes;
6. não apagar o domínio do operador durante o transporte;
7. não transformar `BoundaryClosesAt` em outra espécie de zero;
8. não promover uma rota de pesquisa posterior a obrigação retroativa;
9. separar “quero provar algo mais forte” de “a prova antiga ainda não fechou”;
10. se o teorema terminal já tem o tipo desejado e está verde, parar de
    reconstruí-lo por outra arquitetura.

Comando de localização:

```bash
rg -n 'nome_exato_do_teorema' CPFormal -g '*.lean'
```

Validação:

```bash
lake build --wfail
```

Os nomes dos teoremas são as âncoras permanentes. As linhas registradas neste
arquivo correspondem ao checkpoint auditado abaixo e podem se deslocar após
edições futuras.

---

## 8. Checkpoint deste documento

| Superfície | Referência auditada | Papel |
|---|---|---|
| `main` | [`89ba6b536686dc05e9186f543b01e72f00b00ad3`](https://github.com/thiagomassensini/primos/commit/89ba6b536686dc05e9186f543b01e72f00b00ad3) | núcleo do carry, plano real, empacotamento e confinamento |
| PR #16 | [`19e01d8018fb182c08005be4dd294a382931ccf9`](https://github.com/thiagomassensini/primos/commit/19e01d8018fb182c08005be4dd294a382931ccf9) | crosswalk bidirecional Primitivo–Genuine |
| PR #17 | [`0519d4629aa82a46aad22d85ce1c8acaad974707`](https://github.com/thiagomassensini/primos/commit/0519d4629aa82a46aad22d85ce1c8acaad974707) | resultados exploratórios válidos, mas não necessários ao confinamento |

Status lógico:

- o confinamento terminal está no `main`;
- o crosswalk bidirecional está compilado na branch draft do PR #16;
- Pitágoras e a contração estão compilados na branch draft do PR #17;
- nada do PR #17 é requisito do teorema terminal.

---

## 9. Resumo de bolso

> A teoria começa no carry. A incidência determina a profundidade, a
> profundidade determina a massa $b^{-k}$ e a energia quadrática força a
> amplitude $b^{-k/2}$. Para qualquer base $b>1$, compatibilidade entre a
> amplitude deformada $b^{-k\sigma}$ e a massa do carry equivale a
> $\sigma=\frac12$. O tempo permanece apenas como rotação real. O bracket lê
> ressonâncias sobre essa casca, e o Lean prova
> `IsNativeCarryRealOperatorZero camera sigma time ↔ sigma = 1/2 ∧
> IsNativeCarryRealOperatorResonance camera time`. O Primitivo real e o Genuine
> são duas roupas da mesma leitura, ligadas por um empacotamento aditivo
> injetivo que preserva os zeros. Green, TFVD, Bessel, Pitágoras,
> precompression, estado-fonte e contração são extensões possíveis, não
> obrigações necessárias para reabrir o confinamento já fechado.
