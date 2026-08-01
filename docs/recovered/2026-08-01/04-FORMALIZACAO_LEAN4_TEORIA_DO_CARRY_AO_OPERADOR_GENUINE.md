# Formalização Lean 4 da teoria do carry ao operador Genuine no limite

## 1. Fonte formal e convenções

Este texto expõe a sequência matemática certificada pelo código Lean 4 do repositório `thiagomassensini/primos`, tomando como superfície formal o agregador `CPFormal.lean` no commit

`975f709b620769e8659f9eda8543fc540fefb769`.

O objetivo é apresentar a matemática na ordem em que os objetos se sustentam:

$$
\boxed{
\text{carry}
\longrightarrow
\text{massa e amplitude crítica}
\longrightarrow
\sigma=\tfrac12
\longrightarrow
s(t)=\tfrac12+it
\longrightarrow
u_t
\longrightarrow
\text{Genuine}
\longrightarrow
\text{Green/TFVD}
\longrightarrow
\mathcal G_\infty
}
$$

Há duas ordens complementares no código:

1. a ordem de construção, na qual a carta Genuine ambiente é erguida a partir do bracket e depois especializada em $s(t)$;
2. a ordem espectral, na qual o carry fixa a amplitude, $t\in\mathbb R$ gira apenas a fase, e o Genuine é o readout canônico desse estado.

As duas ordens são identificadas pelos teoremas citados ao longo do texto.

### Hipóteses usuais

Salvo indicação local:

- $p,q\in\mathbb N$ são primos ímpares;
- $p\ne q$ é acrescentado quando se compara o defeito de duas câmeras;
- $M,L,N\in\mathbb N$ são cutoffs;
- $t,\sigma,\delta\in\mathbb R$;
- $s\in\mathbb C$;
- $\mathcal S=\{s\in\mathbb C:0<\Re(s)<1\}$ é `genuineCriticalStrip`;
- $\mathcal H_{-1}=\{s\in\mathbb C:-1<\Re(s)\}$ é `bracketHalfPlane`.

Nos tipos Lean, a primalidade aparece como `hp : Nat.Prime p`, a imparidade como `hpodd : Odd p` e a pertinência ao strip como `hs : s ∈ genuineCriticalStrip`.

Para abreviar os nomes:

- a geometria $Cp$ está em `CPFormal.Carry.Cp`;
- o Genuine finito está em `CPFormal.Genuine.Cp`;
- a camada analítica e espectral está em `CPFormal.Analytic.Cp`;
- a segunda diferença abstrata está em `CPFormal`.

## 2. Fundação combinatória: par simétrico e stencil

A célula mínima é um par simétrico

$$
P=(c,r),\qquad
\ell(P)=c-r,\qquad
r(P)=c+r.
$$

Ela é formalizada por `CPFormal.SymmetricPair`, com projeções `SymmetricPair.left` e `SymmetricPair.right`. A reflexão (P^*=(c,-r)) troca as pernas; isso é `SymmetricPair.reflected`, `reflected_left` e `reflected_right`. A recuperação do centro,

$$
\ell(P)+r(P)=2c,
$$

é `SymmetricPair.left_add_right`.

Sobre qualquer grupo comutativo aditivo, a segunda diferença centrada é

$$
\Delta_r^2 f(c)=f(c-r)-2f(c)+f(c+r),
$$

definida por `centeredSecondDifference`. Sua paridade no raio, linearidade e ação sobre zero são `centeredSecondDifference_neg_radius`, `centeredSecondDifference_add` e `centeredSecondDifference_zero`.

O bracket saturado até o raio (h) é

$$
\mathcal B_h f(c)=\sum_{r=1}^{h}\Delta_r^2 f(c),
$$

formalizado por `saturatedBracket`, com `saturatedBracket_add` e `saturatedBracket_zero`.

Esses objetos são a interface aditiva que reaparece nas câmeras (C2), (Cp), no Genuine e na forma de Green.

## 3. Carry (C2): centro, incidência e profundidade

Considere as pernas ímpares

$$
O=\{n\in\mathbb N:n\ge 3,\ n\text{ ímpar}\}.
$$

Para (n\in O), `CPFormal.Carry.C2.adjacentCenter n` escolhe o único vizinho divisível por (4):

$$
c_2(n)=
\begin{cases}
n-1,&n\equiv1\pmod4,\\
n+1,&n\equiv3\pmod4.
\end{cases}
$$

A dicotomia é `odd_mod_four`; as fórmulas locais são `adjacentCenter_of_mod_one` e `adjacentCenter_of_mod_three`. Os teoremas estruturais são:

$$
4\mid c_2(n),\qquad c_2(n)\ge4,
\qquad n=c_2(n)-1\ \text{ou}\ n=c_2(n)+1.
$$

Nomes Lean: `four_dvd_adjacentCenter`, `four_le_adjacentCenter` e `leg_of_adjacentCenter`. A unicidade é `adjacentCenter_unique`.

O tipo de incidência guarda um centro e uma de suas duas pernas:

$$
I_2=\{(c,n):c\ge4,\ 4\mid c,\ n=c-1\ \text{ou}\ n=c+1\}.
$$

As funções `incidenceOfOddLeg` e `oddLegOfIncidence` formam a equivalência

$$
O\simeq I_2,
$$

nomeada `oddLegEquivIncidence`.

A profundidade efetiva é definida antes da escolha do centro:

$$
d_2^{\mathrm{eff}}(n)
=\max\bigl(v_2(n-1),v_2(n+1)\bigr),
$$

por `CPFormal.Carry.C2.effectiveDepth`. O centro selecionado tem profundidade ao menos (2), por `two_le_centerDepth`, enquanto o outro vizinho tem profundidade (1), por `padicValNat_two_eq_one_of_mod_four_two`. A identificação fundamental é

$$
d_2^{\mathrm{eff}}(n)=v_2(c_2(n)),
$$

em `CPFormal.Carry.C2.effectiveDepth_eq_centerDepth`.

Assim, no ramo (C2), “profundidade vista pela perna” e “profundidade do centro incidente” são a mesma coordenada formal.

## 4. Carry (Cp): câmera balanceada e incidência global

Fixe um primo ímpar (p) e defina

$$
h_p=\frac{p-1}{2},
\qquad
A_p=\{-h_p,\ldots,-1,1,\ldots,h_p\}.
$$

Os nomes são `halfRange p` e `balancedOffsets p`. A caracterização

$$
a\in A_p
\iff
a\ne0\ \land\ -h_p\le a\le h_p
$$

é `mem_balancedOffsets_iff`; a exclusão do zero é `zero_not_mem_balancedOffsets`.

A imparidade fornece

$$
2h_p+1=p,
\qquad
|A_p|=p-1,
$$

por `two_mul_halfRange_add_one` e `card_balancedOffsets`.

### 4.1. Resíduo não nulo e offset canônico

O subtipo dos offsets balanceados é `BalancedOffset p`; o dos resíduos não nulos módulo (p) é `NonzeroResidue p`. Para (p) primo ímpar, a coerção módulo (p) dá a equivalência

$$
A_p\simeq (\mathbb Z/p\mathbb Z)\setminus\{0\},
$$

formalizada por `balancedOffsetEquivNonzeroResidue`. Suas duas direções explícitas são `residueOfBalanced` e `balancedOfResidue`.

Se

$$
N_p=\{n\in\mathbb Z:p\nmid n\}
$$

é o subtipo `Nonmultiple p`, então `offsetOfNonmultiple` fornece o representante balanceado canônico (a_p(n)). O centro associado é

$$
c_p(n)=n-a_p(n),
$$

definido por `centerOfNonmultiple`, e `dvd_centerOfNonmultiple` prova (p\mid c_p(n)).

### 4.2. Bijeção centro–perna

A incidência (Cp) é

$$
I_p=\{(c,a):p\mid c,\ a\in A_p\}.
$$

`incidenceOfNonmultiple` envia (n) a ((c_p(n),a_p(n))); `nonmultipleOfIncidence` envia ((c,a)) a (c+a). As identidades de reconstrução estão em `incidenceOfNonmultiple_leg` e `offsetOf_nonmultipleOfIncidence`.

O resultado global é

$$
N_p\simeq I_p,
$$

por `nonmultipleEquivIncidence`. Sua forma existencial, `existsUnique_incidence`, afirma

$$
\forall n\in N_p,\quad
\exists!\,(c,a)\in I_p\quad c+a=n.
$$

## 5. A única perna carregada e a profundidade efetiva (Cp)

Para cada offset candidato,

$$
d_p(n,a)=v_p(n-a)
$$

é `offsetDepth p n a`. A profundidade efetiva da câmera é

$$
d_p^{\mathrm{eff}}(n)=\max_{a\in A_p}d_p(n,a),
$$

definida por `effectiveDepth`; a profundidade central é

$$
d_p^{\mathrm{ctr}}(n)=v_p(c_p(n)),
$$

definida por `centerDepth`.

O teorema de unicidade da perna carregada é

$$
p\mid(n-a)\iff a=a_p(n),
$$

em `dvd_sub_iff_eq_offset`. Dele seguem:

- `offsetDepth_eq_zero_of_ne_offset`:
  $$
  a\ne a_p(n)\Longrightarrow d_p(n,a)=0;
  $$
- `offsetDepth_canonical`:
  $$
  d_p(n,a_p(n))=d_p^{\mathrm{ctr}}(n);
  $$
- `effectiveDepth_eq_centerDepth`:
  $$
  d_p^{\mathrm{eff}}(n)=d_p^{\mathrm{ctr}}(n).
  $$

`one_le_centerDepth` registra a positividade da profundidade quando o centro canônico é não nulo; `centerDepth_eq_zero_of_center_eq_zero` trata a convenção no centro zero.

Esta é a origem aritmética do índice vertical (k) usado em todas as amplitudes posteriores.

## 6. Reindexação ponderada e caixas alinhadas

Se (w:\mathbb N\to R) é um peso e (F:\mathbb Z\to R), a coordenada da perna é

$$
T_{\mathrm{leg}}(n)=w(d_p^{\mathrm{eff}}(n))F(n),
$$

`nonmultipleTerm`, enquanto a coordenada de incidência é

$$
T_{\mathrm{inc}}(c,a)=w(v_p(c))F(c+a),
$$

`incidenceTerm`.

A equivalência preserva o termo:

$$
T_{\mathrm{inc}}(\iota_p(n))=T_{\mathrm{leg}}(n),
$$

por `incidenceTerm_incidenceOfNonmultiple` e `incidenceTerm_nonmultipleEquivIncidence`.

Para toda caixa finita (S\subset N_p),

$$
\sum_{n\in S}T_{\mathrm{leg}}(n)
=
\sum_{x\in\iota_p(S)}T_{\mathrm{inc}}(x),
$$

em `weighted_reindex`.

Se uma caixa esperada (E\subset I_p) é escolhida, `weighted_reindex_with_boundary` conserva literalmente os termos extras e ausentes:

$$
\sum_{x\in\iota_p(S)}T(x)
=\sum_{x\in E}T(x)
+\sum_{x\in\iota_p(S)\setminus E}T(x)
-\sum_{x\in E\setminus\iota_p(S)}T(x).
$$

Os dois bordos são `extraIncidences` e `missingIncidences`. Em cobertura exata, `weighted_reindex_of_exact_cover` os elimina pela igualdade dos conjuntos.

### 6.1. Caixas (C2)

Os centros são (4(k+1)), (0\le k<M), com `leftIncidence k` e `rightIncidence k`. A enumeração literal das pernas é

$$
3,5,7,\ldots,4M+1.
$$

`alignedOddLegBox_eq_arithmeticOddLegBox`, `card_alignedOddLegBox` e `incidenceImage_alignedOddLegBox` provam a identificação, a cardinalidade (2M) e a cobertura exata. A soma final é `CPFormal.Carry.C2.weighted_reindex_alignedBox`.

### 6.2. Caixas (Cp)

Os centros são

$$
c_k=p(k+1),\qquad 0\le k<M,
$$

e cada centro recebe todos os (p-1) offsets. Os objetos são `alignedIncidence`, `incidenceIndexBox`, `alignedIncidenceBox` e `alignedNonmultipleBox`.

As cardinalidades

$$
|\operatorname{alignedIncidenceBox}(p,M)|
=|\operatorname{alignedNonmultipleBox}(p,M)|
=M(p-1)
$$

são `card_alignedIncidenceBox` e `card_alignedNonmultipleBox`. A igualdade de imagem é `incidenceImage_alignedNonmultipleBox`; a soma exata é `CPFormal.Carry.Cp.weighted_reindex_alignedBox`.

## 7. Da profundidade à massa e à amplitude crítica

Para uma profundidade de carry (k), o código define

$$
\mu_{p,k}=p^{-k},
\qquad
\alpha_{p,k}=p^{-k/2}.
$$

Os nomes Lean são `criticalMass p k` e `criticalAmplitude p k`. A identidade local fundamental é

$$
\boxed{\alpha_{p,k}^{,2}=\mu_{p,k}},
$$

provada por `criticalAmplitude_sq_eq_mass`; `criticalAmplitude_nonneg` dá a não negatividade.

Para uma abscissa real geral $\sigma$,

$$
\alpha_{p,k}(\sigma)=p^{-k\sigma},
\qquad
q_p(\sigma)=p^{-2\sigma},
\qquad
w_{p,k}(\sigma)=q_p(\sigma)^k.
$$

São `branchAmplitude`, `branchRatio` e `branchMassWeight`. O kernel prova

$$
\alpha_{p,k}(\sigma)^2=w_{p,k}(\sigma)
$$

em `branchAmplitude_sq_eq_massWeight`, além das especializações

$$
\alpha_{p,k}\!\left(\frac12\right)=\alpha_{p,k},
\qquad
w_{p,k}\!\left(\frac12\right)=\mu_{p,k},
$$

em `branchAmplitude_half` e `branchMassWeight_half`.

A profundidade aritmética já identificada transporta a massa:

$$
\mu_{p,d_p^{\mathrm{eff}}(n)}
=\mu_{p,d_p^{\mathrm{ctr}}(n)},
$$

por `criticalMass_effectiveDepth_eq_centerDepth`. Nas caixas alinhadas, `criticalMass_reindex_alignedBox` e `criticalAmplitude_sq_reindex_alignedBox` reindexam respectivamente a massa e o quadrado da amplitude.

Portanto, (p^{-k/2}) não é uma normalização adicionada depois: seu expoente (k) é a profundidade de carry já fixada pela incidência.

## 8. Saturação do ramo e seleção de σ = 1/2

A massa quadrática de todas as (p-1) pernas e de todas as profundidades positivas é

$$
\mathcal N_p(\sigma)^2
=(p-1)\sum_{k\ge1}p^{-2k\sigma},
$$

definida como `branchNormSq p sigma`.

Para $p$ primo e $\sigma>0$, `branchNormSq_eq_closed` dá, com $q=p^{-2\sigma}$,

$$
\mathcal N_p(\sigma)^2=(p-1)q(1-q)^{-1}.
$$

`branchRatio_half` prova (q_p(1/2)=p^{-1}), e `branchNormSq_half` prova

$$
\mathcal N_p\!\left(\frac12\right)^2=1.
$$

A recíproca exata é

$$
\boxed{
\mathcal N_p(\sigma)^2=1
\iff
\sigma=\frac12
},
$$

formalizada por `branchNormSq_eq_one_iff` sob `Nat.Prime p` e $0<\sigma$.

O deslocamento transversal e o defeito da norma são

$$
\delta(\sigma)=\sigma-\frac12,
\qquad
D_p(\sigma)=\mathcal N_p(\sigma)^2-1,
$$

definidos por `criticalDisplacement` e `branchDefect`. O teorema

`branchDefect_eq_zero_iff_criticalDisplacement_eq_zero`

identifica seus zeros:

$$
D_p(\sigma)=0\iff\delta(\sigma)=0.
$$

## 9. Tilt transversal: o mesmo locus crítico em coordenadas locais

Para um centro real (c), defina

$$
\Theta_{p,\delta}(c)
=\sum_{a\in A_p}(c+a)^{-\delta}-(p-1)c^{-\delta}.
$$

Este é `cpTilt p delta center`; a versão parametrizada pela abscissa é

$$
\Theta_{p,\sigma-1/2}(c),
$$

`cpTiltAtSigma p sigma center`.

O pareamento (a\leftrightarrow-a) fornece

$$
\Theta_{p,\delta}(c)
=\frac12\sum_{a\in A_p}
\Big((c-a)^{-\delta}+(c+a)^{-\delta}-2c^{-\delta}\Big),
$$

por `cpTilt_eq_half_sum_pair`.

Para (c>h_p), o sinal de cada segunda diferença é controlado pela convexidade ou concavidade estrita. Os teoremas globais são `cpTilt_pos_of_delta_pos` e `cpTilt_neg_of_neg_one_lt_delta`.

Sob

$$
p\text{ primo ímpar},\qquad
0<\sigma,\qquad
h_p<c,
$$

`cpTiltAtSigma_eq_zero_iff_half` prova

$$
\Theta_{p,\sigma-1/2}(c)=0
\iff
\sigma=\frac12.
$$

Finalmente,

`branchDefect_eq_zero_iff_cpTiltAtSigma_eq_zero_of_admissible_center`

identifica a saturação quadrática e o tilt no mesmo locus:

$$
D_p(\sigma)=0
\iff
\Theta_{p,\sigma-1/2}(c)=0.
$$

## 10. Bracket (Cp) e a lei Genuine finita

A soma das pernas e o bracket da câmera são

$$
L_p[f](c)=\sum_{a\in A_p}f(c+a),
\qquad
B_p[f](c)=L_p[f](c)-(p-1)f(c).
$$

No Lean, são `CPFormal.Genuine.Cp.legSum` e `CPFormal.Genuine.Cp.bracket`.

O pareamento dos offsets positivos e negativos é `legSum_eq_pairSum`. Como (p-1=2h_p), `bracket_eq_saturatedBracket` identifica o bracket com a soma das segundas diferenças:

$$
\boxed{
B_p[f](c)
=\sum_{r=1}^{h_p}\Delta_r^2f(c)
=\mathcal B_{h_p}f(c)
}.
$$

A camada abstrata `CPFormal.Genuine.FiniteCancellation` separa três canais em um conjunto finito de centros (C):

$$
\begin{aligned}
D_C&=\sum_{c\in C}w(c)L(c),\\
Q_C&=\sum_{c\in C}w(c)\bigl(L(c)-\kappa(c)V(c)\bigr),\\
S_C&=\sum_{c\in C}w(c)\kappa(c)V(c).
\end{aligned}
$$

São `directChannel`, `bracketChannel` e `survivingCenterChannel`. A identidade local `localCancellation` e a soma `finiteCancellation` dão

$$
D_C-Q_C=S_C.
$$

Na câmera (Cp), (kappa=p-1). Os nomes especializados são `CPFormal.Genuine.Cp.finiteDirect`, `finiteBrackets` e `finiteCenters`, com

$$
L_p[f](c)-B_p[f](c)=(p-1)f(c)
$$

em `local_genuine_cancellation`, e

$$
\operatorname{finiteDirect}
-\operatorname{finiteBrackets}
=\operatorname{finiteCenters}
$$

em `finite_genuine_cancellation`.

O ramo (C2) possui a especialização paralela com `CPFormal.Genuine.C2.legSum`, `bracket`, `local_genuine_cancellation` e `finite_genuine_cancellation`, usando multiplicidade (2).

## 11. Carta Genuine finita e correção vertical

Inclua agora o centro no conjunto de offsets:

$$
A_p^0=\{-h_p,\ldots,0,\ldots,h_p\},
$$

`fullOffsets`. O bloco completo é

$$
U_p[f](c)=\sum_{a\in A_p^0}f(c+a),
$$

`centerBlock`. Os teoremas `fullOffsets_erase_zero`, `zero_mem_fullOffsets` e `card_fullOffsets` controlam a decomposição e a cardinalidade. Em particular,

$$
U_p[f](c)=L_p[f](c)+f(c)
$$

por `centerBlock_eq_legSum_add_center`, e

$$
\boxed{B_p[f](c)=U_p[f](c)-pf(c)}
$$

por `bracket_eq_centerBlock_sub_p_mul_center`.

Defina a semente, os centros alinhados e a carta finita:

$$
S_p[f]=\sum_{n=1}^{h_p}f(n),
\qquad
c_k=p(k+1),
$$

$$
\mathcal C_{p,M}[f]
=S_p[f]+\sum_{k=0}^{M-1}B_p[f](c_k).
$$

Os nomes são `seedSum`, `alignedCenter` e `finiteChart`.

O prefixo de blocos e a correção vertical são

$$
P_{p,M}[f]
=S_p[f]+\sum_{k=0}^{M-1}U_p[f](c_k),
$$

$$
V_{p,M}[f]
=\sum_{k=0}^{M-1}p,f(c_k).
$$

São `blockPrefix` e `verticalCorrection`. A identidade

$$
\boxed{
\mathcal C_{p,M}[f]=P_{p,M}[f]-V_{p,M}[f]
}
$$

é `finiteChart_eq_blockPrefix_sub_verticalCorrection`.

Os blocos ladrilham o intervalo positivo:

$$
P_{p,M}[f]
=\sum_{n=1}^{pM+h_p}f(n),
$$

por `blockPrefix_eq_positiveIntervalSum`. Portanto,

$$
\mathcal C_{p,M}[f]
=\sum_{n=1}^{pM+h_p}f(n)
-p\sum_{k=0}^{M-1}f\bigl(p(k+1)\bigr),
$$

em `finiteChart_eq_positiveIntervalSum_sub_p_mul_centerSum`.

## 12. Monômio complexo, fatoração finita e ganho da segunda diferença

Para (n>0), defina

$$
d_s(n)=n^{-s},
$$

como `dirichletTerm s n`. O prefixo positivo é

$$
P_M(s)=\sum_{n=1}^{M}n^{-s},
$$

`positiveDirichletPrefix s M`.

Nos centros alinhados,

$$
d_s(p(k+1))=d_s(p)d_s(k+1)
$$

por `dirichletTerm_alignedCenter`, e

$$
p,d_s(p)=p^{1-s}
$$

por `prime_mul_dirichletTerm_eq_cpow_one_sub`. A carta finita torna-se

$$
\boxed{
\mathcal C_{p,M}(s)
=P_{pM+h_p}(s)-p^{1-s}P_M(s)
},
$$

em `finiteChart_dirichlet_eq_two_prefixes`.

No eixo real positivo, escreva (f_s(x)=x^{-s}). Sua segunda derivada é

$$
f_s''(x)=s(s+1)x^{-s-2}.
$$

Os objetos são `realDirichletPower` e `realDirichletPowerDeriv2`. O lema abstrato `norm_centeredSecondDifference_le` e sua especialização `norm_realDirichletPower_centeredSecondDifference_le` mostram que uma segunda diferença compra duas potências de decaimento.

No centro (p(k+1)), o par de raio (r) é

$$
\Delta_{p,r,k}(s)
=f_s(p(k+1)-r)-2f_s(p(k+1))+f_s(p(k+1)+r),
$$

`realCpPairBracket`. A soma dos raios é

$$
\Delta^{\mathrm{sat}}_{p,k}(s)
=\sum_{r=1}^{h_p}\Delta_{p,r,k}(s),
$$

`realCpSaturatedBracket`.

As identificações exatas são:

- `realCpPairBracket_eq_centeredSecondDifference`;
- `realCpSaturatedBracket_eq_saturatedBracket`;
- `realCpSaturatedBracket_eq_genuineBracket`.

Para (p) primo e (-1<\Re(s)),

$$
\sum_{k\ge0}\left\|\Delta^{\mathrm{sat}}_{p,k}(s)\right\|<\infty
$$

por `summable_norm_realCpSaturatedBracket`; a série complexa é `summable_realCpSaturatedBracket`.

## 13. Carta bracketada infinita

A carta bracketada é

$$
\mathcal B_p(s)
=S_p(s)+\sum_{k\ge0}\Delta^{\mathrm{sat}}_{p,k}(s),
$$

definida como `bracketedDirichletChart p s`. Seu corte é

$$
\mathcal B_{p,M}(s)
=S_p(s)+\sum_{k=0}^{M-1}\Delta^{\mathrm{sat}}_{p,k}(s),
$$

`finiteBracketedDirichletChart p M s`.

`finiteBracketedDirichletChart_eq_finiteChart` identifica a soma analítica com a carta aritmética:

$$
\mathcal B_{p,M}(s)=\mathcal C_{p,M}[d_s].
$$

Para (-1<\Re(s)),

$$
\mathcal B_{p,M}(s)\longrightarrow\mathcal B_p(s)
$$

por `finiteBracketedDirichletChart_tendsto`. A mesma convergência, escrita a partir da carta aritmética, é `finiteChart_dirichlet_tendsto_bracketedDirichletChart`.

A regularidade em $\mathcal H_{-1}$ é certificada por:

- `differentiableOn_bracketedDirichletChart`;
- `analyticOnNhd_bracketedDirichletChart`;
- `bracketedDirichletChart_unique_analytic_continuation`.

## 14. Fator de câmera, quociente e Genuine canônico

O fator da câmera (p) é

$$
F_p(s)=1-p^{1-s},
$$

definido como `cpChartFactor p s`. Para $p$ primo e $s\in\mathcal S$,

$$
F_p(s)\ne0
$$

por `cpChartFactor_ne_zero_on_genuineCriticalStrip`.

O quociente normalizado é

$$
G_p(s)=\frac{\mathcal B_p(s)}{F_p(s)},
$$

`cpGenuineQuotient p s`. No strip,

$$
\mathcal B_p(s)=F_p(s)G_p(s)
$$

por `bracketedDirichletChart_eq_factor_mul_cpGenuineQuotient`, e

$$
\mathcal B_p(s)=0\iff G_p(s)=0
$$

por `bracketedDirichletChart_zero_iff_cpGenuineQuotient_zero`. A analiticidade do quociente é `analyticOnNhd_cpGenuineQuotient_genuineCriticalStrip`.

### 14.1. Compatibilidade entre câmeras primas

O produto cruzado é

$$
X_{p,q}(s)=F_q(s)\mathcal B_p(s),
$$

`crossNormalizedChart p q s`. Para $p,q$ primos ímpares,

$$
F_q(s)\mathcal B_p(s)=F_p(s)\mathcal B_q(s)
$$

em todo $\mathcal H_{-1}$, por `crossNormalizedChart_eq_swap`.

No strip, o cancelamento dos fatores dá

$$
G_p(s)=G_q(s),
$$

por `cpGenuineQuotient_eq_cpGenuineQuotient`.

O representante canônico é

$$
G(s)=G_3(s),
$$

definido como `genuineContinuation s`. Para toda câmera prima ímpar:

$$
G_p(s)=G(s),
$$

$$
\boxed{
\mathcal B_p(s)=F_p(s)G(s)
},
$$

$$
\mathcal B_p(s)=0\iff G(s)=0.
$$

Os nomes Lean são `cpGenuineQuotient_eq_genuineContinuation`, `bracketedDirichletChart_eq_cpChartFactor_mul_genuineContinuation` e `bracketedDirichletChart_zero_iff_genuineContinuation_zero`.

### 14.2. Forma integral em segundas diferenças

`bracketedDirichletChart_eq_centeredSecondDifferenceSeries` reescreve a carta diretamente como série de stencils centrados. Na câmera (3), `bracketedDirichletChart_three_eq_one_add_centeredSecondDifferenceSeries` isola a semente (1).

`cpGenuineQuotient_eq_centeredSecondDifferenceSeries` e `genuineContinuation_eq_centeredSecondDifferenceSeries` transportam essa descrição ao quociente e ao Genuine canônico. A caracterização de zero correspondente é `genuineContinuation_zero_iff_centeredSecondDifferenceSeries_eq_neg_one`.

## 15. A meia abscissa deixa um parâmetro real de fase

A saturação do ramo fixou $\sigma=1/2$. O grau de liberdade restante é

$$
\boxed{
s(t)=\frac12+it,
\qquad t\in\mathbb R
}.
$$

No Lean, esta é a definição `criticalLineParameter t`. Os teoremas

`criticalLineParameter_re` e `criticalLineParameter_im`

provam

$$
\Re s(t)=\frac12,
\qquad
\Im s(t)=t.
$$

Consequentemente,

$$
\delta(\Re s(t))=0.
$$

`criticalLineParameter_mem_genuineCriticalStrip` prova (s(t)\in\mathcal S), e `reflectedParameter_criticalLineParameter` prova que a reflexão

$$
s^\#=1-\overline s
$$

fixa (s(t)) ponto a ponto.

## 16. Estado real-espectral

O estado no vértice positivo (n+1) é

$$
u_t(n)=(n+1)^{-s(t)}
=(n+1)^{-1/2}e^{-it\log(n+1)}.
$$

Ele é `realSpectralState t n`, definido literalmente por

`positiveDirichletValue (criticalLineParameter t) n`.

O teorema `norm_realSpectralState` certifica

$$
\boxed{
\|u_t(n)\|=(n+1)^{-1/2}
}.
$$

Portanto, a profundidade de carry determina a lei de amplitude, enquanto (t) atua somente na fase.

### 16.1. Câmeras na órbita real

O fator especializado é

$$
F_p(t)=F_p(s(t)),
$$

`realSpectralChartFactor p t`, com `realSpectralChartFactor_ne_zero`.

As câmeras são:

$$
\mathcal B_{p,M}(t)=\mathcal B_{p,M}(s(t)),
$$

`finiteRealSpectralChart p M t`;

$$
C_{p,M}(t)=\frac{\mathcal B_{p,M}(t)}{F_p(t)},
$$

`finiteRealSpectralCamera p M t`;

$$
C_p(t)=G_p(s(t)),
$$

`realSpectralCamera p t`;

$$
G_{\mathbb R}(t)=G(s(t)),
$$

`realSpectralGenuine t`.

Para toda câmera prima ímpar,

$$
C_p(t)=G_{\mathbb R}(t)
$$

por `realSpectralCamera_eq_realSpectralGenuine`; a independência da câmera é `realSpectralCamera_prime_independent`.

A fatoração real é

$$
\mathcal B_p(s(t))=F_p(t)G_{\mathbb R}(t),
$$

em `bracketedDirichletChart_criticalLine_eq_factor_mul_realSpectralGenuine`, e

$$
\mathcal B_p(s(t))=0
\iff
G_{\mathbb R}(t)=0
$$

em `bracketedDirichletChart_criticalLine_zero_iff_realSpectralGenuine_zero`.

O predicado

$$
\operatorname{Res}(t)
\iff G_{\mathbb R}(t)=0
$$

é `IsRealSpectralResonance t`. A equivalência com o zero de qualquer carta prima ímpar é `isRealSpectralResonance_iff_chart_zero`.

## 17. Gradientes, autovalor de bloco e reflexão

Nos vértices positivos, defina

$$
v_s(n)=(n+1)^{-s}
$$

como `positiveDirichletValue s n`, e o gradiente

$$
g_s(n)=v_s(n+1)-v_s(n)
$$

como `positiveDirichletGradient s n`.

O bloco de (p) gradientes consecutivos é `cpBlockGradient p s n`. A telescopagem e a multiplicatividade dão a lei própria

$$
\boxed{
\operatorname{Block}_{p,s}(n)=p^{-s}g_s(n)
},
$$

em `cpBlockGradient_eq_eigenvalue_mul`.

A reflexão do parâmetro é

$$
s^\#=1-\overline s,
$$

`reflectedParameter s`. O pareamento finito refletido é

$$
E_M(s)
=\sum_{n=0}^{M-1}\overline{g_s(n)},g_{s^\#}(n),
$$

definido como `finiteReflectedGradientPairing M s`.

## 18. Green finito e normalização radial

O Wronskiano dos blocos é `finiteCpGreenFlux`. A fatoração

$$
W_{p,M}(s)
=\bigl(\overline{p^{-s}}-p^{-s^\#}\bigr)E_M(s)
$$

é `finiteCpGreenFlux_eq_eigenvalueDifference_mul_pairing`.

A forma discreta de Stokes é `finiteGreenBulk_eq_boundary`; sua especialização refletida é `finiteReflectedStokesFlux_eq_endpoints`. O endpoint externo possui a fórmula

$$
\overline{v_s(M)}v_{s^\#}(M)=\frac1{M+1},
$$

por `finiteReflectedOuterEndpoint_eq_inv`, e converge a zero por `finiteReflectedOuterEndpoint_tendsto_zero`.

`FiniteComplexGreenCertificate` empacota coeficiente, energia, bulk, corrente e endpoints; a realização concreta é `finiteCpGreenCertificate`, com identidade expandida `finiteCpGreen_identity_explicit`.

### 18.1. Retirada da fase

Escreva

$$
\delta=\Re(s)-\frac12.
$$

O normalizador

$$
N_p(s)=p^{1/2+i\Im(s)}
$$

é `cpPhaseNormalizer p s`. Os teoremas `cpPhaseNormalizer_mul_eigenvalue`, `phaseNormalizedCpBlockGradient_eq_radial_mul` e `phaseNormalizedCpBlockGradient_reflected_eq_radial_mul` dão

$$
N_p(s)p^{-s}=p^{-\delta},
\qquad
N_p(s^\#)p^{-s^\#}=p^{\delta}.
$$

O detector radial orientado é

$$
R_p(\delta)=p^\delta-p^{-\delta},
$$

`cpRadialDifference p delta`. Seu cofator é

$$
C_p(\delta)=
\begin{cases}
\log p,&\delta=0,\\[1mm]
R_p(\delta)/(2\delta),&\delta\ne0,
\end{cases}
$$

`cpRadialCofactor p delta`.

Para (p) primo,

$$
R_p(\delta)=2\delta C_p(\delta),
\qquad
C_p(\delta)>0,
\qquad
R_p(\delta)=0\iff\delta=0.
$$

Os nomes são `cpRadialDifference_eq_two_mul_delta_mul_cofactor`, `cpRadialCofactor_pos` e `cpRadialDifference_eq_zero_iff`.

A energia radial finita é

$$
\mathcal E_{p,M}(s)=C_p(\delta)\Re E_M(s),
$$

`finiteRadialGreenEnergy p M s`. Para $M>0$, $p$ primo e $s\in\mathcal S$,

$$
\mathcal E_{p,M}(s)>0
$$

por `finiteRadialGreenEnergy_pos`. A positividade termo a termo e a da soma são `finiteReflectedGradientEdge_re_pos` e `finiteReflectedGradientPairing_re_pos`.

O fluxo orientado satisfaz

$$
\Phi^{\mathrm{raw}}_{p,M}(s)
=2\delta\,\mathcal E_{p,M}(s)
+\partial^{\mathrm{raw}}_{M}(s),
$$

em `finiteSignedCpGreen_identity`.

## 19. Acoplamento do bordo Green à carta Genuine

Na câmera canônica (p=3), a semente vale (1). O traço de brackets `canonicalBracketTrace M s` satisfaz

$$
\mathcal B_{3,M}(s)=1+\operatorname{Trace}_M(s),
$$

por `bracketedDirichletChart_three_eq_one_add_trace` e, na interface angular, por `finiteBracketedDirichletChart_three_eq_inner_add_trace`.

O bordo bracketado é

$$
\partial_M^{\mathrm{br}}(s)
=\partial_M^{\mathrm{raw}}(s)-\operatorname{Trace}_M(s),
$$

`finiteBracketCoupledBoundary M s`. A identidade de cutoff é

$$
\boxed{
\partial_M^{\mathrm{br}}(s)
=\operatorname{outer}_M(s)-\mathcal B_{3,M}(s)
},
$$

em `finiteBracketCoupledBoundary_eq_outer_sub_finiteChart`.

Se $s\in\mathcal S$ e $G(s)=0$, então

$$
\partial_M^{\mathrm{br}}(s)\longrightarrow0,
\qquad
\Re\partial_M^{\mathrm{br}}(s)\longrightarrow0,
$$

por `finiteBracketCoupledBoundary_tendsto_zero_of_genuine_zero` e `finiteBracketCoupledSignedBoundary_tendsto_zero_of_genuine_zero`.

O fluxo real acoplado é

$$
\boxed{
\Phi_{p,M}(s)
=2\delta\,\mathcal E_{p,M}(s)
+\partial_{M,\mathbb R}^{\mathrm{br}}(s)
},
$$

em `finiteBracketCoupledCpGreen_identity`. A forma equivalente é

$$
\Phi_{p,M}(s)
=R_p(\delta)\Re E_M(s)
+\partial_{M,\mathbb R}^{\mathrm{br}}(s),
$$

por `finiteBracketCoupledCpGreenFlux_eq_radialDifference_mul_pairing`.

Sob $p$ primo, $s\in\mathcal S$ e $G(s)=0$, o teorema

`coupledFlux_tendsto_zero_iff_criticalDisplacement_eq_zero`

identifica

$$
\Phi_{p,M}(s)\longrightarrow0
\iff
\delta=0.
$$

## 20. Intertwiner Genuine–Green

A relação entre o bloco de gradientes e o bracket não é apenas assintótica. Para uma função (f), sejam:

- `cpAlignedCenterGradient`: diferença de (f) entre centros (Cp) consecutivos;
- `cpCenterBlockGradient`: diferença dos blocos completos;
- `cpGenuineBracketGradient`: diferença dos brackets;
- `cpGenuineResolvedGradient`: bloco menos bracket.

`cpGenuineResolvedGradient_eq_p_mul_alignedCenterGradient` prova

$$
\operatorname{ResolvedGradient}_{p,f}(n)
=p\bigl(f(c_{n+1})-f(c_n)\bigr).
$$

Para (f=d_s), `cpBlockGradient_eq_alignedCenterGradient` e `cpGenuineResolvedGradient_dirichlet_eq_p_mul_cpBlockGradient` identificam esse residual com (p) vezes o bloco Green.

A versão normalizada é `cpGenuineGreenGradient_eq_cpBlockGradient`. Nos fluxos finitos:

$$
\operatorname{finiteGenuineResolvedCpGreenFlux}
=p\,\operatorname{finiteCpGreenFlux}
$$

por `finiteGenuineResolvedCpGreenFlux_eq_p_mul_finiteCpGreenFlux`, enquanto

$$
\operatorname{finiteGenuineCpGreenFlux}
=\operatorname{finiteCpGreenFlux}
$$

por `finiteGenuineCpGreenFlux_eq_finiteCpGreenFlux`.

Após a normalização de fase, `finiteOrientedGenuineCpGreenFlux_eq_finiteOrientedCpGreenFlux` mantém a igualdade. A interface com a TFVD diagonal é

$$
\operatorname{finiteOrientedGenuineCpGreenFlux}
=\operatorname{finiteTfvdCpGreenDiagonal},
$$

em `finiteOrientedGenuineCpGreenFlux_eq_tfvdDiagonal`.

## 21. Porta angular e TFVD finita

Na câmera canônica, o bloco angular usa três gradientes consecutivos. `canonicalAngularGradientBlock` e `finiteCanonicalAngularTrace` definem o bloco e seu traço. A telescopagem é

$$
\mathcal B_{3,M}(s)
=\operatorname{AngularTrace}_M(s)+v_s(3M),
$$

por `finiteBracketedDirichletChart_three_eq_angularTrace_add_outer`.

Para $\Re(s)>0$, `canonicalAngularOuterValue_tendsto_zero` e `finiteCanonicalAngularTrace_tendsto` dão

$$
\operatorname{AngularTrace}_M(s)\longrightarrow\mathcal B_3(s).
$$

Em um zero Genuine no strip, `finiteCanonicalAngularTrace_tendsto_zero_of_genuine_zero` especializa esse limite a zero.

### 21.1. Coordenadas da válvula

Fixe escalas não nulas (kappa,omega). Para duas arestas (x_L,x_R), a codificação é

$$
\operatorname{through}
=-\frac{x_L+x_R}{\kappa},
\qquad
\operatorname{bracket}
=\omega\frac{x_R-x_L}{\kappa}.
$$

O tipo é `TfvdCoordinate`; a codificação e o retorno são `tfvdEncode` e `tfvdDecode`. A inversão exata é

$$
\operatorname{decode}(\operatorname{encode}(x_L,x_R))=(x_L,x_R),
$$

por `tfvdDecode_encode`.

O readout angular

$$
\frac{3\kappa}{2}\operatorname{through}
-\frac{\kappa}{2\omega}\operatorname{bracket}
=-(x_L+2x_R)
$$

é `tfvdAngularReadout`, com `tfvdAngularReadout_encode`.

As coordenadas canônicas do campo e do log-jet são `canonicalAngularTfvdCoordinate` e `canonicalLogJetTfvdCoordinate`. Os teoremas `finiteTfvdAngularReadout_canonicalAngularPort` e `finiteTfvdAngularReadout_canonicalLogJetPort` recuperam as portas finitas correspondentes.

### 21.2. Diagonal e síntese escalar

`finitePortWedgeEntry` define a entrada ((m,n)) do Wronskiano. A soma completa é `finiteFullPortWronskian`; suas parcelas são `finiteDiagonalPortWronskian` e `finiteOffDiagonalPortWronskian`.

A decomposição exata é

$$
W_{\mathrm{scalar}}
=W_{\mathrm{diag}}+W_{\mathrm{off}},
$$

por `finiteScalarPortWronskian_eq_diagonal_add_offDiagonal`.

O pareamento TFVD local é `tfvdReflectedGreenWedge`. Em coordenadas codificadas, `tfvdReflectedGreenWedge_encode` o reduz ao wedge das arestas. A realização Green é `canonicalCpGreenTfvdCoordinate`, e

$$
\operatorname{finiteTfvdCpGreenDiagonal}(p,M,s)
=\operatorname{finiteOrientedCpGreenFlux}(p,M,s)
$$

por `finiteTfvdCpGreenDiagonal_eq_finiteOrientedCpGreenFlux`.

## 22. TFVD enriquecida e proveniência das três arestas

Um bloco angular possui três arestas. O tipo

`EnrichedAngularTfvdCoordinate`

guarda a coordenada visível e a terceira aresta em `dormantEdge`. `enrichedAngularTfvdEncode` e `enrichedAngularTfvdDecode` formam a inversão `enrichedAngularTfvdDecode_encode`.

O trio recuperado é `TfvdThreeEdges`; a passagem ao portador Green é `enrichedAngularTfvdToCpGreenTriple`. A identificação bloco a bloco é

`enrichedAngularTfvdToCpGreenTriple_eq_canonical`.

O wedge refletido entre a porta angular e seu log-jet é `enrichedTfvdReflectedLogJetWedge`. Em coordenadas canônicas, `canonicalEnrichedTfvdReflectedLogJetWedgeTriple_eq_canonical` produz o trio de wedges.

Cada aresta satisfaz a identidade

$$
W^{\log}_{n}(s)
=W^{G}_{n}(s)+D^{\log-G}_{n}(s),
$$

por `canonicalReflectedLogJetEdgeWedge_eq_green_add_defect`. A versão tripla é `canonicalReflectedLogJetWedgeTriple_eq_green_add_defect`.

### 22.1. Comutador log-jet

O campo log-ponderado é `natLogDirichletTerm`. O bloco logarítmico satisfaz uma regra de produto discreta:

$$
\operatorname{cpLogBlockGradient}
=p^{-s}\operatorname{logJetGradient}
+\log(p)p^{-s}g_s,
$$

em `cpLogBlockGradient_eq_eigenvalue_mul_logJet_add_logScale`.

Logo o comutador é colinear com o gradiente:

$$
[B_p,\log](s,n)=\log(p)p^{-s}g_s(n),
$$

por `cpLogJetCommutator_eq_logScale_mul_gradient`.

No wedge refletido,

$$
W^{\mathrm{comm}}_n(s)=-\log(p)W^G_n(s),
$$

em `canonicalReflectedCpLogJetCommutatorWedge_eq_neg_log_mul_green`. O defeito se decompõe como

$$
D^{\log-G}_n
=W^{\mathrm{comm}}_n+R^{\log}_n,
$$

por `logJetGreenEdgeDefect_eq_commutatorWedge_add_residual`.

### 22.2. Soma por blocos e série residual

`sum_range_forwardDifference_mul_eq_cutoff_add_bulk` é a soma por partes finita que separa cutoff móvel e bulk cruzado. Aplicada ao canal residual:

$$
\operatorname{finiteResidualTrace}
=\operatorname{movingCutoff}
+\operatorname{crossBulk}
+\operatorname{GreenFlux},
$$

em `finiteCanonicalLogJetCommutatorResidualTrace_eq_cutoff_add_bulk_add_green`.

Os controles de norma são `norm_reflectedLogJetVertexFlux_le_two_mul_rpow_neg_two` e `summable_norm_reflectedLogJetVertexFlux`. A série limite é `reflectedLogJetVertexFluxSeries`; os cutoffs convergem por `finiteReflectedLogJetVertexFlux_tendsto_series` e `reflectedLogJetMovingCutoff_tendsto_zero`.

A reflexão é transportada por `reflectedLogJetVertexFluxSeries_reflectedParameter`. Quando $\Re(s)=1/2$, `reflectedLogJetVertexFluxSeries_re_eq_zero_of_re_eq_half` identifica a parte real nula. Os traços completos são reunidos em `criticalLine_completeTraces_tendsto`.

Na parametrização (s(t)), as fórmulas locais são abertas em um leque de fases. Com

$$
\ell_n=\log(n+2)-\log(n+1)>0
$$

e

$$
A_n=\exp\!\left[-\frac{\log(n+1)+\log(n+2)}2\right]>0,
$$

`positiveRealLogGap` e `criticalPhaseAmplitude`, o fluxo é

$$
-2\ell_nA_n\sin(t\ell_n)i.
$$

Os nomes são `reflectedDirichletVertexCrossFlux_criticalLine_eq_sine`, `reflectedLogJetVertexFlux_criticalLine_eq_sine` e `reflectedLogJetVertexFluxSeries_criticalLine_eq_sineSeries`.

## 23. Colagem finita Genuine–TFVD–Green

Um cutoff de (M) blocos angulares corresponde a (3M) arestas Green. A colagem enriquecida é `enrichedAngularTfvdCoordinateToCpGreenTriple`, com as identidades `enrichedAngularTfvdCoordinateToCpGreenTriple_encode` e `enrichedAngularTfvdCoordinateToCpGreenTriple_eq_canonical`.

O bordo angular bracketado é `finiteCanonicalAngularBracketCoupledBoundary`, com

$$
\partial^{\mathrm{ang}}_M(s)
=\operatorname{outer}_{3M}(s)-\mathcal B_{3,M}(s)
$$

por `finiteCanonicalAngularBracketCoupledBoundary_eq_outer_sub_finiteChart`.

O ledger enriquecido é reunido em

`finiteCanonicalAngularBracketCoupledGenuineGreenFlux_eq_enrichedLedger`.

Sua forma radial é

`finiteCanonicalAngularBracketCoupledGenuineGreenFlux_eq_radialDifference_mul_pairing`.

`criticalDisplacement_eq_zero_of_alignedGenuineGreenFlux_tendsto_zero` e `alignedGenuineGreenFlux_tendsto_zero_of_criticalDisplacement` dão as duas direções entre fechamento do fluxo e $\delta=0$, nas hipóteses explícitas de primalidade, strip e zero Genuine. A equivalência do ledger é `enrichedLedger_tendsto_zero_iff_re_eq_half_of_genuine_zero`.

### 23.1. Porta semeada e forma de bordo `same-s`

`SeededEnrichedTfvdPort` coloca a semente (1) no mesmo portador dos blocos enriquecidos. `finiteSeededEnrichedTfvdGenuineReadout_canonical` identifica seu readout com a carta finita; `finiteSeededEnrichedTfvdGenuineReadout_tendsto_zero_of_genuine_zero` fornece o limite em um zero Genuine.

A forma de bordo `same-s` é `finiteCanonicalSeededTfvdSameSBoundaryForm`. O fluxo, o endpoint móvel e o defeito de proveniência são, respectivamente:

- `finiteCanonicalTfvdCoupledGenuineGreenFlux`;
- `finiteCanonicalSeededTfvdGreenMovingEndpoint`;
- `finiteCanonicalTfvdSameSGreenProvenanceDefect`.

A identidade finita exata é

$$
\boxed{
\operatorname{BoundaryForm}
=\operatorname{CoupledGreenFlux}
+\operatorname{MovingEndpoint}
+\operatorname{ProvenanceDefect}
},
$$

em `finiteCanonicalSeededTfvdGreen_identity`. A parte real é `finiteCanonicalSeededTfvdGreen_signed_identity`; o endpoint converge a zero por `finiteCanonicalSeededTfvdGreenMovingEndpoint_tendsto_zero_of_genuine_zero`.

### 23.2. Regra de produto tilt–carrier e leitura TFVD

A fatoração local do campo é

$$
x^{-s}=x^{-1/2-i\Im(s)}x^{-\delta}.
$$

Os fatores são `criticalLineDirichletCarrier` e `complexTransversePowerProfile`. A identidade é `realDirichletPower_eq_criticalLineCarrier_mul_transverse`.

`centeredSecondDifference_mul` fornece a regra de Leibniz discreta para uma segunda diferença de produto. Aplicada à fatoração acima,

$$
\Delta^2(\text{carrier crítico}\times\text{perfil transversal})
=\text{tilt ponderado}
+\text{curvatura do carrier}
+\text{dois canais cruzados}.
$$

O nome local é `centeredSecondDifference_localDirichletProfile_eq_weightedTilt_add_carrier`; no bloco canônico (p=3), a soma é

`realCpSaturatedBracket_three_eq_weightedTilt_add_carrierRemainder`.

No cutoff,

$$
\operatorname{BracketTrace}_M
=\operatorname{WeightedTiltTrace}_M
+\operatorname{CarrierRemainderTrace}_M
$$

por `finiteCanonicalBracketTrace_eq_weightedTilt_add_carrierRemainder`.

A leitura linear independente das três arestas é `enrichedTfvdGenuineBracketReadout`. Sua identificação com o bracket canônico é `enrichedTfvdGenuineBracketReadout_canonical`; a decomposição em tilt e remainder é `enrichedTfvdGenuineBracketReadout_canonical_eq_weightedTilt_add_carrierRemainder`.

No cutoff, `finiteEnrichedTfvdGenuineBracketReadout_canonical_eq_weightedTilt_add_carrierRemainder` transporta a identidade bloco a bloco, e `finiteEnrichedTfvdGenuineBracketReadout_tendsto_neg_one_of_genuine_zero` fixa o limite da leitura não semeada em um zero Genuine.

## 24. TFVD vertical vestida pela amplitude do carry

Na fibra vertical, a razão canônica entre amplitudes consecutivas é

$$
q_p=p^{-1/2},
$$

definida como `primeCarryAmplitudeRatio p`. Para $p\ge2$, `primeCarryAmplitudeRatio_lt_one` prova $0\le q_p<1$.

O núcleo causal do Green vestido é

$$
K_q(r)=r q^r,
$$

`carryWeightedVerticalGreenKernel q r`. Sua somabilidade é `carryWeightedVerticalGreenKernel_summable`; a especialização (r p^{-r/2}) é `primeCarryWeightedVerticalGreenKernel`.

Uma família de shifts contrativos é `CarryVerticalShiftFamily H`. O operador

$$
G_q=\sum_{r\ge0}K_q(r)S_r
$$

é `carryWeightedVerticalGreen`; sua convergência e cota de norma são `carryWeightedVerticalGreenTerm_summable` e `carryWeightedVerticalGreen_norm_le_kernelMass`.

No Hilbert

$$
\mathcal H_{\mathrm{carry}}=\ell^2(\mathbb N,\mathbb C),
$$

`CarryVerticalL2`, os shifts concretos são `carryVerticalL2BackwardShift` e `carryVerticalL2UnilateralShift`; o Green é `carryVerticalL2WeightedGreen q`.

### 24.1. Bracket, traço e retorno

O bracket vestido é `carryWeightedVerticalCenteredBracket q`; o traço de bordo é

$$
\operatorname{Tr}_q x
=\left(x_0,\frac{x_1}{q}-x_0\right),
$$

`carryWeightedVerticalTrace q`.

Os dois modos de retorno são

$$
g_q(k)=q^k,
\qquad
h_q(k)=kq^k,
$$

`carryGeometricAmplitudeVector` e `carryAffineSlopeAmplitudeVector`. O retorno

$$
R_q(a,b)(k)=q^k(a+kb)
$$

é `carryWeightedVerticalReturn q`.

Os teoremas de bordo são

$$
\operatorname{Tr}_qR_q=I
$$

em `carryWeightedVerticalTrace_comp_return`, e

$$
B_qR_q=0
$$

em `carryWeightedVerticalCenteredBracket_comp_return`.

A telescopagem escalar é `carryWeightedScalarReconstruction`. Promovida ao Hilbert, ela produz o Teorema Fundamental da Válvula Discreta:

$$
\boxed{
G_qB_q+R_q\operatorname{Tr}_q=I
},
$$

em `carryWeightedVerticalTfvd_identity` para $0<q<1$. A especialização material é

`primeCarryWeightedVerticalTfvd_identity p hp`.

## 25. Gerador real-espectral finito

Para um cutoff (N), o espaço é

$$
\mathcal H_N=\mathbb C^{\{0,\ldots,N-1\}},
$$

`FiniteRealSpectralHilbert N`.

A frequência da coordenada (n) é

$$
\omega_n=\log(n+1),
$$

`finiteRealSpectralFrequency n`. O gerador diagonal é

$$
(L_Nx)_n=\omega_nx_n,
$$

`finiteRealSpectralGenerator N`, com fórmula `finiteRealSpectralGenerator_apply`.

`finiteRealSpectralGenerator_isSymmetric` prova a simetria; `finiteRealSpectralSelfAdjointGenerator N` fornece a realização contínua auto-adjunta. Nos vetores canônicos,

$$
L_Ne_n=\omega_ne_n,
$$

por `finiteRealSpectralGenerator_basisVector`.

### 25.1. Evolução unitária

A fase é

$$
\varphi_t(n)=e^{-it\omega_n},
$$

`finiteRealSpectralPhase t n`. A evolução

$$
(U_N(t)x)_n=\varphi_t(n)x_n
$$

é `finiteRealSpectralEvolution N t`, uma equivalência linear isométrica.

As leis de grupo são

$$
U_N(0)=I,
\qquad
U_N(t+u)=U_N(t)U_N(u),
$$

em `finiteRealSpectralEvolution_zero` e `finiteRealSpectralEvolution_add`.

O corte do estado (u_t) é `finiteRealSpectralStateVector N t`, com fórmula coordenada `finiteRealSpectralStateVector_apply`.

O gerador (L_N), a evolução (U_N(t)) e o readout `realSpectralGenuine t` são objetos distintos: (L_N) tem frequências (log(n+1)), (U_N(t)) gira a fase e o Genuine observa a câmera bracketada nessa órbita.

## 26. Gerador maximal infinito em ℓ²

O Hilbert infinito é

$$
\mathcal H_\infty=\ell^2(\mathbb N,\mathbb C),
$$

`InfiniteRealSpectralHilbert`.

A frequência é `infiniteRealSpectralFrequency n = log(n+1)`. O domínio maximal é

$$
\mathcal D(L)=
\left\{x\in\ell^2:
(\omega_nx_n)_{n\ge0}\in\ell^2
\right\},
$$

`infiniteRealSpectralMaximalDomain`. O operador é

$$
(Lx)_n=\omega_nx_n,
$$

`infiniteRealSpectralGenerator`.

Os teoremas estruturais são:

- `mem_infiniteRealSpectralGenerator_domain`: caracterização do domínio;
- `infiniteRealSpectralBasisVector_mem_domain`: os vetores canônicos pertencem ao domínio;
- `infiniteRealSpectralGenerator_basisVector`: $Le_n=\omega_ne_n$;
- `infiniteRealSpectralGenerator_dense_domain`: domínio denso;
- `infiniteRealSpectralGenerator_isFormalAdjoint`: simetria formal;
- `infiniteRealSpectralGenerator_adjoint_apply`: fórmula do adjunto;
- `infiniteRealSpectralGenerator_adjoint_domain_le`: maximalidade do domínio;
- `infiniteRealSpectralGenerator_isSelfAdjoint`: auto-adjunção;
- `infiniteRealSpectralGenerator_isClosed`: grafo fechado.

A evolução infinita é

$$
(U(t)x)_n=e^{-it\omega_n}x_n,
$$

`infiniteRealSpectralEvolution t`. As leis

$$
U(0)=I,
\quad
U(t+u)=U(t)U(u),
\quad
U(-t)U(t)=I,
\quad
\|U(t)x\|=\|x\|
$$

são `infiniteRealSpectralEvolution_zero`, `infiniteRealSpectralEvolution_add`, `infiniteRealSpectralEvolution_neg` e `infiniteRealSpectralEvolution_norm`.

## 27. Cauda Genuine-first: proveniência exata do cutoff

A cauda bracketada depois do corte (M) é

$$
T_{p,M}(s)
=\sum_{k\ge0}\Delta^{\mathrm{sat}}_{p,k+M}(s),
$$

definida como `realCpBracketCutoffTail p M s`.

Para (p) primo e (-1<\Re(s)),

$$
\boxed{
\mathcal B_p(s)
=\mathcal B_{p,M}(s)+T_{p,M}(s)
},
$$

por `bracketedDirichletChart_eq_finite_add_cutoffTail`. A versão com a carta aritmética é `bracketedDirichletChart_eq_finiteChart_add_cutoffTail`.

Se $\mathcal B_p(s)=0$, então

$$
\mathcal B_{p,M}(s)=-T_{p,M}(s)
$$

por `finiteBracketedDirichletChart_eq_neg_cutoffTail_of_chart_zero`. A forma vertical é

$$
P_{p,M}(s)+T_{p,M}(s)=V_{p,M}(s),
$$

em `blockPrefix_add_cutoffTail_eq_verticalCorrection_of_chart_zero`.

Na órbita real, uma ressonância fornece

$$
\operatorname{finiteRealSpectralChart}_{p,M}(t)
=-T_{p,M}(s(t))
$$

por `finiteRealSpectralChart_eq_neg_cutoffTail_of_resonance`, e a câmera normalizada é

$$
\operatorname{finiteRealSpectralCamera}_{p,M}(t)
=-\frac{T_{p,M}(s(t))}{F_p(t)}
$$

por `finiteRealSpectralCamera_eq_neg_cutoffTail_div_factor_of_resonance`.

## 28. Cutoffs cruzados e detector multibase

Para a câmera (p), use o cutoff determinado pela outra base:

$$
M_p(L;q)=qL+h_q.
$$

Este é `crossPrimeAlignedCutoff q L`. Os dois cutoffs ladrilham o mesmo horizonte horizontal:

$$
P_{p,M_p(L;q)}[f]
=P_{q,M_q(L;p)}[f]
$$

por `blockPrefix_cross_prime_aligned_scale`.

O defeito alinhado é

$$
\mathfrak D_{p,q,L}(s)
=\bigl(V_{p,M_p}-T_{p,M_p}\bigr)
-\bigl(V_{q,M_q}-T_{q,M_q}\bigr),
$$

`crossPrimeAlignedCutoffDefect p q L s`.

O kernel prova, em cada escala,

$$
\mathfrak D_{p,q,L}(s)
=\mathcal B_q(s)-\mathcal B_p(s)
$$

por `crossPrimeAlignedCutoffDefect_eq_chart_sub_chart`, e

$$
\boxed{
\mathfrak D_{p,q,L}(s)
=\bigl(F_q(s)-F_p(s)\bigr)G(s)
}
$$

por `crossPrimeAlignedCutoffDefect_eq_factor_sub_mul_genuine`.

Para (p\ne q), `cpChartFactor_sub_ne_zero_of_distinct_primes_on_strip` dá

$$
F_q(s)-F_p(s)\ne0,
$$

e `crossPrimeAlignedCutoffDefect_eq_zero_iff_genuine_zero` conclui

$$
\boxed{
\mathfrak D_{p,q,L}(s)=0
\iff
G(s)=0
}.
$$

A cauda satisfaz

$$
T_{p,M}(s)\longrightarrow0
$$

por `realCpBracketCutoffTail_tendsto_zero`. Em um zero Genuine, as correções verticais sincronizam:

$$
V_{p,M_p(L;q)}(s)-V_{q,M_q(L;p)}(s)
\longrightarrow0,
$$

em `verticalCorrection_cross_prime_aligned_tendsto_zero_of_genuine_zero`.

A forma horizontal ponderada é

`weightedHorizontalPrefixes_cross_prime_aligned_tendsto_zero_of_genuine_zero`, usando `verticalCorrection_dirichlet_eq_cpow_mul_prefix`.

## 29. Green multibase em eixos ortogonais

As duas câmeras Green vivem em

$$
\mathcal H_G^{(2)}=\mathbb R^2,
$$

`TwoPrimeGreenHilbert`. `twoPrimeGreenVector x y` preserva as duas coordenadas e

$$
\langle(x,y),(x,y)\rangle=x^2+y^2
$$

por `twoPrimeGreenVector_inner_self`.

Nos cutoffs cruzados, definem-se:

- `crossPrimeAlignedGreenFluxVector`;
- `crossPrimeAlignedRadialBulkVector`;
- `crossPrimeAlignedGreenBoundaryVector`.

A identidade vetorial exata é

$$
\boxed{
\boldsymbol\Phi_{p,q,L}(s)
=\mathbf R_{p,q,L}(s)
+\boldsymbol\partial_{p,q,L}(s)
},
$$

por `crossPrimeAlignedGreenFluxVector_eq_radial_add_boundary`.

O bulk é

$$
\mathbf R_{p,q,L}(s)
=\Bigl(
2\delta\,\mathcal E_{p,M_p}(s),
2\delta\,\mathcal E_{q,M_q}(s)
\Bigr).
$$

No strip,

$$
\boxed{
\mathbf R_{p,q,L}(s)=0
\iff
\delta=0
},
$$

por `crossPrimeAlignedRadialBulkVector_eq_zero_iff_criticalDisplacement_eq_zero`.

A energia de bordo é `crossPrimeAlignedGreenBoundaryEnergy`; sua identificação com o produto interno é `crossPrimeAlignedGreenBoundaryVector_inner_self`. Em um zero Genuine,

$$
\|\boldsymbol\partial_{p,q,L}(s)\|^2\longrightarrow0
$$

por `crossPrimeAlignedGreenBoundaryEnergy_tendsto_zero_of_genuine_zero`.

O fechamento coordenada a coordenada é `CrossPrimeAlignedGreenClosure p q s`. Sob as hipóteses explícitas de primalidade, imparidade, strip e (G(s)=0),

$$
\boxed{
\operatorname{CrossPrimeAlignedGreenClosure}_{p,q}(s)
\iff
\delta=0
},
$$

em `crossPrimeAlignedGreenClosure_iff_criticalDisplacement_eq_zero`. A comparação com o bulk em qualquer escala é `crossPrimeAlignedGreenClosure_iff_radialBulkVector_eq_zero`.

## 30. Câmeras Genuine ortogonais e operador finito

O espaço de duas câmeras complexas é

$$
\mathcal H_{\mathrm{Gen}}^{(2)}=\mathbb C^2,
$$

`TwoPrimeGenuineHilbert`.

Os eixos `firstPrimeGenuineAxis` e `secondPrimeGenuineAxis` são ortogonais por `firstPrimeGenuineAxis_inner_secondPrimeGenuineAxis`.

Para $s\in\mathcal S$, a câmera normalizada é

$$
C_{p,M}(s)=\frac{\mathcal B_{p,M}(s)}{F_p(s)},
$$

`finiteNormalizedGenuineCamera p M s`. Para (p) primo ímpar,

$$
C_{p,M}(s)\longrightarrow G(s)
$$

por `finiteNormalizedGenuineCamera_tendsto_genuineContinuation`.

O vetor alinhado é

$$
\mathbf C_{p,q,L}(s)
=\bigl(C_{p,M_p(L;q)}(s),C_{q,M_q(L;p)}(s)\bigr),
$$

`finiteAlignedOrthogonalGenuineVector`. Ele converge a

$$
\mathbf G_\infty(s)=(G(s),G(s)),
$$

`orthogonalGenuineLimitVector`, por `finiteAlignedOrthogonalGenuineVector_tendsto_limit`.

O operador diagonal genérico é

$$
D(a,b)(x_0,x_1)=(ax_0,bx_1),
$$

`twoPrimeGenuineDiagonalOperator a b`. Portanto, o operador finito alinhado é

$$
\mathcal G_{p,q,L}(s)
=D\bigl(C_{p,M_p(L;q)}(s),C_{q,M_q(L;p)}(s)\bigr),
$$

`finiteAlignedOrthogonalGenuineOperator p q L s`.

## 31. Operador Genuine no limite e convergência forte

O operador-limite é

$$
\boxed{
\mathcal G_\infty(s)
=D(G(s),G(s))
=G(s)I_{\mathbb C^2}
},
$$

definido por `orthogonalGenuineLimitOperator s`. A ação escalar é `orthogonalGenuineLimitOperator_apply`:

$$
\mathcal G_\infty(s)v=G(s)v.
$$

Para todo (v\in\mathbb C^2),

$$
\boxed{
\mathcal G_{p,q,L}(s)v
\longrightarrow
\mathcal G_\infty(s)v
},
$$

em `finiteAlignedOrthogonalGenuineOperator_tendsto_apply`, sob $p,q$ primos ímpares e $s\in\mathcal S$. Esta é a convergência forte formalizada.

O operador-limite possui a caracterização

$$
\boxed{
\mathcal G_\infty(s)=0
\iff
G(s)=0
},
$$

em `orthogonalGenuineLimitOperator_eq_zero_iff`. A direção especializada é `orthogonalGenuineLimitOperator_eq_zero_of_genuine_zero`; a convergência dos operadores finitos a zero em cada vetor é `finiteAlignedOrthogonalGenuineOperator_tendsto_zero_of_genuine_zero`.

Na órbita (s=s(t)), o coeficiente é

$$
G(s(t))=G_{\mathbb R}(t),
$$

logo

$$
\mathcal G_\infty(s(t))=0
\iff
\operatorname{IsRealSpectralResonance}(t).
$$

Esta especialização combina `realSpectralGenuine`, `IsRealSpectralResonance` e `orthogonalGenuineLimitOperator_eq_zero_iff`.

## 32. Energia Green infinita e vetor-limite

Para $s\in\mathcal S$, a estimativa

$$
\|\operatorname{edge}_n(s)\|
\le
\|s\|\,\|s^\#\|(n+1)^{-3}
$$

é `norm_finiteReflectedGradientEdge_le`. A somabilidade absoluta é dada por `summable_norm_finiteReflectedGradientEdge` e `summable_finiteReflectedGradientEdge`.

O pareamento infinito é

$$
E_\infty(s)
=\sum_{n\ge0}\overline{g_s(n)}g_{s^\#}(n),
$$

`infiniteReflectedGradientPairing s`. Os pareamentos finitos convergem por `finiteReflectedGradientPairing_tendsto_infinite`.

A energia real é

$$
\mathcal E_\infty(s)=\Re E_\infty(s),
$$

`infiniteReflectedGreenEnergy s`, e

$$
\boxed{\mathcal E_\infty(s)>0}
$$

por `infiniteReflectedGreenEnergy_pos`.

Em um zero Genuine,

$$
\Phi_{p,M}(s)
\longrightarrow
R_p(\delta)\mathcal E_\infty(s)
$$

por `finiteBracketCoupledCpGreenFlux_tendsto_infiniteBulk_of_genuine_zero`.

O vetor Green limite é

$$
\mathbf L_{p,q}(s)
=\Bigl(
R_p(\delta)\mathcal E_\infty(s),
R_q(\delta)\mathcal E_\infty(s)
\Bigr),
$$

`crossPrimeAlignedGreenLimitVector p q s`.

Nos cutoffs cruzados,

$$
\boldsymbol\Phi_{p,q,L}(s)
\longrightarrow
\mathbf L_{p,q}(s)
$$

por `crossPrimeAlignedGreenFluxVector_tendsto_limit_of_genuine_zero`.

Como $\mathcal E_\infty(s)>0$,

$$
\boxed{
\mathbf L_{p,q}(s)=0
\iff
\delta=0
},
$$

em `crossPrimeAlignedGreenLimitVector_eq_zero_iff_criticalDisplacement_eq_zero`.

## 33. Kernel conjunto dos dois objetos-limite

O operador Genuine e o vetor Green são colados pela equivalência

$$
\boxed{
\left(
\mathcal G_\infty(s)=0
\ \land\
\mathbf L_{p,q}(s)=0
\right)
\iff
\left(
G(s)=0
\ \land\
\delta=0
\right)
}.
$$

O nome Lean é `orthogonalGenuineGreenJointKernel_iff`, com hipóteses $p,q$ primos e $s\in\mathcal S$.

Na especialização $s=s(t)$, `criticalLineParameter_re` dá $\delta=0$ identicamente e `realSpectralGenuine t=G(s(t))`. Assim, nessa órbita, o kernel conjunto é lido pelo predicado `IsRealSpectralResonance t`.

## 34. Pencils de bordo

Um pencil linear é dado por dois traços

$$
\Gamma_0:X\to B,
\qquad
\Gamma_1:X\to B.
$$

O tipo é `LinearBoundaryPencil X B`. Para $\lambda\in\mathbb C$,

$$
P(\lambda)=\Gamma_1-\lambda\Gamma_0
$$

é `LinearBoundaryPencil.operator`.

Um valor é característico quando existe (x) com

$$
\Gamma_0x\ne0,
\qquad
P(\lambda)x=0.
$$

Esta é `LinearBoundaryPencil.IsCharacteristicValue`. A formulação pela inclinação da relação valor–fluxo é `LinearBoundaryPencil.RelationHasSlope`; a equivalência é `isCharacteristicValue_iff_relationHasSlope`.

Se (Gamma_0) é uma equivalência linear, `RegularLinearBoundaryPencil` define a linearização

$$
L_P=\Gamma_0^{-1}\Gamma_1.
$$

O nome é `RegularLinearBoundaryPencil.linearization`; `isCharacteristicValue_iff_eigenpair` identifica valores característicos e autopares.

### 34.1. Pencil Genuine escalar

Na altura real (t),

$$
\Gamma_0(z)=z,
\qquad
\Gamma_1(z)=G_{\mathbb R}(t)z.
$$

O fluxo é `realSpectralGenuineBoundaryFlux t`; o pencil é `realSpectralGenuineBoundaryPencil t`. Sua linearização satisfaz

$$
L_tz=G_{\mathbb R}(t)z
$$

por `realSpectralGenuineBoundaryLinearization_apply`.

A classificação é

$$
\lambda\text{ característico}
\iff
\lambda=G_{\mathbb R}(t),
$$

em `realSpectralGenuine_isCharacteristicValue_iff`.

Assim,

$$
\operatorname{IsRealSpectralResonance}(t)
\iff
0\text{ é valor característico}
$$

por `isRealSpectralResonance_iff_zero_characteristicValue`, e

$$
\operatorname{IsRealSpectralResonance}(t)
\iff
\ker L_t\ne\{0\}
$$

por `isRealSpectralResonance_iff_linearized_kernel`. A relação de bordo é fechada por `realSpectralGenuineBoundaryRelation_isClosed`.

### 34.2. Pencil da fibra vertical

O pencil `carryWeightedVerticalBoundaryPencil q` usa como traços o valor e o fluxo definidos a partir de `carryWeightedVerticalTrace q`. A relação é descrita por `carryWeightedVerticalBoundaryRelation_eq_top` e sua fechadura por `carryWeightedVerticalBoundaryRelation_isClosed`.

A reconstrução TFVD através desse pencil é `carryWeightedVerticalTfvd_reconstruction_via_boundaryPencil`. A especialização material é `primeCarryWeightedVerticalBoundaryPencil p`.

## 35. Carrier aritmético `G_pre`

`NativeGpreContext` mantém separados, por tipos distintos, os eixos

$$
(p_{\mathrm{ar}},\tau_{\mathrm{ar}},
\text{célula},\text{canto},\text{orientação},
\text{papel},\text{perna},d_J,p_{\mathrm{torre}},j_{\mathrm{torre}}).
$$

Os tipos básicos são:

- `GpreArithmeticPrime`;
- `GpreArithmeticTime`;
- `GpreJordanDivisor`;
- `GpreTowerPrime`;
- `GpreTowerLevel`;
- `GpreCorner`;
- `GpreOrientation`;
- `GpreLeg`;
- `GpreGraphRole`.

### 35.1. Fibra aritmética e torre

As funções aritméticas nativas são:

- `nativeGprePowerArithmetic`;
- `nativeGpreValuationPowerArithmetic`;
- `nativeGpreJordanArithmetic`;
- `nativeGpreHArithmetic`.

As fórmulas de soma sobre divisores são `sum_divisors_nativeGpreJordanArithmetic` e `sum_divisors_nativeGpreHArithmetic`. O bracket local Jordan–(H) é `nativeGpreJordanBracket`; sua resolução na fibra é `sum_divisors_nativeGpreJordanBracket`.

O readout reduzido do par é `nativeGpreReducedPairReadout`. A soma das coordenadas do divisor recupera esse readout por `sum_gcdDivisors_nativeGpreDivisorCoordinate_eq_reduced`. A versão por canto é `sum_gcdDivisors_nativeGpreCornerCoordinate_eq_readout`.

O perfil material é

$$
\rho_{p,\tau}(j)=
\begin{cases}
0,&j=0,\\
p^{-j\tau}/j,&j>0,
\end{cases}
$$

`nativeUnitMassTowerProfile p tau j`. Sua somabilidade quadrática é `nativeUnitMassTowerProfile_sq_summable`. O vetor em $\ell^2$ é `nativeGpreTowerProfileVector`; a identidade de norma é `nativeGpreTowerProfileVector_norm_sq`.

O coeficiente completo é `nativeGpreTowerCoordinateCoefficient`. O lift linear

$$
(L_{G_{\mathrm{pre}}}x)(c)
=x(c.\mathrm{cell})\,\Theta(c)
$$

é `nativeGpreTowerLiftLinearMap`; a fórmula coordenada é `nativeGpreTowerLiftLinearMap_apply`. A soma na fibra dos divisores recupera o readout tensorizado com a torre em `sum_gcdDivisors_nativeGpreTowerCoordinate_eq_readout`.

As cotas de Jordan são:

$$
0\le J_{2\tau}(n)\le n^{2\tau},
$$

por `nativeGpreJordanArithmetic_nonneg` e `nativeGpreJordanArithmetic_le_pow`. A majorante local do bracket é `NativeGpreLocalJordanHBound.abs_bracket_le`.

A continuidade global é organizada por `NativeGpreTowerLiftCertificate`. O ledger quadrático é `nativeGpreGraphSquareBound`; `nativeGpreGraphSquareBound_lt_128_sq` prova a cota estrita por (128^2). O mapa contínuo é `NativeGpreTowerLiftCertificate.toContinuousLinearMap`, com `norm_toContinuousLinearMap_le`; a extensão à completude é `NativeGpreTowerLiftCertificate.completionExtension`.

### 35.2. Traços valor–fluxo e pencil de número

`NativeGpreBoundaryContext` remove apenas o papel valor/fluxo do contexto; `withRole` o recoloca. Os dois lifts são `nativeGpreBoundaryValueLift` e `nativeGpreBoundaryNumberFluxLift`.

Em uma coordenada de nível (j),

$$
\Gamma_1=j\Gamma_0,
$$

por `nativeGpreBoundaryNumberFluxLift_apply_eq_level_mul_value` e, como mapas, por `nativeGpreBoundaryNumberFluxLift_eq_numberOperator_comp_valueLift`.

O pencil é `nativeGpreProvenanceBoundaryPencil`. Sua relação está contida no grafo do operador número por `nativeGpreProvenanceBoundaryRelation_le_numberGraph`. Uma coordenada ativa determina o nível em `nativeGpreProvenanceBoundaryPencil_operator_eq_zero_forces_level`; dois níveis distintos são tratados por `nativeGpreProvenanceBoundaryPencil_no_zero_on_two_distinct_levels`.

## 36. Análise TFVD–`G_pre` e range fechado

Para um atlas finito (S) de contextos, a análise enriquecida é

$$
\mathcal A_{q,S}(x)
=\Bigl(
(B_qx,\operatorname{Tr}_qx),
(L_S^{\mathrm{value}}x,L_S^{\mathrm{number}}x)
\Bigr),
$$

definida como `nativeGpreFiniteTfvdAnalysis q S`.

A reconstrução é

$$
\mathcal R_{q,S}(g,b,\pi)=G_qg+R_qb,
$$

`nativeGpreFiniteTfvdReconstruction`. Pela identidade vertical,

$$
\boxed{
\mathcal R_{q,S}\mathcal A_{q,S}=I
},
$$

em `nativeGpreFiniteTfvdReconstruction_comp_analysis`.

Consequências:

- `nativeGpreFiniteTfvdAnalysis_injective`: injetividade;
- `nativeGpreFiniteTfvdAnalysisProjection_idempotent`: projeção contínua idempotente;
- `nativeGpreFiniteTfvdAnalysis_range_eq_eqLocus`: range como locus de pontos fixos;
- `nativeGpreFiniteTfvdAnalysis_range_isClosed`: range fechado;
- `nativeGpreFiniteTfvdAnalysis_range_isComplete`: range completo.

A inclusão canônica do core finitamente suportado em $\ell^2$ é `nativeGpreCanonicalVerticalRealization`, injetiva por `nativeGpreCanonicalVerticalRealization_injective`. A colagem diagonal é `nativeGpreCanonicalTfvdGlue`, e a reconstrução vertical correspondente é `nativeGpreCanonicalTfvd_vertical_reconstruction`.

No atlas finito, `nativeGpreFiniteCanonicalTfvdBoundaryPencil` produz a relação valor–fluxo conjunta. Sua fechadura é `nativeGpreFiniteCanonicalTfvdBoundaryRelation_isClosed`; as projeções TFVD e de proveniência são `nativeGpreFiniteCanonicalTfvdRelation_vertical_projection` e `nativeGpreFiniteCanonicalTfvdRelation_provenance_projection`.

Quando (S\subseteq T), `nativeGpreFiniteTfvdAnalysis_restrict` prova compatibilidade com a restrição de atlas. No produto de todos os atlas finitos, `nativeGpreTfvdProjectiveAnalysis` possui left inverse por `nativeGpreTfvdProjectiveAnalysis_hasLeftInverse`; sua injetividade e range fechado são `nativeGpreTfvdProjectiveAnalysis_injective` e `nativeGpreTfvdProjectiveAnalysis_range_isClosed`.

### 36.1. Observador visível

Para um funcional contínuo $\ell:\mathcal H_{\mathrm{carry}}\to\mathbb C$, o readout é aplicado depois da reconstrução:

$$
\operatorname{Readout}(d)=\ell(\mathcal R_{q,S}d).
$$

Este é `nativeGpreFiniteTfvdVisibleReadout`. Na imagem da análise,

$$
\operatorname{Readout}(\mathcal A_{q,S}x)=\ell(x)
$$

por `nativeGpreFiniteTfvdVisibleReadout_analysis`.

Na órbita $z\mapsto zx$, `nativeGpreFiniteTfvdVisibleBoundaryPencil` tem coeficiente $\ell(x)$, e

$$
\lambda\text{ característico}
\iff
\lambda=\ell(x)
$$

por `nativeGpreFiniteTfvdVisible_isCharacteristicValue_iff`. A especialização em zero é `nativeGpreFiniteTfvdVisible_zeroCharacteristic_iff`; a relação é fechada por `nativeGpreFiniteTfvdVisibleBoundaryRelation_isClosed`.

## 37. Estado nativo vestido e limite dos pencils Genuine

O estado finito vestido é

$$
x_{q,M,t}(n)=
\begin{cases}
q^n u_t(n),&n<3M+1,\\
0,&n\ge3M+1.
\end{cases}
$$

No Lean, ele é `nativeGpreFiniteWeightedRealSpectralState`.

`carryWeightedUndressedEval q n` remove o fator (q^n). O observador angular é `carryWeightedCanonicalAngularBlockObserver`; o observador da carta é `carryWeightedFiniteChartObserver q M`.

O teorema

`carryWeightedFiniteChartObserver_finiteRealSpectralState`

prova

$$
\ell_{q,M}\bigl(x_{q,M,t}\bigr)=\mathcal B_{3,M}(s(t)).
$$

Após a divisão por (F_3(t)), `nativeGpreFiniteGenuineObserver` recupera a câmera finita. A identidade é `nativeGpreFiniteGenuineObserver_finiteRealSpectralState`:

$$
\ell^G_{q,M,t}\bigl(x_{q,M,t}\bigr)
=C_{3,M}(t).
$$

O pencil `nativeGpreFiniteGenuineBoundaryPencil` satisfaz

$$
\lambda\text{ característico}
\iff
\lambda=C_{3,M}(t)
$$

por `nativeGpreFiniteGenuine_isCharacteristicValue_iff`; em zero, usa-se `nativeGpreFiniteGenuine_zeroCharacteristic_iff`.

As câmeras convergem:

$$
C_{3,M}(t)\longrightarrow G_{\mathbb R}(t)
$$

por `finiteRealSpectralCamera_three_tendsto_realSpectralGenuine`. As linearizações convergem em `nativeGpreFiniteGenuineBoundaryLinearization_tendsto`, e convergem a zero em uma ressonância por `nativeGpreFiniteGenuineBoundaryLinearization_tendsto_zero_of_resonance`.

O pencil-limite é `nativeGpreGenuineLimitBoundaryPencil t`. A equivalência final dessa interface é

$$
\operatorname{IsRealSpectralResonance}(t)
\iff
0\text{ é valor característico do pencil-limite},
$$

em `isRealSpectralResonance_iff_nativeGpreGenuineLimit_zeroCharacteristic`.

## 38. Síntese escalar e orçamentos angulares

O kernel centrado de síntese é `finitePortSynthesisKernelValue`; sua soma zero é `finitePortSynthesisKernelValue_sum_eq_zero`. A primitiva finita é `finitePortSynthesisKernelPrefix`.

O ledger de pareamentos é

`finitePortSynthesis_pairing_ledger`.

Aplicado à porta angular, ele fornece:

- `finiteCanonicalAngularTrace_eq_secondDifferenceSynthesis_sub_outer`;
- `finiteCanonicalAngularScalarPairing_synthesis_ledger`;
- `finiteCanonicalAngularScalarPairing_synthesis_green_ledger`;
- `finiteCanonicalAngularGreenCorrection_synthesis_ledger`.

A soma por partes é `finitePortSynthesisKernelPairing_summation_by_parts`. O bulk fechado é `finitePortSynthesisClosedBulk`, com

$$
\operatorname{KernelPairing}_M
=M\,\operatorname{ClosedBulk}_M
$$

em `finitePortSynthesisKernelPairing_eq_mul_closedBulk`.

Na porta canônica, `finiteCanonicalAngularClosedSynthesisBulk_eq_centeredTraceBulk` identifica esse bulk com os traços centrados. A decomposição escalar é

$$
\operatorname{AngularScalarPairing}
=M\,\operatorname{GreenEnergy}
+\operatorname{ClosedBulkDefect},
$$

em `finiteCanonicalAngularScalarPairing_eq_mul_green_add_closedBulkDefect`.

Os limites radiais formalizados são `finiteCanonicalAngularRadialScalarPairing_tendsto_zero_of_genuine_zero`, `finiteCanonicalAngularRadialGreenBudget_tendsto_zero_of_genuine_zero` e `finiteCanonicalAngularRadialClosedBulkBudget_tendsto_zero_of_genuine_zero`.

### 38.1. Orçamentos Green angular e unilateral

O pareamento escalar angular é `finiteCanonicalAngularScalarPairing`; sua fatoração como produto é `finiteCanonicalAngularScalarPairing_eq_product`, e sua decomposição diagonal/off-diagonal é `finiteCanonicalAngularScalarPairing_eq_diagonal_add_offDiagonal`.

A energia e a correção locais são `finiteCanonicalAngularGreenEnergy` e `canonicalAngularLocalGreenCorrection`. O ledger global é

$$
\operatorname{AngularScalarPairing}
=\operatorname{AngularGreenEnergy}
+\operatorname{AngularGreenCorrection},
$$

em `finiteCanonicalAngularScalarPairing_eq_green_add_correction`.

`finiteCanonicalAngularGreenBudget_tendsto_zero_of_genuine_zero_pair` fornece o limite refletido em um par de zeros Genuine. A versão unilateral usa `finiteCanonicalAngularGreenBudget_tendsto_zero_of_genuine_zero`.

As interfaces de cancelamento são `GenuineAngularGreenCancellationBridge p` e `GenuineOneSidedAngularGreenBridge p`. Seus teoremas `GenuineAngularGreenCancellationBridge.criticalDisplacement_eq_zero` e `GenuineOneSidedAngularGreenBridge.criticalDisplacement_eq_zero` extraem a coordenada crítica. As conversões para a interface de fluxo são `GenuineAngularGreenCancellationBridge.toGenuineCarryFluxBridge` e `GenuineOneSidedAngularGreenBridge.toGenuineCarryFluxBridge`.

## 39. Detectores equivalentes da coordenada transversal

O mesmo deslocamento

$$
\delta=\Re(s)-\frac12
$$

é medido por interfaces diferentes. A tabela registra a equivalência efetivamente formalizada e suas condições.

| Detector | Equivalência | Nome Lean e condições centrais |
|---|---|---|
| Norma do ramo | $\mathcal N_p(\sigma)^2=1\iff\sigma=1/2$ | `branchNormSq_eq_one_iff`; $p$ primo, $0<\sigma$ |
| Defeito do ramo | $D_p(\sigma)=0\iff\delta(\sigma)=0$ | `branchDefect_eq_zero_iff_criticalDisplacement_eq_zero`; mesmas condições |
| Tilt local | $\Theta_{p,\sigma-1/2}(c)=0\iff\sigma=1/2$ | `cpTiltAtSigma_eq_zero_iff_half`; $p$ primo ímpar, $0<\sigma$, $h_p<c$ |
| Diferença radial | $R_p(\delta)=0\iff\delta=0$ | `cpRadialDifference_eq_zero_iff`; $p$ primo |
| Fluxo de uma câmera | $\Phi_{p,M}\to0\iff\delta=0$ em um zero Genuine | `coupledFlux_tendsto_zero_iff_criticalDisplacement_eq_zero`; $p$ primo, $s\in\mathcal S$, $G(s)=0$ |
| Ledger enriquecido | `EnrichedGenuineCarryLedgerClosesAt p s` $\iff\Re(s)=1/2$ em um zero Genuine | `enrichedGenuineCarryLedgerClosesAt_iff_re_eq_half_of_genuine_zero` |
| Green multibase | `CrossPrimeAlignedGreenClosure p q s` $\iff\delta=0$ em um zero Genuine | `crossPrimeAlignedGreenClosure_iff_criticalDisplacement_eq_zero` |
| Vetor Green limite | $\mathbf L_{p,q}(s)=0\iff\delta=0$ | `crossPrimeAlignedGreenLimitVector_eq_zero_iff_criticalDisplacement_eq_zero`; $p,q$ primos, $s\in\mathcal S$ |

As proposições globais de transporte são:

$$
\operatorname{GenuineZeroSaturatesCarry}(p)
\equiv
\forall s\in\mathcal S,
\ G(s)=0\Rightarrow\mathcal N_p(\Re s)^2=1,
$$

definida como `GenuineZeroSaturatesCarry p`, e `GenuineZerosCloseEnrichedCarryLedger`, definida pelo fechamento do ledger em todos os zeros no strip.

`genuineZeroSaturatesCarry_iff_genuineZerosCloseEnrichedCarryLedger` identifica essas duas formulações; `genuineZeroSaturatesCarry_iff_genuineCarryFluxBridge` identifica a formulação de saturação com `GenuineCarryFluxBridge`; `genuineZeroSaturatesCarry_prime_independent` transporta a proposição entre bases primas. Sob `GenuineZeroSaturatesCarry p`, `re_eq_half_of_genuine_zero_of_saturatesCarry` fornece $\Re(s)=1/2$ para um zero no strip.

## 40. Guia para localizar rotas já formalizadas

Esta tabela organiza objetos que representam a mesma matemática em níveis distintos.

| Conteúdo | Forma finita/aritmética | Forma analítica/espectral | Forma operacional/limite |
|---|---|---|---|
| Centro e profundidade | `nonmultipleEquivIncidence`, `effectiveDepth_eq_centerDepth` | `criticalMass_effectiveDepth_eq_centerDepth` | `primeCarryAmplitudeRatio` |
| Bracket | `CPFormal.Genuine.Cp.bracket` | `realCpSaturatedBracket` | `bracketedDirichletChart` |
| Segunda diferença | `centeredSecondDifference`, `saturatedBracket` | `realCpPairBracket_eq_centeredSecondDifference` | `genuineContinuation_eq_centeredSecondDifferenceSeries` |
| Carta | `CPFormal.Genuine.Cp.finiteChart` | `finiteBracketedDirichletChart` | `genuineContinuation` |
| Câmera normalizada | `finiteRealSpectralCamera` na órbita $s(t)$ | `finiteNormalizedGenuineCamera` para $s\in\mathcal S$ | `orthogonalGenuineLimitOperator` |
| Green | `finiteCpGreenFlux` | `finiteGenuineCpGreenFlux` | `crossPrimeAlignedGreenLimitVector` |
| Green em TFVD | `finiteTfvdCpGreenDiagonal` | `finiteOrientedGenuineCpGreenFlux_eq_tfvdDiagonal` | `CrossPrimeAlignedGreenClosure` |
| Válvula | `tfvdEncode`/`tfvdDecode` | `carryWeightedVerticalTfvd_identity` | `nativeGpreFiniteTfvdReconstruction_comp_analysis` |
| Readout Genuine | `finiteSeededEnrichedTfvdGenuineReadout` | `realSpectralGenuine` | `nativeGpreGenuineLimitBoundaryPencil` |
| Ressonância | zero da carta prima | `IsRealSpectralResonance` | valor característico zero / operador Genuine zero |

### 40.1. Três operadores que devem permanecer distintos

| Operador | Espaço | Ação | Teoremas centrais |
|---|---|---|---|
| Gerador real-espectral $L$ | $\mathbb C^N$ ou $\ell^2$ | $(Lx)_n=\log(n+1)x_n$ | `finiteRealSpectralGenerator_basisVector`, `infiniteRealSpectralGenerator_isSelfAdjoint` |
| Operador Genuine no limite $\mathcal G_\infty(s)$ | $\mathbb C^2$ | $v\mapsto G(s)v$ | `orthogonalGenuineLimitOperator_apply`, `finiteAlignedOrthogonalGenuineOperator_tendsto_apply` |
| Linearização do pencil Genuine | $\mathbb C$ | $z\mapsto G_{\mathbb R}(t)z$ | `realSpectralGenuineBoundaryLinearization_apply`, `isRealSpectralResonance_iff_linearized_kernel` |

O gerador produz a fase, o operador Genuine transporta o coeficiente canônico das duas câmeras e o pencil expressa o mesmo readout como relação de bordo escalar.

## 41. Sequência lógica canônica da formalização

A prova pode ser recuperada sem percorrer rotas paralelas na seguinte ordem.

1. **Incidência balanceada.** `balancedOffsetEquivNonzeroResidue` escolhe o offset residual único; `nonmultipleEquivIncidence` converte a perna em centro e offset.

2. **Carry único.** `dvd_sub_iff_eq_offset` mostra que apenas o offset canônico carrega divisibilidade; `effectiveDepth_eq_centerDepth` identifica o máximo da câmera com a profundidade do centro.

3. **Transporte exato.** `weighted_reindex` passa da soma por pernas à soma por incidências; `weighted_reindex_alignedBox` fecha a igualdade nas caixas alinhadas.

4. **Massa e amplitude.** `criticalAmplitude_sq_eq_mass` estabelece
   $$
   (p^{-k/2})^2=p^{-k}.
   $$

5. **Seleção da abscissa.** `branchNormSq_eq_one_iff` estabelece
   $$
   \mathcal N_p(\sigma)^2=1\iff\sigma=\frac12.
   $$

6. **Coordenada transversal.** `criticalDisplacement` escreve $delta=\sigma-1/2$; `branchDefect_eq_zero_iff_criticalDisplacement_eq_zero`, `cpTiltAtSigma_eq_zero_iff_half` e `cpRadialDifference_eq_zero_iff` reconhecem o mesmo locus em três linguagens.

7. **Parâmetro real.** `criticalLineParameter t` escreve
   $$
   s(t)=\frac12+it.
   $$

8. **Estado real-espectral.** `realSpectralState t n` define
   $$
   u_t(n)=(n+1)^{-1/2-it};
   $$
   `norm_realSpectralState` fixa o módulo $(n+1)^{-1/2}$.

9. **Bracket como segunda diferença.** `bracket_eq_saturatedBracket` e `realCpSaturatedBracket_eq_genuineBracket` identificam a câmera finita com os stencils centrados.

10. **Lei Genuine finita.** `finite_genuine_cancellation` preserva o canal central; `finiteChart_eq_positiveIntervalSum_sub_p_mul_centerSum` organiza a identidade por blocos.

11. **Carta infinita.** `finiteBracketedDirichletChart_tendsto` leva os cutoffs à carta `bracketedDirichletChart` em $Re(s)>-1$.

12. **Normalização.** `cpChartFactor_ne_zero_on_genuineCriticalStrip` permite definir `cpGenuineQuotient`; `bracketedDirichletChart_eq_factor_mul_cpGenuineQuotient` dá a fatoração.

13. **Genuine canônico.** `crossNormalizedChart_eq_swap` e `cpGenuineQuotient_eq_cpGenuineQuotient` identificam todas as câmeras; `genuineContinuation` é o representante comum.

14. **Readout real.** `realSpectralCamera_eq_realSpectralGenuine` identifica a câmera de $u_t$ com $G(s(t))$; `IsRealSpectralResonance` nomeia seu zero.

15. **Green radial.** `cpBlockGradient_eq_eigenvalue_mul`, `finiteBracketCoupledCpGreen_identity` e `finiteRadialGreenEnergy_pos` constroem o fluxo assinado com energia positiva.

16. **TFVD.** `tfvdDecode_encode` dá a válvula local; `finiteOrientedGenuineCpGreenFlux_eq_tfvdDiagonal` identifica sua diagonal Green; `carryWeightedVerticalTfvd_identity` fornece
   $$
   G_qB_q+R_q\operatorname{Tr}_q=I.
   $$

17. **Proveniência.** `nativeGpreFiniteTfvdReconstruction_comp_analysis` incorpora bracket, traço e eixos `G_pre` em uma análise injetiva de range fechado.

18. **Cauda e multibase.** `bracketedDirichletChart_eq_finite_add_cutoffTail` conserva o cutoff; `crossPrimeAlignedCutoffDefect_eq_zero_iff_genuine_zero` detecta $G(s)=0$ em toda escala cruzada.

19. **Ortogonalização.** `finiteAlignedOrthogonalGenuineVector_tendsto_limit` mantém duas câmeras em eixos separados; `crossPrimeAlignedGreenFluxVector_eq_radial_add_boundary` faz o mesmo para Green.

20. **Operador no limite.** `finiteAlignedOrthogonalGenuineOperator_tendsto_apply` prova convergência forte para
   $$
   \mathcal G_\infty(s)=G(s)I.
   $$

21. **Energia e kernel conjuntos.** `infiniteReflectedGreenEnergy_pos` dá energia infinita positiva; `orthogonalGenuineGreenJointKernel_iff` cola o kernel do operador ao kernel radial Green.

22. **Interface de bordo.** `isRealSpectralResonance_iff_zero_characteristicValue` e `isRealSpectralResonance_iff_nativeGpreGenuineLimit_zeroCharacteristic` reescrevem a ressonância como valor característico zero.

Em forma compacta:

$$
\boxed{
\begin{gathered}
n
\xleftrightarrow{\ \text{incidência}\ }
(c_p(n),a_p(n))
\Longrightarrow
k=v_p(c_p(n))
\Longrightarrow
\alpha_{p,k}=p^{-k/2},\\[1mm]
\mathcal N_p(\sigma)^2=1
\Longleftrightarrow
\sigma=\tfrac12
\Longrightarrow
s(t)=\tfrac12+it
\Longrightarrow
u_t(n)=(n+1)^{-s(t)},\\[1mm]
u_t
\xrightarrow{\ \text{brackets}\ }
\mathcal B_{p,M}
\xrightarrow{M\to\infty}
F_pG
\xrightarrow{\ \text{duas câmeras}\ }
\mathcal G_{p,q,L}
\xrightarrow[\mathrm{forte}]{L\to\infty}
G(s)I.
\end{gathered}
}
$$

## 42. Índice por conclusão matemática

| Conclusão procurada | Nome Lean principal |
|---|---|
| Centro (C2) único | `CPFormal.Carry.C2.adjacentCenter_unique` |
| Bijeção perna–incidência (C2) | `CPFormal.Carry.C2.oddLegEquivIncidence` |
| Profundidade (C2) | `CPFormal.Carry.C2.effectiveDepth_eq_centerDepth` |
| Bijeção offset–resíduo (Cp) | `CPFormal.Carry.Cp.balancedOffsetEquivNonzeroResidue` |
| Bijeção perna–incidência (Cp) | `CPFormal.Carry.Cp.nonmultipleEquivIncidence` |
| Offset carregado único | `CPFormal.Carry.Cp.dvd_sub_iff_eq_offset` |
| Profundidade (Cp) | `CPFormal.Carry.Cp.effectiveDepth_eq_centerDepth` |
| Reindexação exata | `CPFormal.Carry.Cp.weighted_reindex_alignedBox` |
| Amplitude ao quadrado = massa | `criticalAmplitude_sq_eq_mass` |
| Saturação = meia abscissa | `branchNormSq_eq_one_iff` |
| Tilt = meia abscissa | `cpTiltAtSigma_eq_zero_iff_half` |
| Bracket = soma de segundas diferenças | `CPFormal.Genuine.Cp.bracket_eq_saturatedBracket` |
| Cancelamento Genuine finito | `CPFormal.Genuine.Cp.finite_genuine_cancellation` |
| Carta finita em dois prefixos | `finiteChart_dirichlet_eq_two_prefixes` |
| Somabilidade dos brackets | `summable_norm_realCpSaturatedBracket` |
| Convergência da carta | `finiteBracketedDirichletChart_tendsto` |
| Fator da câmera não nulo | `cpChartFactor_ne_zero_on_genuineCriticalStrip` |
| Independência da câmera | `cpGenuineQuotient_eq_cpGenuineQuotient` |
| Fatoração canônica | `bracketedDirichletChart_eq_cpChartFactor_mul_genuineContinuation` |
| Estado de amplitude crítica | `norm_realSpectralState` |
| Câmera real = Genuine | `realSpectralCamera_eq_realSpectralGenuine` |
| Gerador finito auto-adjunto | `finiteRealSpectralSelfAdjointGenerator` |
| Gerador infinito auto-adjunto | `infiniteRealSpectralGenerator_isSelfAdjoint` |
| Bloco de gradientes próprio | `cpBlockGradient_eq_eigenvalue_mul` |
| Identidade Green radial | `finiteBracketCoupledCpGreen_identity` |
| Energia Green positiva | `finiteRadialGreenEnergy_pos` |
| Intertwiner Genuine–Green | `finiteGenuineCpGreenFlux_eq_finiteCpGreenFlux` |
| TFVD vertical | `carryWeightedVerticalTfvd_identity` |
| Análise `G_pre` com left inverse | `nativeGpreFiniteTfvdReconstruction_comp_analysis` |
| Range da análise fechado | `nativeGpreFiniteTfvdAnalysis_range_isClosed` |
| Carta = prefixo + cauda | `bracketedDirichletChart_eq_finite_add_cutoffTail` |
| Detector multibase = Genuine | `crossPrimeAlignedCutoffDefect_eq_zero_iff_genuine_zero` |
| Green ortogonal finito | `crossPrimeAlignedGreenFluxVector_eq_radial_add_boundary` |
| Câmeras normalizadas convergem | `finiteNormalizedGenuineCamera_tendsto_genuineContinuation` |
| Operadores convergem fortemente | `finiteAlignedOrthogonalGenuineOperator_tendsto_apply` |
| Operador-limite = (G(s)I) | `orthogonalGenuineLimitOperator_apply` |
| Zero do operador-limite | `orthogonalGenuineLimitOperator_eq_zero_iff` |
| Energia Green infinita positiva | `infiniteReflectedGreenEnergy_pos` |
| Vetor Green limite crítico | `crossPrimeAlignedGreenLimitVector_eq_zero_iff_criticalDisplacement_eq_zero` |
| Kernel conjunto | `orthogonalGenuineGreenJointKernel_iff` |
| Ressonância = valor característico zero | `isRealSpectralResonance_iff_zero_characteristicValue` |

## 43. Mapa da superfície Lean ativa

| Camada | Módulos importados por `CPFormal.lean` |
|---|---|
| Status e primitivas | `Logic/Status`, `Finite/SymmetricPair`, `Finite/Bracket`, `Carry/Shift` |
| Carry (C2) | `Carry/C2Adjacent`, `Carry/C2Depth`, `Carry/C2WeightedReindex`, `Carry/C2AlignedBox` |
| Carry (Cp) | `Carry/CpBalancedResidue`, `Carry/CpGlobalIncidence`, `Carry/CpDepth`, `Carry/CpWeightedReindex`, `Carry/CpAlignedBox`, `Carry/CpBranchWeight` |
| Genuine finito | `Genuine/BalancedOffsets`, `Genuine/FiniteCancellation`, `Genuine/C2`, `Genuine/Cp`, `Genuine/CpFiniteChart`, `Genuine/CpBracketPairing` |
| Norma, tilt e ponte Green | `Analytic/CpBranchNorm`, `Analytic/CpTilt`, `Analytic/CpTiltRigidity`, `Analytic/CpGreenBridge` |
| Carta e regularidade | `Analytic/CpFiniteDirichletChart`, `Analytic/CpDirichletLimit`, `Analytic/CenteredSecondDifferenceBound`, `Analytic/DirichletSecondDifference`, `Analytic/CpBracketConvergence`, `Analytic/CpBracketHolomorphic`, `Analytic/CpGenuineQuotient`, `Analytic/CpGenuineCompatibility` |
| Green finito | `Analytic/CpFiniteGreen`, `Analytic/CpReflectedEndpoint`, `Analytic/CpFiniteGreenCertificate`, `Analytic/CpFiniteGreenRadial`, `Analytic/CpFiniteGreenPositivity`, `Analytic/CpBracketGreenBoundary`, `Analytic/CpBracketGreenFlux` |
| Porta angular e TFVD | `Analytic/CpAngularPort`, `Analytic/CpFiniteTfvdBridge`, `Analytic/CpFinitePortWronskian`, `Analytic/CpGenuineGreenIntertwiner`, `Analytic/CpFiniteTfvdAngularGreenIntertwiner` |
| Log-jet e residual | `Analytic/CpFiniteTfvdLogJetGreenComparison`, `Analytic/CpFiniteLogJetCommutator`, `Analytic/CpFiniteTfvdLogJetCommutatorDefect`, `Analytic/CpFiniteTfvdLogJetResidualCutoff`, `Analytic/CpFiniteTfvdLogJetResidualAsymptotics`, `Analytic/CpFiniteTfvdLogJetResidualReflection`, `Analytic/CpFiniteTfvdLogJetCriticalLineTraces`, `Analytic/CpFiniteTfvdLogJetCriticalPhaseFan` |
| Colagem Genuine–carry | `Analytic/CpFiniteGenuineTfvdProvenanceGluing`, `Analytic/CpGenuineCarrySaturationTransport`, `Analytic/CpGenuineTiltProductRule`, `Analytic/CpTfvdGenuineCarryIdentification` |
| Porta semeada | `Analytic/CpSeededTfvdSameSBoundary`, `Analytic/CpFiniteSeededTfvdGreenIdentity` |
| Núcleo `G_pre` | `Analytic/CpGpreTypes`, `Analytic/CpNativeGpreTowerLift`, `Analytic/CpNativeGpreTowerNorm`, `Analytic/CpNativeGpreJordanBounds`, `Analytic/CpNativeGpreLocalBracketMajorant`, `Analytic/CpQtildeProvenanceContinuity` |
| Real-espectral | `Analytic/CpRealSpectralOperator`, `Analytic/CpRealSpectralGenerator`, `Analytic/CpInfiniteRealSpectralGenerator` |
| Genuine-first | `Analytic/CpGenuineFirstCutoffTail`, `Analytic/CpGenuineFirstMultibaseCutoff`, `Analytic/CpGenuineFirstOrthogonalMultibaseGreen`, `Analytic/CpGenuineFirstOrthogonalLimit`, `Analytic/CpGenuineFirstOrthogonalGreenLimit` |
| Pencils e Green vertical | `Analytic/CpGenuineBoundaryPencil`, `Analytic/CpCarryWeightedVerticalGreen`, `Analytic/CpCarryL2UnilateralShift`, `Analytic/CpCarryWeightedVerticalBracketTrace`, `Analytic/CpCarryWeightedVerticalReturn`, `Analytic/CpCarryWeightedVerticalTfvd`, `Analytic/CpCarryWeightedVerticalTfvdFinite`, `Analytic/CpCarryWeightedVerticalTfvdIdentity`, `Analytic/CpCarryWeightedVerticalBoundaryPencil` |
| Pencils e análise `G_pre` | `Analytic/CpNativeGpreBoundaryPencil`, `Analytic/CpNativeGpreTfvdGluing`, `Analytic/CpNativeGpreTfvdCanonicalGluing`, `Analytic/CpNativeGpreTfvdFiniteClosedRelation`, `Analytic/CpNativeGpreTfvdCutoffCompatibility`, `Analytic/CpNativeGpreTfvdProjectiveAnalysis`, `Analytic/CpNativeGpreTfvdAnalysis`, `Analytic/CpNativeGpreTfvdVisiblePencil`, `Analytic/CpNativeGpreTfvdGenuineCompression` |
| Orçamentos e síntese | `Analytic/CpFiniteGenuineAngularGreenBudget`, `Analytic/CpFiniteGenuineOneSidedGreenBudget`, `Analytic/CpGenuineSecondDifferenceIdentity`, `Analytic/CpFiniteScalarSynthesis`, `Analytic/CpFiniteScalarSynthesisSummationByParts`, `Analytic/CpFiniteScalarSynthesisClosedDefectObstruction` |

`Carry/Shift` fornece `mulShift` e a comutação `mulShift_comm`. `Logic/Status` fornece o tipo `EvidenceStatus`, usado para distinguir os estatutos documentais dos enunciados; ele não altera os objetos matemáticos acima.

## 44. Assinatura matemática final

A formalização ativa pode ser resumida pelas seguintes identidades estruturais:

$$
\boxed{\; d_p^{\mathrm{eff}}(n)=v_p(c_p(n)) \;}
$$
`effectiveDepth_eq_centerDepth`

$$
\boxed{\; \alpha_{p,k}^2=p^{-k} \;}
$$
`criticalAmplitude_sq_eq_mass`

$$
\boxed{\; \mathcal N_p(\sigma)^2=1 \iff \sigma=\frac12 \;}
$$
`branchNormSq_eq_one_iff`

$$
\boxed{\; s(t)=\frac12+it, \quad \|u_t(n)\|=(n+1)^{-1/2} \;}
$$
`criticalLineParameter`, `norm_realSpectralState`

$$
\boxed{\; B_p[f](c)=\sum_{r=1}^{h_p}\Delta_r^2f(c) \;}
$$
`bracket_eq_saturatedBracket`

$$
\boxed{\; \mathcal B_p(s)=F_p(s)G(s) \;}
$$
`bracketedDirichletChart_eq_cpChartFactor_mul_genuineContinuation`

$$
\boxed{\; G_qB_q+R_q\operatorname{Tr}_q=I \;}
$$
`carryWeightedVerticalTfvd_identity`

$$
\boxed{\; \Phi_{p,M}(s)=R_p(\delta)\Re E_M(s)+\partial_{M,\mathbb R}^{\mathrm{br}}(s) \;}
$$
`finiteBracketCoupledCpGreenFlux_eq_radialDifference_mul_pairing`

$$
\boxed{\; \mathcal G_{p,q,L}(s)v\to\mathcal G_\infty(s)v=G(s)v \;}
$$
`finiteAlignedOrthogonalGenuineOperator_tendsto_apply`

$$
\boxed{\; \mathbf L_{p,q}(s)=0 \iff \Re(s)=\frac12 \;}
$$
`crossPrimeAlignedGreenLimitVector_eq_zero_iff_criticalDisplacement_eq_zero`

$$
\boxed{\; (\mathcal G_\infty(s)=0\land\mathbf L_{p,q}(s)=0) \iff (G(s)=0\land\Re(s)=\tfrac12) \;}
$$
`orthogonalGenuineGreenJointKernel_iff`

A leitura conceitual correspondente é:

- O carry fixa a profundidade e a amplitude;
- O parâmetro real gira a fase;
- O Genuine é o readout canônico;
- A TFVD conserva o estado e a proveniência;
- As câmeras convergem fortemente para `G(s)I`.
