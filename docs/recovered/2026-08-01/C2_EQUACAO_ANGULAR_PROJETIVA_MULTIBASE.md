# Equação Angular Projetiva Multibase

## Das câmeras primas ortogonais ao operador de síntese e ao gargalo Genuine

Escavando até o fundo, a intuição estava certa — mas encontramos uma distinção decisiva:

\[
\boxed{
\text{existe uma equação angular projetiva multibase,}
}
\]

porém ela contém duas ortogonalidades diferentes e dois operadores diferentes. Misturá-los daria a impressão de uma prova que ainda não existe.

O nome mais preciso seria:

\[
\boxed{
\text{equação de incidência angular projetiva multibase}
}
\]

em um espaço de Hilbert ponderado.

## 1. O mecanismo completo em uma figura

```text
                         RAMO ANGULAR
n^{-s} ── fases primas ── bracket C_p ── correntes z_p(s)
                                              │
                                              ▼
                                    ⊕_p H_{p,w}
                                              │
                                    projeção de síntese
                                              │
                                              ▼
                                           ζ(s)


                         RAMO TRANSVERSAL
n^{-1/2-δ-it} - n^{-1/2-it}
                  │
                  ▼
          perfil relativo R_{δ,t}
                  │
          curvatura + Hardy + frame U
                  │
                  ▼
          pressão 𝔐R_{δ,t}

PONTE QUE FALTA:
projeção angular nula  ──────────►  pressão transversal nula
       ζ(s)=0                         δ=0
```

O ramo superior detecta zeros.

O ramo inferior detecta saída da linha crítica.

A prova final precisaria ligar os dois.

---

## 2. A camada microscópica: o que realmente gira

Escrevendo

\[
s=\frac12+\delta+it,
\]

temos

\[
n^{-s}
=
n^{-1/2}\,n^{-\delta}\,e^{-it\log n}.
\]

Pela fatoração única,

\[
\log n=\sum_p v_p(n)\log p,
\]

portanto

\[
e^{-it\log n}
=
\prod_{p\mid n}
e^{-itv_p(n)\log p}.
\]

Assim, cada inteiro não possui uma fase prima única. Ele carrega um acorde:

\[
\boxed{
\theta_t(n)
=
-t\sum_pv_p(n)\log p.
}
\]

As fases microscópicas são

\[
\theta_{p,t}(n)=-t\,v_p(n)\log p.
\]

Mas elas ainda não são os ângulos das câmeras. Elas são as rotações internas que produzirão as correntes observadas pelas câmeras depois do bracket.

Para o transporte vertical normalizado,

\[
V_{p,\delta,t}
=
p^{-\delta}e^{-it\log p}S_p,
\]

vale

\[
\|V_{p,\delta,t}\|
=
p^{-\delta}.
\]

Logo:

\[
\delta=0
\quad\Longrightarrow\quad
V_{p,0,t}=e^{-it\log p}S_p
\]

é unitário em todas as verticais primas simultaneamente.

Portanto a frase correta é:

\[
\boxed{
\Re(s)=\frac12
\text{ fixa a neutralidade radial dos transportes atômicos.}
}
\]

Ela não garante que a norma da corrente depois do bracket seja constante em \(t\), porque o bracket não precisa comutar com o gerador de fase.

---

## 3. A câmera \(C_p\): de fase atômica para curvatura local

Para um primo ímpar \(p\), com

\[
h_p=\frac{p-1}{2},
\]

a câmera utiliza centros \(pm\) e pares simétricos \(pm-j,pm+j\). Sua coordenada local é

\[
\boxed{
J_{p,m,j}(s)
=
(pm-j)^{-s}
-
2(pm)^{-s}
+
(pm+j)^{-s}.
}
\]

Isso é uma segunda diferença:

\[
J_{p,m,j}(s)=\Delta_j^2f_s(pm),
\qquad
f_s(n)=n^{-s}.
\]

Portanto a câmera não fotografa diretamente as fases primas. Ela fotografa a curvatura discreta do campo complexo \(n^{-s}\).

A carta completa é

\[
\Phi_p(s)
=
E_p(s)
+
\sum_{m\ge1}\sum_{j=1}^{h_p}J_{p,m,j}(s),
\]

com a semente finita

\[
E_p(s)=\sum_{n=1}^{h_p}n^{-s}.
\]

O fator de calibração é

\[
F_p(s)=1-p^{1-s}.
\]

Então, onde vale a continuação das cartas,

\[
\boxed{
\frac{\Phi_p(s)}{F_p(s)}=\zeta(s).
}
\]

Esse fator não é arbitrário. Ele vem do operador literal de carry

\[
D_p=I-pS_p,
\]

pois a síntese de Dirichlet satisfaz

\[
\mathcal M_s(D_px)
=
(1-p^{1-s})\mathcal M_s(x).
\]

No interior da faixa crítica \(0<\sigma<1\), \(F_p(s)\neq0\), porque

\[
|p^{1-s}|=p^{1-\sigma}>1.
\]

---

## 4. Por que o bracket fornece uma boa câmera

A segunda diferença melhora a cauda. Para \(c=pm\),

\[
\Delta_j^2f_s(c)
\sim
j^2s(s+1)c^{-s-2}.
\]

Assim,

\[
J_{p,m,j}(s)=O(m^{-\sigma-2}),
\]

e a cauda depois de \(M\) satisfaz

\[
\sum_{m>M}J_{p,m,j}(s)
=
O(M^{-\sigma-1}).
\]

Na linha crítica:

\[
\boxed{
\text{cauda}=O(M^{-3/2}).
}
\]

Isso explica duas observações numéricas:

- o deslocamento dos mínimos finitos cai aproximadamente como \(M^{-3/2}\);
- como o score angular usa o módulo ao quadrado, no zero ele cai como

\[
\boxed{
\mathscr A_M(\rho)=O(M^{-3}).
}
\]

---

## 5. A primeira ortogonalidade: separação de registros

O espaço multibase é um somatório direto:

\[
\boxed{
\mathcal H_{\mathrm{MB}}
=
\bigoplus_{p\in\mathcal P}\mathcal H_p.
}
\]

Se \(\iota_p\) coloca uma corrente no bloco da câmera \(p\), então

\[
\langle\iota_pu,\iota_qv\rangle=0
\qquad(p\neq q).
\]

Essa ortogonalidade é construída para impedir que câmeras diferentes se cancelem antes de medirmos suas energias:

\[
\left\|
\bigoplus_p z_p
\right\|^2
=
\sum_p\|z_p\|^2.
\]

Ela não afirma que

\[
e^{-it\log p}
\quad\text{e}\quad
e^{-it\log q}
\]

formem \(90^\circ\) no plano complexo.

Essa é a interpretação literal da nota:

> Primeiro colocamos cada câmera num registro ortogonal; somente depois autorizamos a síntese coerente.

Quando sintetizamos,

\[
\left|\sum_pa_p\right|^2
=
\sum_p|a_p|^2
+
2\operatorname{Re}
\sum_{p<q}a_p\overline{a_q}.
\]

Ou seja: os termos de interferência são deliberadamente reintroduzidos apenas no mostrador final.

Portanto:

\[
\boxed{
\text{ortogonalidade dos blocos}
\neq
\text{ortogonalidade das fases primas}.
}
\]

Chamaremos essa primeira noção de:

\[
\boxed{
\text{ortogonalidade de registros multibase}.
}
\]

---

## 6. A segunda ortogonalidade: o plano cego da síntese

Reunimos as sementes e correntes normalizadas numa única corrente:

\[
z(s)
=
\bigoplus_{p,e}
z_{p,e}(s),
\]

com

\[
z_{p,e}(s)
=
\frac{\text{coordenada local}_{p,e}(s)}
{|\mathcal P|F_p(s)}.
\]

Sua síntese é

\[
S(z)=\sum_ez_e.
\]

Consequentemente,

\[
\boxed{
S(z(s))
=
\frac1{|\mathcal P|}
\sum_{p\in\mathcal P}\frac{\Phi_p(s)}{F_p(s)}
=
\zeta(s).
}
\]

O núcleo da síntese é o plano cego:

\[
\ker S
=
\{z:S(z)=0\}.
\]

O zero é exatamente a condição

\[
\boxed{
z(s)\in\ker S,
\qquad
z(s)\neq0.
}
\]

O vetor completo não desaparece. Somente sua componente visível pela síntese desaparece.

---

## 7. A correção importante: o observador constante só funciona no truncamento

No corte finito com \(N_M\) coordenadas, o operador atual usa

\[
e_M=\frac1{\sqrt{N_M}}(1,\ldots,1)
\]

e

\[
\mathscr A_M(s)
=
\frac{|\langle e_M,z_M(s)\rangle|^2}
{\|z_M(s)\|^2}
=
\frac{|\sum_ez_e(s)|^2}
{N_M\sum_e|z_e(s)|^2}.
\]

Isso é um cosseno angular perfeitamente legítimo em dimensão finita.

Mas existe um problema no limite:

\[
N_M\longrightarrow\infty,
\]

e o campo constante não pertence ao \(\ell^2\) infinito.

Fora dos zeros, acontece artificialmente:

\[
|\sum_ez_e|\longrightarrow|\zeta(s)|>0,
\]

\[
\sum_e|z_e|^2\longrightarrow E(s)>0,
\]

mas

\[
\mathscr A_M(s)
\sim
\frac{|\zeta(s)|^2}{N_ME(s)}
\longrightarrow0.
\]

Logo, no score euclidiano cru, todo ponto pareceria assintoticamente ortogonal.

Portanto:

\[
\boxed{
\mathscr A_M
\text{ é um excelente scanner finito, mas não é ainda o ângulo infinito.}
}
\]

---

## 8. O espaço infinito correto: observador de Riesz

Para uma coordenada na escala \(r_e\), defina

\[
\boxed{
w_e=r_e\log^2(er_e)
=
r_e(1+\log r_e)^2.
}
\]

O espaço é

\[
\mathcal H_w
=
\left\{
z:
\sum_ew_e|z_e|^2<\infty
\right\},
\]

com produto interno

\[
\langle u,v\rangle_w
=
\sum_ew_e\overline{u_e}v_e.
\]

A direção da síntese passa a ser o vetor de Riesz

\[
\boxed{
k_e=\frac1{w_e}.
}
\]

De fato,

\[
\langle k,z\rangle_w
=
\sum_ew_e\frac1{w_e}z_e
=
\sum_ez_e
=
S(z).
\]

Além disso,

\[
\|k\|_w^2
=
\sum_e\frac1{w_e}
<\infty,
\]

porque a cauda é comparável a

\[
\sum_m\frac1{m\log^2m}.
\]

Simultaneamente, como

\[
J_{p,m,j}(s)=O(m^{-\sigma-2}),
\]

temos

\[
\sum_m
m\log^2(em)|J_{p,m,j}(s)|^2
\ll
\sum_m
m^{-2\sigma-3}\log^2(em),
\]

que converge em toda a faixa crítica.

Agora a síntese é um funcional contínuo genuíno.

---

## 9. O operador angular projetivo correto

A projeção ortogonal sobre a direção de síntese é

\[
\boxed{
P_{\mathrm{syn}}z
=
\frac{\langle k,z\rangle_w}{\|k\|_w^2}\,k.
}
\]

A energia visível é

\[
\|P_{\mathrm{syn}}z\|_w^2
=
\frac{|\langle k,z\rangle_w|^2}{\|k\|_w^2}.
\]

Portanto o score angular infinito é

\[
\boxed{
\mathscr A_w(s)
=
\frac{\|P_{\mathrm{syn}}z(s)\|_w^2}
{\|z(s)\|_w^2}
=
\frac{|\zeta(s)|^2}
{\|k\|_w^2\|z(s)\|_w^2}.
}
\]

Defina

\[
\boxed{
\Theta_w(s)
=
\arccos
\frac{|\langle k,z(s)\rangle_w|}
{\|k\|_w\|z(s)\|_w}.
}
\]

Então

\[
\boxed{
\mathscr A_w(s)=\cos^2\Theta_w(s).
}
\]

E a equação angular fica:

\[
\boxed{
\zeta(s)=0
\iff
\mathscr A_w(s)=0
\iff
\Theta_w(s)=\frac\pi2.
}
\]

Essa é exatamente uma geometria de raios: multiplicar \(z\) por qualquer \(\lambda\neq0\) não muda \(\mathscr A_w\). A construção vive em espaço projetivo complexo e usa o ângulo Hermitiano entre raios — a mesma estrutura subjacente à geometria de Fubini–Study, salvo convenções de normalização do ângulo. Ver [Brody–Hughston](https://arxiv.org/abs/quant-ph/9906086) e [Ashtekar–Schilling](https://arxiv.org/abs/gr-qc/9706069).

O nome rigoroso da condição é:

\[
\boxed{
[z(s)]
\in
\mathbb P(k^\perp).
}
\]

Isto é, o raio da corrente encontra o hiperplano projetivo cego da síntese.

Então:

\[
\boxed{
\text{é uma ortogonalidade projetiva hermitiana induzida pela síntese.}
}
\]

---

## 10. Por que “projetiva” é mais profundo que “normalizada”

Não é apenas porque dividimos por normas.

O objeto matemático relevante não é o vetor \(z\), mas sua direção:

\[
[z]
=
\{\lambda z:\lambda\in\mathbb C^\times\}.
\]

A fase global e a escala global são descartadas. O que permanece é:

- a direção da corrente;
- sua incidência com o hiperplano \(\ker S\);
- seu ângulo em relação ao observador \(k\).

Assim, o zero não significa “vetor zero”. Significa:

\[
\boxed{
\text{um raio ativo entrou no hiperplano cego.}
}
\]

Essa formulação é mais precisa que simplesmente dizer “as fases se cancelaram”.

---

## 11. Cada câmera também tem seu próprio ângulo

Para cada bloco \(p\), existe um vetor de Riesz \(k_p\) e uma projeção

\[
P_pz_p
=
\frac{\langle k_p,z_p\rangle}{\|k_p\|^2}k_p.
\]

O ângulo local é

\[
\cos^2\Theta_p(s)
=
\frac{|\langle k_p,z_p(s)\rangle|^2}
{\|k_p\|^2\|z_p(s)\|^2}.
\]

Como

\[
\langle k_p,z_p(s)\rangle
=
\frac{\Phi_p(s)}{F_p(s)}
=
\zeta(s),
\]

num zero exato temos

\[
\boxed{
P_pz_p(\rho)=0
\quad\text{para toda câmera }p.
}
\]

Isso traz uma correção conceitual forte:

\[
\boxed{
\text{o zero infinito não é produzido por uma câmera cancelando outra.}
}
\]

Cada câmera individualmente já sintetiza o mesmo zero. O cancelamento decisivo ocorre dentro de cada câmera, entre suas sementes, centros e raios.

As câmeras múltiplas são valiosas porque conservam diferentes decomposições internas da mesma corrente antes do colapso escalar.

Depois da soma local, elas são escalarmente redundantes:

\[
F_q\Phi_p=F_p\Phi_q.
\]

---

## 12. A equação angular das alturas \(\gamma\)

Na linha crítica, definimos a curva projetiva

\[
t\longmapsto
[z(1/2+it)].
\]

As alturas dos zeros são os instantes em que essa curva encontra o hiperplano cego:

\[
\boxed{
\gamma:
\quad
[z(1/2+i\gamma)]
\in
\mathbb P(k^\perp).
}
\]

Equivalentemente,

\[
\boxed{
\Theta_w(1/2+i\gamma)=\frac\pi2.
}
\]

Então a frase intuitiva pode ser refinada para:

\[
\boxed{
\text{a linha crítica fixa a neutralidade radial;}
\quad
\gamma\text{ resolve a incidência angular projetiva.}
}
\]

Mas não são ângulos dois a dois entre primos. \(\gamma\) é o instante em que a corrente completa — depois das fases, brackets, centros, raios e calibrações — fica ortogonal à direção da síntese.

---

## 13. Multiplicidade do zero vira ordem de contato angular

Se

\[
\rho=\frac12+i\gamma
\]

é um zero simples, então

\[
\zeta\left(\frac12+it\right)
=
i\zeta'(\rho)(t-\gamma)
+
O((t-\gamma)^2).
\]

Como o denominador angular é positivo e suave em \(\gamma\),

\[
\boxed{
\mathscr A_w(1/2+it)
=
\frac{|\zeta'(\rho)|^2}
{\|k\|_w^2\|z(\rho)\|_w^2}
(t-\gamma)^2
+
O(|t-\gamma|^3).
}
\]

Portanto um zero simples produz um vale quadrático.

Mais geralmente, se o zero possui multiplicidade \(m\),

\[
\boxed{
\mathscr A_w(s)
\asymp
C|s-\rho|^{2m}.
}
\]

Geometricamente:

\[
\boxed{
\text{a multiplicidade do zero é a ordem de contato da curva projetiva com o hiperplano cego.}
}
\]

Essa é uma das leituras mais fortes que a formulação angular oferece.

---

## 14. O teste ponderado confirmou o mecanismo

Refizemos a auditoria usando o observador de Riesz ponderado.

No corte \(M=8192\):

| Ponto | \(\mathscr A_w\) | Ângulo |
|---|---:|---:|
| \(\gamma_1=14.134725\ldots\) | \(2.653\times10^{-15}\) | \(89.999997^\circ\) |
| \(t=15\) | \(2.713\times10^{-3}\) | \(87.014^\circ\) |
| \(t=17\) | \(1.324\times10^{-2}\) | \(83.394^\circ\) |

O fato de ângulos genéricos ainda serem grandes não é estranho em dimensão alta. O conteúdo matemático não é “ângulo grande”, mas

\[
\Theta=\frac\pi2
\]

exatamente, junto da taxa de aproximação.

Na varredura cega

\[
10\le t\le50.5,
\]

o score ponderado encontrou exatamente os dez primeiros vales esperados. Refinando com \(M=2048\), o maior erro contra as alturas de referência foi

\[
1.42\times10^{-5}.
\]

Também observamos:

- no primeiro zero, \(\mathscr A_w\) cai aproximadamente por um fator \(1/8\) quando \(M\) dobra, compatível com \(M^{-3}\);
- fora dos zeros, \(\mathscr A_w\) estabiliza num valor positivo;
- o score euclidiano antigo cai como \(1/N_M\) mesmo fora dos zeros.

Portanto o score ponderado é o candidato correto ao operador angular infinito.

---

## 15. A métrica não é totalmente única

Existe uma sutileza importante.

O hiperplano

\[
\ker S
\]

e a condição

\[
S(z)=0
\]

são invariantes.

Mas o valor numérico do ângulo depende de:

- produto interno escolhido;
- peso \(w_e\);
- pesos externos das câmeras;
- normalização colocada em cada bloco.

Assim:

\[
\boxed{
\text{o zero e a incidência projetiva são canônicos;}
\quad
\text{o valor do ângulo fora do zero depende da métrica.}
}
\]

O peso

\[
w_e=r_e\log^2(er_e)
\]

é natural porque resolve simultaneamente:

- continuidade da síntese;
- finitude da energia;
- estabilidade com o truncamento.

Mas outros pesos admissíveis poderiam produzir ângulos numericamente diferentes, com o mesmo conjunto de zeros.

Para infinitas câmeras primas, também é necessário escolher pesos externos \(a_p\) com

\[
\sum_pa_p=1
\]

e

\[
\sum_p|a_p|^2\|k_p\|^2<\infty.
\]

O executável atual utiliza um conjunto finito de primos.

---

## 16. O frame de Parseval é outra projeção

O frame logarítmico usa

\[
\omega_p(n)
=
\frac{v_p(n)\log p}{\log n},
\qquad
\sum_{p\mid n}\omega_p(n)=1,
\]

e

\[
\mathcal A|n\rangle
=
\sum_{p\mid n}
\sqrt{\omega_p(n)}\,|p;n\rangle.
\]

Logo,

\[
\mathcal A^*\mathcal A=I.
\]

No manômetro de centros, o operador correspondente é

\[
(Uc)_{p,k}
=
\sqrt{\widetilde\omega_p(k)}c_k,
\]

com

\[
U^*U=I
\]

e

\[
P_{\mathrm{coh}}=UU^*.
\]

Essa projeção não é \(P_{\mathrm{syn}}\).

Temos, portanto:

1. \(P_{\mathrm{coh}}\): projeta o atlas sobre dados de câmeras que representam a mesma curvatura central;
2. \(P_{\mathrm{syn}}\): projeta a corrente sobre a direção escalar que produz \(\zeta\).

Essa distinção precisa permanecer explícita.

---

## 17. A linha crítica e os zeros são dois kernels distintos

Defina o perfil relativo

\[
R_{\delta,t}(n)
=
n^{-1/2-it}(n^{-\delta}-1).
\]

O manômetro transversal é

\[
\mathfrak M R_{\delta,t}
=
U\mathcal H R_{\delta,t},
\]

onde

\[
(\mathcal HR)(k)
=
k^{3/2}\log(ek)\Delta_1^2R(k).
\]

O resultado obtido é

\[
\boxed{
\mathfrak M R_{\delta,t}=0
\iff
\delta=0.
}
\]

Separadamente, o operador angular satisfaz

\[
\boxed{
P_{\mathrm{syn}}z(s)=0
\iff
\zeta(s)=0.
}
\]

Portanto existem dois conjuntos:

\[
\mathcal Z_{\mathrm{ang}}
=
\{s:P_{\mathrm{syn}}z(s)=0\},
\]

\[
\mathcal N_{\mathrm{rad}}
=
\{s:\mathfrak M R_{\delta,t}=0\}
=
\{\Re(s)=1/2\}.
\]

A afirmação desejada fica:

\[
\boxed{
\mathcal Z_{\mathrm{ang}}
\subseteq
\mathcal N_{\mathrm{rad}}.
}
\]

Ou, operacionalmente:

\[
\boxed{
P_{\mathrm{syn}}z(s)=0
\quad\Longrightarrow\quad
\mathfrak M R_{\delta,t}=0.
}
\]

Essa é a ponte exata que ainda falta.

---

## 18. Por que positividade não fecha a ponte

Se \(\delta\neq0\), sabemos que

\[
\|\mathfrak M R_{\delta,t}\|>0.
\]

Mas um vetor não nulo pode ser ortogonal a um observador:

\[
v\neq0,
\qquad
\langle k,v\rangle=0.
\]

Portanto

\[
\text{pressão positiva}
\]

não implica

\[
\text{projeção escalar não nula}.
\]

Esse foi exatamente o no-go encontrado no entrelaçador:

\[
\|j\|^2
=
\frac{|\langle k,j\rangle|^2}{\|k\|^2}
+
\|(I-P_k)j\|^2.
\]

Num zero,

\[
\langle k,j\rangle=0,
\]

mas pode restar toda a energia em

\[
(I-P_k)j.
\]

Então o zero não é ausência de energia. É energia completamente invisível à síntese.

---

## 19. A formulação projetiva do gargalo final

Considere a superfície projetiva

\[
\Sigma
=
\left\{
[z(1/2+\delta+it)]:
(\delta,t)\in\mathbb R^2
\right\}.
\]

Considere o hiperplano cego

\[
\mathcal H_{\mathrm{blind}}
=
\mathbb P(k^\perp).
\]

Os zeros são

\[
\Sigma\cap\mathcal H_{\mathrm{blind}}.
\]

A linha crítica é

\[
\delta=0.
\]

A afirmação final seria:

\[
\boxed{
\Sigma\cap\mathcal H_{\mathrm{blind}}
\subseteq
\{\delta=0\}.
}
\]

O manômetro prova que a superfície realmente se move quando \(\delta\neq0\). Mas ainda não prova que esse movimento possui componente normal ao hiperplano cego.

Em outras palavras:

\[
\boxed{
\text{o manômetro controla movimento;}
\quad
\text{a ponte precisa controlar movimento na direção visível.}
}
\]

---

## 20. Que tipo de identidade poderia fechar

A peça faltante não parece ser outra norma abstrata. Precisa ser uma identidade assinada de fluxo ou Green:

\[
\boxed{
0
=
2\delta\,\mathcal E(s)
+
\mathcal B_{\mathrm{atlas}}(s)
}
\]

válida quando o Genuine zera.

Se

\[
\mathcal E(s)>0
\]

e

\[
\mathcal B_{\mathrm{atlas}}(s)\longrightarrow0
\]

pela colagem/Stokes das câmeras, então

\[
0=2\delta\mathcal E(s)
\]

forçaria

\[
\delta=0.
\]

Projetivamente, isso equivaleria a mostrar que a derivada transversal da superfície \(\Sigma\) possui componente assinada contra a normal \(k\) do hiperplano cego.

---

## 21. Onde a formalização quebra hoje

A auditoria T14 confirma que o problema não é apenas numérico.

A agulha relativa foi formalizada e possui lower certificado. Mas várias coordenadas de centro do atlas CP ainda não têm theorem que as transporte ao canal C2 zero-equivalente ao Genuine.

O primeiro gap já aparece em

\[
k=3.
\]

Os centros \(5,6,7,9,\ldots\) também não são isolados pelo alvo C2 vigente; a carta \(p=5\), por exemplo, transporta apenas certas triplas com fingerprint \([1,3,1]\).

Por isso o status correto continua sendo:

```text
STOP_T14_BRIDGE_CP_C2_GAP
```

Analiticamente, as cartas normalizadas sintetizam \(\zeta\).

Formalmente, o manômetro transversal CP ainda não foi transformado numa peça literal do target C2/Genuine.

---

## 22. O que é realmente novo — e o que seria tautologia

Qualquer função escalar pode artificialmente ser escrita como coeficiente matricial:

\[
F(s)=\langle k,z(s)\rangle.
\]

Então “zero é ortogonalidade” sozinho seria quase tautológico.

O conteúdo não trivial desta construção está no que foi obtido:

- coordenadas aritméticas produzidas pelo carry;
- decomposição exata das fases em verticais primas;
- charts \(C_p\) que sintetizam o mesmo canal;
- segunda diferença que controla a cauda;
- frame de Parseval que abre câmeras sem duplicar massa;
- espaço ponderado onde síntese e corrente coexistem;
- observador de Riesz explícito;
- manômetro transversal com kernel exatamente \(\delta=0\);
- Hardy discreto controlando gradiente por curvatura;
- planura multibase e fronteira de Stokes.

Isso transforma uma representação formal numa arquitetura geométrica real.

Mas ainda não transforma a arquitetura numa prova de que todo zero possui \(\delta=0\).

---

## 23. Vocabulário fixado

Fixamos estes quatro termos:

\[
\boxed{
\begin{aligned}
\text{ortogonalidade de registros}
&:\quad \mathcal H_{\mathrm{MB}}=\bigoplus_p\mathcal H_p,\\[2mm]
\text{projeção angular de síntese}
&:\quad P_{\mathrm{syn}}z,\\[2mm]
\text{ortogonalidade projetiva hermitiana}
&:\quad [z]\in\mathbb P(k^\perp),\\[2mm]
\text{equação angular projetiva multibase}
&:\quad \mathscr A_w(s)=0.
\end{aligned}
}
\]

Devemos evitar dizer:

> As fases dos primos são ortogonais.

A frase correta é:

> As câmeras primas ocupam blocos ortogonais de registro. Cada bloco transforma as fases aritméticas numa corrente local. A síntese possui um vetor de Riesz, e um zero ocorre quando o raio da corrente multibase entra no hiperplano projetivo ortogonal a esse vetor.

## Síntese de chão de fábrica

Cada inteiro toca um acorde de primos.

Cada \(C_p\) é uma câmera que reorganiza esse acorde em pixels de curvatura.

O somatório direto impede que os pixels de câmeras diferentes sejam apagados cedo demais.

A projeção final pergunta:

\[
\text{“quanto dessa imagem aponta na direção que produz o escalar?”}
\]

Nas alturas \(\gamma\), a imagem continua cheia de atividade, mas cai exatamente no plano cego:

\[
\boxed{
\text{atividade local não nula}
+
\text{projeção escalar nula}.
}
\]

A linha crítica, por outro lado, é onde todos os zooms primos deixam de expandir ou contrair:

\[
\boxed{
\text{neutralidade radial simultânea}.
}
\]

Então chegamos ao entendimento completo do mecanismo:

\[
\boxed{
\begin{aligned}
\Re(s)=\frac12
&\quad\text{é a equação radial de neutralidade},\\
\gamma
&\quad\text{resolve a equação angular projetiva},\\
\zeta(s)=0\Rightarrow\Re(s)=\frac12
&\quad\text{é a ponte ainda aberta entre elas}.
\end{aligned}
}
\]
