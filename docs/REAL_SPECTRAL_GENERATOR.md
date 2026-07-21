# Checkpoint 0.54 — gerador espectral real e mecanismo de persistência

## Separação entre gerador, órbita e ressonância Genuine

**Diretriz:** `GENUINE_FIRST`  
**Camada formal:** Lean 4, corte finito  
**Camada computacional:** laboratório reprodutível sem refinamento contínuo  
**Guardrail:** o parâmetro `t` da órbita não é autovalor do gerador diagonal

---

## 0. Correção conceitual necessária

A geometria crítica produz o estado

\[
\psi_t(n)=n^{-1/2}e^{-it\log n}.
\]

Existe um gerador diagonal natural

\[
L|n\rangle=\log n\,|n\rangle,
\qquad U_t=e^{-itL}.
\]

Entretanto, os papéis são diferentes:

\[
\boxed{\operatorname{Spec}(L_N)=\{\log 1,\ldots,\log N\}}
\]

no corte finito, enquanto `t` é o parâmetro real do grupo unitário `U_t`.
As alturas encontradas pelo scanner são valores para os quais um readout do
estado orbitado fecha:

\[
\boxed{\mathcal G(1/2+it)=0.}
\]

Portanto o nome rigoroso atual é **ressonância real do readout Genuine**. Para
promover `t` a espectro no sentido estrito será necessário construir um pencil
ou problema de bordo cuja equação característica seja esse fechamento, ou uma
linearização auto-adjunta equivalente.

Essa distinção não enfraquece o resultado; ela impede identificar dois
espectros diferentes por linguagem.

---

## 1. Núcleo Lean do corte finito

O módulo

```text
CPFormal/Analytic/CpRealSpectralGenerator.lean
```

introduz, para cada `N`, o Hilbert finito

\[
H_N=\ell^2(\{0,\ldots,N-1\};\mathbb C).
\]

A frequência do índice `n` é

\[
\omega_n=\log(n+1).
\]

O gerador é

\[
(L_Nx)_n=\omega_n x_n.
\]

O kernel registra que `L_N` é simétrico e usa Hellinger–Toeplitz para o
empacotar como operador contínuo auto-adjunto em todo `H_N`.

Nos vetores canônicos,

\[
L_Ne_n=\log(n+1)e_n.
\]

Assim, os autovalores do gerador ficaram identificados explicitamente e não são
confundidos com as alturas de ressonância.

---

## 2. Grupo unitário finito

Defina

\[
u_n(t)=e^{-it\log(n+1)}.
\]

A evolução coordenada é

\[
(U_t^{(N)}x)_n=u_n(t)x_n.
\]

O Lean prova:

\[
U_0^{(N)}=I,
\qquad
U_{t+u}^{(N)}=U_t^{(N)}U_u^{(N)},
\]

bem como a preservação exata do produto interno. Portanto

\[
U_t^{(N)}:H_N\simeq_{\mathrm{unitário}}H_N.
\]

Nenhum zero ou dado numérico entra nessa prova.

---

## 3. Ressonância intrínseca

O predicado formal é

```lean
def IsRealSpectralResonance (t : ℝ) : Prop :=
  realSpectralGenuine t = 0
```

Para toda câmera prima ímpar `p`, o kernel transporta a identidade de cartas já
provada para

\[
\boxed{
\operatorname{IsRealSpectralResonance}(t)
\iff
\operatorname{bracketedDirichletChart}
  \left(p,\frac12+it\right)=0.
}
\]

Logo uma câmera não cria a ressonância. Ela reconhece o fechamento do mesmo
Genuine real-espectral.

---

## 4. Diagnóstico sem diluição dimensional

O score canônico do scanner é

\[
A_{K,M}(t)
=
\frac{|\sum_e z_e(t)|^2}
{N_{K,M}\sum_e|z_e(t)|^2}.
\]

Para separar o aprofundamento verdadeiro do fator `N`, o laboratório registra
também

\[
\boxed{
R_{K,M}(t)
=N_{K,M}A_{K,M}(t)
=\frac{|\sum_ez_e(t)|^2}{\sum_e|z_e(t)|^2}.
}
\]

Esse é o resíduo de visibilidade sem a diluição pela dimensão. A fração cega é

\[
1-A_{K,M}(t),
\]

e o ângulo com a direção observadora é

\[
\Theta_{K,M}(t)=\arccos\sqrt{A_{K,M}(t)}.
\]

O script

```text
experiments/c2_real_spectral_mechanism.py
```

reconstrói literalmente todas as coordenadas antes da síntese e audita:

- igualdade entre o score reconstruído e o scanner;
- energia visível, energia cega e ledger total;
- idempotência e autoadjunção numéricas da projeção constante;
- resultantes separadas de sementes e brackets;
- cosseno e razão de módulos do fechamento semente–bracket;
- visibilidade interna de cada câmera;
- alinhamento ou cancelamento dos restos entre câmeras.

---

## 5. Auditoria dos dez pontos do corte 1024

Na grade sem refinamento, para as câmeras `3,5,7,11`, o auditor foi aplicado
nos dez pontos publicados entre `10` e `50`.

O resultado reproduz o mecanismo relatado:

1. a energia total permanece estritamente positiva;
2. a fração cega é superior a `0.999999999998` em todos os pontos;
3. o cosseno semente–bracket é extremamente próximo de `-1`;
4. as câmeras individuais já possuem visibilidade muito pequena;
5. em oito pontos os restos das câmeras permanecem fortemente alinhados;
6. os pontos próximos de `30.4249` e `49.7738` apresentam participação
   inter-câmeras maior, compatível com a classificação “mista”.

Esses itens são **NUMÉRICOS EM CORTE FINITO**. Eles demonstram que o programa
mede um mecanismo coordenado; não certificam por si só uma raiz contínua nem um
limite infinito.

---

## 6. Protocolo de persistência

O laboratório de persistência acompanha cada mínimo somente em grades decimais
indexadas. Para cortes `M_1<...<M_r`, ele registra:

\[
(M_j,k_j,t_{k_j},A_j,R_j,E_j,\Theta_j).
\]

Também usa pontos de controle fixos entre candidatos. O expoente empírico é
obtido por regressão de

\[
\log R_M\approx c-\alpha\log M.
\]

A interpretação correta é:

- `α≈0` nos controles: aumentar o corte não fecha o readout;
- `α>0` nos candidatos: o resíduo sem diluição aprofunda;
- alternância no sinal dos deslocamentos de `t_M`: assinatura de bordo móvel;
- pequena dispersão entre atlas: câmeras diferentes reconhecem o mesmo evento.

O ajuste de potência é um resumo descritivo, não extrapolação certificada de
uma altura limite.

---

## 7. Próximo objeto infinito

O gerador candidato no Hilbert infinito é o operador de multiplicação maximal

\[
(Lx)_n=\log(n+1)x_n,
\]

com domínio

\[
D(L)=\left\{x\in\ell^2:
\sum_n\log^2(n+1)|x_n|^2<\infty\right\}.
\]

Os próximos gates formais são:

```text
NEEDS_MAXIMAL_LOG_MULTIPLICATION_OPERATOR
NEEDS_DENSE_DOMAIN_AND_CLOSED_GRAPH
NEEDS_SELF_ADJOINTNESS_OF_INFINITE_GENERATOR
NEEDS_UNITARY_GROUP_ON_L2
NEEDS_GENUINE_BOUNDARY_PENCIL
NEEDS_CHARACTERISTIC_VALUE_LINEARIZATION
```

O pencil de bordo deverá consumir a órbita crítica e satisfazer

\[
\mathfrak B(t)\psi_0=0
\iff
\mathcal G(1/2+it)=0,
\]

sem transformar essa equivalência em definição tautológica e preservando os
registros de semente, bracket, câmera e bordo até a última síntese.

---

## 8. Estatuto

```text
KERNEL-CHECKED
  gerador diagonal finito
  simetria e auto-adjunção finitas
  frequências log(n+1) nos vetores canônicos
  grupo unitário finito e lei de composição
  ressonância Genuine independente da câmera

NUMÉRICO REPRODUTÍVEL
  resíduo sem diluição
  decomposição visível/cega
  fechamento semente–bracket
  visibilidade por câmera
  alinhamento entre atlas
  persistência em cortes finitos

ABERTO
  gerador maximal infinito
  pencil/relação de bordo com t como valor característico
  certificação infinita das ressonâncias
```
