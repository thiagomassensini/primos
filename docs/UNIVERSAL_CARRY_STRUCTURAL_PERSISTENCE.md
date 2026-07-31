# Persistência estrutural universal do carry

## Estado de certificação

O núcleo matemático desta síntese foi verificado no commit
`6744f44bf0308af11952ef9e8629357c6be60fcf` pelo GitHub Actions, run
`30618216161`, job `91116286122`. A auditoria estática e
`lake build --wfail` terminaram com sucesso, cobrindo os imports ativos de
`CPFormal.lean`.

Esse commit é o *audited mathematical-source commit*: ele evita a
circularidade de tentar gravar num documento o SHA do próprio commit que
contém o documento. Depois da incorporação do PR #30, o workflow da
`v0.55.0` valida dinamicamente o `main` exato antes de criar a tag anotada e
a GitHub Release.

## Resultado central

O núcleo que permanece invariável não é um rótulo de câmera, a primalidade
da largura, uma coordenada complexa nem um cutoff. É a seguinte cadeia
tipada:

1. uma saturação posicional muda coordenadas e conserva valor;
2. a decomposição quociente–resto registra a saturação por um carry;
3. a massa uniforme do evento de carry é `b⁻ᵏ`;
4. sua amplitude quadrática é `b⁻ᵏ/²`, rigidamente selecionando
   `sigma = 1/2`;
5. a rotação real muda fase, mas não essa massa;
6. a segunda diferença comprime o estado em um resultante de câmera;
7. a geometria finita da câmera determina um fator explícito, sem alterar o
   núcleo analítico comum quando esse fator é regular;
8. a reconstrução Green–bracket–retorno conserva o estado completo, embora
   interior e bordo possam se redistribuir.

Isso é uma afirmação sobre a classe formalizada de sistemas posicionais,
câmeras saturadas e operadores associados. Não é uma afirmação de que todo
objeto de toda teoria matemática seja gerado por carry.

## Operador primitivo auditado

O pacote experimental usa, literalmente,

\[
\psi_t(n)=n^{-1/2}
  \bigl(\cos(-t\log n),\sin(-t\log n)\bigr)
\]

e

\[
\Delta_r\psi_t(c)
  =\psi_t(c-r)-2\psi_t(c)+\psi_t(c+r).
\]

Para uma largura natural `b ≥ 3`, com

\[
h_b=\left\lfloor\frac{b-1}{2}\right\rfloor,
\]

o resultante finito é

\[
R_{b,M}(t)=
\sum_{r=1}^{h_b}\psi_t(r)+
\sum_{m=1}^{M}\sum_{r=1}^{h_b}\Delta_r\psi_t(bm).
\]

Não existe transformação posterior ao bracket. A leitura adimensional

\[
\operatorname{score}
=\frac{\lVert R_{b,M}\rVert^2}
 {N\sum_e\lVert z_e\rVert^2}
\]

preserva os zeros finitos porque seu denominador é positivo, mas um score
pequeno não substitui o fechamento bruto `R = 0`.

## Formas normais finitas

Escreva

\[
P_Nf=\sum_{n=1}^{N}f(n),
\qquad
(D_df)(n)=f(dn).
\]

### Largura ímpar

Para toda largura ímpar `b ≥ 3`, prima ou composta,

\[
\boxed{
C_{b,M}f=P_{bM+h_b}f-b\,P_M(D_bf).
}
\]

Os pares em torno de cada centro ladrilham o prefixo inteiro sem lacunas. A
primalidade não participa dessa identidade.

Para `f(n)=n^{-s}`,

\[
C_{b,M}(s)
=H_{bM+h_b}(s)-b^{1-s}H_M(s).
\]

### Largura par natural

Se `b=2a ≥ 4`, então `h_b=a-1` e existe uma classe de meio passo que não
pertence aos pares da câmera:

\[
\boxed{
C_{b,M}f=
P_{bM+a-1}f-P_{2M}(D_af)-(b-2)P_M(D_bf).
}
\]

Ela registra exatamente:

- os meios de bloco `a,3a,\ldots,(2M-1)a`;
- os centros `b,2b,\ldots,Mb`;
- o bordo final do prefixo.

Logo uma câmera par não deve ser silenciosamente tratada como uma câmera
ímpar composta.

### Câmera alinhada C2

A câmera chamada `2` no scanner usa centros `4m`, semente `1` e raio `1`.
Portanto,

\[
\boxed{C_{2,M}^{\mathrm{alinhada}}=C_{4,M}}
\]

para toda função, cutoff e tempo. Os arquivos numéricos das câmeras 2 e 4
são duplicatas exatas do mesmo operador, com rótulos geométricos diferentes.

### Compostas ímpares

Para `a,b ≥ 3` ímpares,

\[
\boxed{
C_{ab,M}f=
C_{a,bM+h_b}f+
a\,C_{b,M}(D_af).
}
\]

No estado crítico real,

\[
R_{ab,M}(t)=
R_{a,bM+h_b}(t)+
\sqrt a\,\operatorname{Rot}(-t\log a)R_{b,M}(t).
\]

Exemplos:

\[
R_{9,M}
=R_{3,3M+1}
+\sqrt3\,\operatorname{Rot}(-t\log3)R_{3,M},
\]

\[
R_{15,M}
=R_{3,5M+2}
+\sqrt3\,\operatorname{Rot}(-t\log3)R_{5,M}.
\]

Isso é uma decomposição exata, não uma igualdade de câmeras no mesmo cutoff.
Ela explica estruturalmente por que a primalidade é dispensável na família
ímpar.

## Fatores de câmera

No semiplano de convergência absoluta, as formas finitas impõem

\[
C_{b,\infty}(s)=\Phi_b(s)\,\zeta(s),
\]

com

\[
\Phi_b(s)=
\begin{cases}
1-b^{1-s},
  & b\text{ ímpar},\\[2mm]
1-(b/2)^{-s}-(b-2)b^{-s},
  & b\text{ par}.
\end{cases}
\]

Para a C2 alinhada usa-se `Φ₄`. Nesse caso,

\[
\Phi_4(s)=
\bigl(1-2^{1-s}\bigr)\bigl(1+2^{-s}\bigr).
\]

Na linha crítica:

- se `b` é ímpar, `|b^(1-s)|=√b>1`, logo `Φ_b ≠ 0`;
- para `b=4`, os dois fatores acima são não nulos;
- para `b=2a≥6`, o canal central
  `(b-2)b^{-s}` domina estritamente a soma do canal unitário e do meio passo.

Consequentemente, após transportar a fatoração por continuação analítica, a
linha crítica possui o mesmo predicado de zero em toda câmera natural. A
passagem completa foi formalizada preservando o canal de meio passo:

\[
\operatorname{Chart}_b(s)
=\Phi_b(s)\operatorname{genuineContinuation}(s)
\]

para toda largura nativa `b ≥ 3` na faixa crítica. Quando
`Re(s)=1/2`, `Φ_b(s) ≠ 0`; portanto

\[
\operatorname{Chart}_b(s)=0
\quad\Longleftrightarrow\quad
\operatorname{genuineContinuation}(s)=0.
\]

A C2 alinhada participa por sua igualdade literal com a largura 4. A câmera
nativa literal de largura 2 é degenerada e não deve ser confundida com ela.
Essa equivalência é do limite analítico na linha crítica; não afirma que
algum cutoff finito zere exatamente, nem que os fatores pares sejam regulares
em toda a faixa.

## Relação com a ontologia da presença causal

A ontologia fornecida serve como disciplina lógica, não como ponte analítica
automática. Sua leitura concreta é:

- **distinção primitiva:** saturado versus não saturado;
- **mediação:** quociente, resíduo, carry e normalização;
- **persistência sem identidade:** a configuração muda, o valor permanece;
- **compressão:** soma, multiplicação e potência possuem certificados
  operacionais explícitos;
- **apresentação:** bases, câmeras e embalagem `R² ↔ ℂ` são vistas distintas;
- **presença observável:** uma leitura normalizada pode permanecer igual
  mesmo quando códigos e componentes internos diferem;
- **bordo:** qualquer informação retirada do interior reaparece como termo
  tipado de bordo, cauda ou defeito.

Essa interpretação é implementada pela interface `RestrictedCodec` e pelo
`ReadoutAtlas`. O teorema `minimal_view_invariance` preserva:

1. leitura normalizada;
2. predicado de fechamento;
3. ledger total `interior + boundary`.

Ele não afirma igualdade dos códigos nem igualdade componente a componente.

## Green, retorno e defeitos

Para toda base material `b ≥ 2`,

\[
q_b=b^{-1/2}
\]

é simultaneamente a amplitude crítica do carry na primeira profundidade e a
razão do operador vertical vestido.

O kernel já prova

\[
G_bB_b+R_b\operatorname{Tr}_b=I,
\]

\[
\operatorname{Tr}_bR_b=I,
\qquad
B_bR_b=0.
\]

Portanto interior e retorno podem mudar com a base, mas sua soma reconstrói o
mesmo estado.

O defeito Green do bordo livre não desaparece por definição. Ele é
exatamente o Wronskiano inicial:

\[
\mathcal D_{\mathrm{Green}}(x,y)
=\mathcal W_q(x,y).
\]

Do mesmo modo, o Richardson C2 não apaga o defeito conectado; ele cancela os
termos lineares e isola

\[
2K_{1/2}-K_1
=\frac12\,\varepsilon_p\varepsilon_q.
\]

Essas duas identidades são paralelas em estrutura — ambas preservam a
proveniência do que não foi absorvido pelo canal principal —, mas ainda não
são o mesmo operador.

## O que o pacote numérico prova e o que não prova

O arquivo recebido tem SHA-256

```text
2a1310ab71a5a7fb3a45a33e23f917dc7e3dff690020556ffa69befe07aa4428
```

Os hashes registrados dos scripts centrais coincidem com os arquivos:

```text
0006bcb248fa60216e93077cfc0d589d65eed49eddf6f916c680b1cf551c7b74
  native_carry_primitive_real_operator.py
acdde5473dc047aefa5e3927fd270267083f68bf8c462446f29f4f4ae5874028
  primitive_cutoff_convergence_test.py
```

Os dados dão evidência forte de coalescência:

- o spread dos mínimos cai de `2488,706 ns` em `M=8192` para
  `1,722 ns` em `M=1048576`;
- um ajuste global dá aproximadamente `M^-1.504`;
- no tempo congelado, as normas decaem com potência observada entre
  `1.49719` e `1.49965`;
- a cauda usada é
  `M^(-3/2) Rot(-t log M)`;
- as oito raízes linearizadas possuem span modelado de cerca de
  `9,95×10^-5 ns`.

Mas:

- nenhuma resultante finita é exatamente zero;
- a extrapolação impõe a ordem `3/2`;
- o limite ajustado no decimal congelado permanece entre aproximadamente
  `5×10^-13` e `3×10^-12`;
- os experimentos não aplicam `G`, `Tr`, retorno vertical nem calculam um
  Wronskiano;
- o cancelamento visível quase total convive com energia interna entre
  aproximadamente `5,6` e `10,6`, portanto leitura zero não implica estado
  zero sem coercividade;
- as câmeras 6, 7, 10, 13 e 14 não aparecem no teste longo;
- C2 e C4 são o mesmo dado, não duas confirmações independentes.

Os experimentos orientam os lemas corretos. A prova deve vir das identidades
finitas, da somabilidade das segundas diferenças, da continuação analítica e
da regularidade explícita dos fatores.

## Mapa Lean

Os módulos desta síntese são:

- `CPFormal.Logic.StructuralPersistence`
  - codecs restritos;
  - atlas de leituras;
  - transporte canônico;
  - ledger interior–bordo;
  - transporte com defeito explícito.
- `CPFormal.Analytic.CpNativeCarryFiniteCameraAlgebra`
  - formas normais finitas;
  - C2 igual a C4;
  - decomposição de compostas.
- `CPFormal.Analytic.CpNaturalCameraFactor`
  - fatores ímpar e par;
  - regularidade sem primalidade;
  - fatorização e regularidade crítica de C2/C4.
- `CPFormal.Analytic.CpNaturalEvenCameraRegularity`
  - dominação estrita do canal central;
  - não anulamento crítico dos fatores pares `b ≥ 6`.
- `CPFormal.Analytic.CpNaturalCameraAnalyticContinuation`
  - convergência e holomorfia para toda largura `b ≥ 2`;
  - limites fatorados ímpar e par em `Re(s)>1`;
  - identidade cruzada com a câmera 3 antes de qualquer divisão;
  - fatoração comum na faixa crítica;
  - equivalência de zeros na linha crítica para toda largura `b ≥ 3`;
  - C2 alinhada transportada pela largura 4.
- `CPFormal.Analytic.CpUniversalCarryStructuralPersistence`
  - certificado agregado de decomposição posicional;
  - conservação de valor;
  - herança causal direta e inversa;
  - massa e amplitude;
  - confinamento radial;
  - embalagem real–complexa;
  - TFVD Green–bracket–retorno;
  - Wronskiano de bordo;
  - defeito conectado C2.

## O que entendemos agora

A geometria finita não altera o núcleo analítico: ela seleciona um fator
explícito determinado pela paridade. Para toda largura nativa `b ≥ 3`, a
carta converge, é holomorfa e, na faixa crítica, é o produto desse fator pelo
mesmo `genuineContinuation`. Na linha `Re(s)=1/2`, todos os fatores são não
nulos. Logo todas as câmeras naturais, incluindo a C2 alinhada como largura
4, detectam exatamente o mesmo predicado de zero.

A primalidade pertence à apresentação histórica por resíduos balanceados,
não ao scanner saturado nativo. Isso estabelece independência da câmera para
a leitura analítica crítica. Não identifica a carta com o estado Green
completo, não elimina bordo ou defeito e não transforma cancelamento visível
em energia nula.

## Próximos teoremas

1. Provar a assíntota rotativa de cutoff
   `M^(-3/2-it)` a partir da segunda diferença, sem assumir sua ordem no
   extrapolador.
2. Classificar os zeros dos fatores pares fora da linha crítica, buscando
   equivalência de zeros em toda a faixa.
3. Construir um intertwiner explícito entre o resultante de câmera e o
   traço Green. Sem esse mapa, a semelhança entre fechamento de câmera e
   fechamento Green permanece uma direção de pesquisa.
4. Formular uma hipótese de observabilidade/coercividade, ou provar
   precisamente sua impossibilidade.
5. Relacionar o cumulante Richardson e o Wronskiano somente por um mapa
   tipado e um diagrama comutativo.
6. Instanciar a ontologia causal com os tipos concretos acima, mantendo
   separados estado, leitura, zero, energia, bordo e defeito.
