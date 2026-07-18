# Caixa de ideias

Este arquivo guarda a linguagem geometrica antes de comprimi-la num enunciado.
Uma ideia pode gerar mais de um candidato formal. Nenhum candidato e escolhido
sem conferir que preserva a visao original.

## V-001 — horizontal de uma base como vertical de outra

Frase de origem:

> A horizontal de uma base e a vertical de outra base.

Leituras formais candidatas:

1. Para um primo `p`, a coordenada horizontal de `n` e o vetor das valuacoes
   `v_q(n)` com `q != p`.
2. Um deslocamento que muda o residuo em base `p` pode ser um deslocamento
   multiplicativo por `q` em outra torre.
3. A massa logaritmica horizontal relativa a `p` e
   `sum_{q != p} v_q(n) log q`.
4. Uma aresta horizontal do atlas `C_p` coincide com uma aresta vertical em
   algum bloco `C_q`, depois de uma reindexacao.

Teste necessario: escolher um inteiro concreto, por exemplo `n=2^a 3^b 5^c`,
e dizer qual objeto e chamado de horizontal em cada base. Isso separara as
quatro leituras.

Estado: `VISION`, promissora e ainda nao univoca.

## V-002 — XOR entre pares de gemeos

Frase de origem:

> Fazer XOR entre par de gemeos.

Possiveis operandos:

- os bits dos inteiros `c-r` e `c+r`;
- os indicadores de carry de cada perna;
- os conjuntos de profundidades onde ocorreu carry;
- os vetores de paridade das valuacoes primas;
- os sinais/fases das duas correntes.

Possiveis saidas:

- primeiro nivel em que apenas uma perna carrega;
- mascara de divergencia das torres;
- paridade da profundidade;
- seletor que cancela pernas iguais e preserva a diferenca.

Antes do Lean precisamos fixar uma tabela com quatro colunas:
`perna esquerda`, `perna direita`, `XOR esperado`, `interpretacao geometrica`.

Estado: `VISION/AMBIGUOUS`. Nao descartada e nao formalizada prematuramente.

## V-003 — bracket como eliminador de pernas

Traducao inicial:

- unidade: `centeredSecondDifference`;
- agregado: `saturatedBracket`;
- alvo finito: reindexar todas as pernas e provar que `direct - legs` deixa
  apenas centros, mais um termo de fronteira explicito.

Estado: traducao inicial implementada no nivel de grupo aditivo.

## Como adicionar uma ideia

Registrar a frase literalmente primeiro. Depois acrescentar candidatos,
exemplos e contraexemplos. A frase original nunca e substituida pela primeira
formalizacao proposta.
