# Acordo de trabalho

## Divisao de papeis

O pesquisador traz:

- imagens geometricas;
- relacoes entre bases;
- analogias de carry, horizontal, vertical, centros e pernas;
- operacoes experimentais, como o XOR entre pares;
- objecoes quando a formalizacao deixou de representar a ideia.

O formalizador transforma cada entrada em:

1. dicionario preciso dos objetos envolvidos;
2. exemplos finitos que a afirmacao deve satisfazer;
3. contraexemplos procurados deliberadamente;
4. enunciado matematico com todas as hipoteses;
5. grafo de lemas menores;
6. implementacao Lean sem `sorry`;
7. estado epistemico registrado no ledger.

## Protocolo de traducao

Para cada nova visao, registramos:

- **Objetos:** quais sao as entradas e saidas?
- **Operacao:** o que muda e o que permanece?
- **Quantificadores:** vale para qual primo, base, centro e profundidade?
- **Fronteira:** o que acontece em zero, nos primeiros centros e nas caudas?
- **Versao finita:** qual afirmacao pode ser calculada exaustivamente?
- **Versao infinita:** qual limite, convergencia ou continuidade e necessario?
- **Papel na prova:** definicao, lema estrutural, detector numerico ou ponte RH?

Uma intuicao nao sera descartada por ainda nao vir formalizada. Ela fica como
`VISION` ou `AMBIGUOUS` ate obter uma traducao fiel.

## Regras contra circularidade

- Nao construir um operador a partir da lista dos gammas conhecidos.
- Nao provar apenas a correspondencia dos zeros que ja estao na linha.
- Nao usar a RH, nem uma forma equivalente, dentro da prova de
  autoadjunticidade.
- Nao chamar um parametro de autovalor sem produzir uma equacao
  `H psi = lambda psi` com dominio fixo.
- Nao promover verificacao numerica a teorema.
- Nao esconder uma ponte aberta dentro de uma typeclass, estrutura ou
  hipotese sem registra-la no ledger.

## Criterio de conclusao de um lema

Um lema esta concluido somente quando:

- o enunciado representa a ideia aprovada;
- nao contem hipoteses circulares;
- compila no toolchain fixado;
- nao usa `sorry` ou axiomas locais;
- possui identificador e dependencias no ledger.
