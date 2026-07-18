# Checkpoint 0.2.0 — Genuine first

Data: 2026-07-18.

## Resultado matematico codificado

1. Lei abstrata finita, sobre qualquer anel comutativo:

   ```text
   canal direto - canal bracketado = centros sobreviventes.
   ```

2. Instancias literais da lei para as cameras C2 e Cp.

3. Ponte combinatoria C2:

   ```text
   pernas impares n >= 3  equiv  incidencias (centro multiplo de 4, perna).
   ```

4. Ponte de profundidade C2:

   ```text
   max(v_2(n-1), v_2(n+1)) = v_2(centro escolhido).
   ```

Esses itens explicam por que o mesmo peso de carry acompanha uma perna no
canal direto e a ocorrencia correspondente no bracket. Eles nao dependem de
zeros conhecidos, zeta, limite infinito nem linguagem espectral.

## Estado epistemico

- Os arquivos nao contem `sorry` nem `axiom` local.
- A auditoria estatica de imports e scripts foi preparada.
- Os lemas permanecem `LEAN_STATEMENT`, nao `KERNEL_CHECKED`.
- O Lean e a mathlib foram baixados, mas o sandbox interrompe o executavel
  antes da elaboracao com `failed to locate application`.

## Proximo corte

1. fazer o kernel aceitar integralmente este checkpoint;
2. provar a reindexacao ponderada finita C2, incluindo a fronteira da caixa;
3. construir o representante balanceado unico modulo primo impar;
4. repetir a reindexacao e a igualdade de profundidade para Cp;
5. somente entao introduzir `n^(-s)`, series e caudas.

Hilbert--Polya e o operador projetivo continuam preservados em
`CPFormal.ResearchReserve`, fora do nucleo ativo.
