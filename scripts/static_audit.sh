#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

if grep -RInE '^[[:space:]]*(axiom|sorry|admit)\b|:=[[:space:]]*by[[:space:]]+(sorry|admit)\b' \
  --include='*.lean' CPFormal CPFormal.lean; then
  echo "Falha: foi encontrado axiom/sorry/admit em codigo Lean." >&2
  exit 1
fi

obsolete_zero_api='nativeCarryRealOperatorZero_sigma_eq_half|nativeCarryRealOperatorZero_ne_of_sigma_ne_half|nativeCarryComplexOperatorZero_sigma_eq_half|nativeCarryComplexOperatorZero_ne_of_sigma_ne_half|GenuineZerosPromoteToNativeZeros|NativeCarryRealPlaneAdmissibleFiniteZero|NativeCarryRealPlaneAdmissibleBoundaryClosesAt'

if grep -RInE "${obsolete_zero_api}" --include='*.lean' CPFormal CPFormal.lean; then
  echo "Falha: a semantica obsoleta de zero nativo reapareceu na API Lean." >&2
  exit 1
fi

if sed -n \
    '/^def IsNativeCarryRealOperatorZero$/,+5p' \
    CPFormal/Analytic/CpNativeCarryRealOperatorZero.lean \
    | grep -q 'MassCompatible'; then
  echo "Falha: compatibilidade de massa nao pode integrar a definicao de zero nativo." >&2
  exit 1
fi

if ! sed -n \
    '/^def IsNativeCarryRealOperatorZero$/,+5p' \
    CPFormal/Analytic/CpNativeCarryRealOperatorZero.lean \
    | grep -q 'NativeCarryRealOperatorBoundaryClosesAt'; then
  echo "Falha: zero nativo deve permanecer fechamento literal da camera." >&2
  exit 1
fi

while IFS= read -r module; do
  path="${module//./\/}.lean"
  if [[ ! -f "$path" ]]; then
    echo "Falha: import local sem arquivo: $module ($path)" >&2
    exit 1
  fi
done < <(
  grep -RhoE '^import[[:space:]]+CPFormal\.[A-Za-z0-9_.]+' \
    --include='*.lean' CPFormal CPFormal.lean \
    | awk '{print $2}' \
    | sort -u
)

bash -n scripts/audit.sh scripts/static_audit.sh

echo "Auditoria estatica concluida: imports locais resolvidos; sem axiom/sorry/admit local."
echo "Aviso: isto nao substitui ./scripts/audit.sh nem a verificacao pelo kernel Lean."
