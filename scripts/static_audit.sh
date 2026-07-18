#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

if grep -RInE '^[[:space:]]*(axiom|sorry)\b|:=[[:space:]]*by[[:space:]]+sorry\b' \
  --include='*.lean' CPFormal CPFormal.lean; then
  echo "Falha: foi encontrado axiom/sorry em codigo Lean." >&2
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

echo "Auditoria estatica concluida: imports locais resolvidos; sem axiom/sorry local."
echo "Aviso: isto nao substitui ./scripts/audit.sh nem a verificacao pelo kernel Lean."
