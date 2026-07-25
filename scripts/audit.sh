#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

if [[ -x "$PWD/.elan/bin/lake" ]]; then
  export ELAN_HOME="$PWD/.elan"
  export PATH="$ELAN_HOME/bin:$PATH"
fi

if grep -RInE '^[[:space:]]*(axiom|sorry|admit)\b|:=[[:space:]]*by[[:space:]]+(sorry|admit)\b' \
  --include='*.lean' CPFormal CPFormal.lean; then
  echo "Falha: foi encontrado axiom/sorry/admit em codigo Lean." >&2
  exit 1
fi

if ! command -v lake >/dev/null 2>&1; then
  echo "Falha: lake nao esta instalado ou nao esta no PATH." >&2
  exit 2
fi

lake update
lake build

echo "Auditoria concluida: build integral sem axiom/sorry/admit local."
