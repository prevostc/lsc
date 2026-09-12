#!/usr/bin/env bash
# Enforce the LscSemantics / Lsc Lake split (lakefile.lean). No Lean needed.
#
# Fails if:
# - any file under Lsc/Lang, Lsc/Security, or Lsc/Util imports Lsc.Compiler.*
# - any file under Lsc/ imports Examples.* or Stdlib.*
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

status=0

scan() {
  local pattern="$1"
  shift
  if command -v rg >/dev/null 2>&1; then
    rg -n --glob '*.lean' "$pattern" "$@" || true
  else
    find "$@" -name '*.lean' -print | while IFS= read -r f; do
      grep -nE "$pattern" "$f" | sed "s|^|$f:|" || true
    done
  fi
}

hits="$(scan '^[[:space:]]*import[[:space:]]+Lsc\.Compiler(\.|[[:space:]]|$)' \
  Lsc/Lang Lsc/Security Lsc/Util)"
if [ -n "$hits" ]; then
  echo "layering: Lsc/Lang, Lsc/Security, Lsc/Util must not import Lsc.Compiler.*" >&2
  printf '%s\n' "$hits" >&2
  status=1
fi

hits="$(scan '^[[:space:]]*import[[:space:]]+(Examples|Stdlib)(\.|[[:space:]]|$)' Lsc)"
if [ -n "$hits" ]; then
  echo "layering: Lsc/ must not import Examples.* or Stdlib.*" >&2
  printf '%s\n' "$hits" >&2
  status=1
fi

if [ "$status" -ne 0 ]; then
  echo "error: library layering violated" >&2
  exit 1
fi
