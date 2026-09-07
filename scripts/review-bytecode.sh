#!/usr/bin/env bash
# Review compiler-generated Yul and labelled Asm under out/.
# Heimdall does not recover selectors for powdr-emitted EQ; ISZERO; JUMPI dispatch.
# Prefer out/<C>.runtime.yul and out/<C>.runtime.asm over heimdall decompilation.
#
# Usage: scripts/review-bytecode.sh [Counter|Token|Vault|Amm|all]
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="${HOME}/.foundry/bin:${PATH}"

CONTRACTS=(Counter Token Vault Amm)
TARGET="${1:-all}"

if [[ ! -f out/Token.runtime.yul ]]; then
  echo "==> artifacts missing; running export"
  scripts/export_bytecode.sh >/dev/null
fi

run_heimdall() {
  local name="$1"
  local hex="out/${name}.runtime.hex"
  local abi="out/${name}.abi.json"
  local out="out/heimdall/${name}"
  if ! command -v heimdall >/dev/null 2>&1; then
    echo "  skip heimdall (not installed)"
    return 0
  fi
  if [[ ! -f "$hex" ]]; then
    return 0
  fi
  mkdir -p "$out"
  # Heimdall does not recover selectors for powdr-emitted EQ; ISZERO; JUMPI dispatch.
  heimdall decompile "$(cat "$hex")" -o "$out" --include-yul -a "$abi" -d 2>/dev/null || true
  heimdall disassemble "$(cat "$hex")" -o print > "$out/disasm.txt" 2>/dev/null || true
  echo "  heimdall → $out (selectors not recovered; see ${name}.runtime.asm)"
}

review_one() {
  local name="$1"
  echo "==> $name"
  for f in runtime.yul deploy.yul runtime.asm runtime.hex; do
    local p="out/${name}.${f}"
    if [[ -f "$p" ]]; then
      echo "  $p  $(wc -l < "$p") lines"
    else
      echo "  missing $p"
    fi
  done
  if [[ -f "out/${name}.runtime.yul" ]]; then
    echo "  --- runtime.yul (head) ---"
    head -n 20 "out/${name}.runtime.yul"
  fi
  if [[ -f "out/${name}.runtime.asm" ]]; then
    echo "  --- runtime.asm (head) ---"
    head -n 20 "out/${name}.runtime.asm"
  fi
  run_heimdall "$name"
}

case "$TARGET" in
  Counter|Token|Vault|Amm) review_one "$TARGET" ;;
  all)
    for c in "${CONTRACTS[@]}"; do review_one "$c"; done
    ;;
  *)
    echo "Usage: $0 [Counter|Token|Vault|Amm|all]" >&2
    exit 1
    ;;
esac
