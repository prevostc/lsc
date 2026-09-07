#!/usr/bin/env bash
# Review compiler-generated Yul, labelled Asm, and heimdall Solidity under out/.
# Prefer out/<C>.runtime.yul / .runtime.asm for the compiler view; out/<C>.sol
# is heimdall's recovered Solidity (selectors with a 0x00 high byte stay missing).
#
# Usage: scripts/review-bytecode.sh [Counter|Token|Vault|Amm|all]
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="${HOME}/.foundry/bin:${HOME}/.bifrost/bin:${PATH}"

CONTRACTS=(Counter Token Vault Amm)
TARGET="${1:-all}"
# shellcheck source=heimdall_decompile.sh
source scripts/heimdall_decompile.sh

if [[ ! -f out/Token.runtime.yul ]]; then
  echo "==> artifacts missing; running export"
  scripts/export_bytecode.sh >/dev/null
fi

run_heimdall() {
  HEIMDALL_NOTICE_PREFIX="  " lsc_heimdall_decompile "$1"
  local heimdall="${HEIMDALL:-${HOME}/.bifrost/bin/heimdall}"
  if [[ ! -x "$heimdall" ]]; then
    heimdall="$(command -v heimdall 2>/dev/null || true)"
  fi
  if [[ -n "$heimdall" && -x "$heimdall" && -f "out/${1}.runtime.hex" ]]; then
    mkdir -p "out/heimdall/${1}"
    "$heimdall" disassemble "out/${1}.runtime.hex" -o print \
      > "out/heimdall/${1}/disasm.txt" 2>/dev/null || true
  fi
}

review_one() {
  local name="$1"
  echo "==> $name"
  for f in runtime.yul deploy.yul runtime.asm runtime.hex sol decompiled.yul; do
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
  if [[ -f "out/${name}.sol" ]]; then
    echo "  --- ${name}.sol (head) ---"
    head -n 30 "out/${name}.sol"
  fi
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
