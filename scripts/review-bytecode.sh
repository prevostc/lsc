#!/usr/bin/env bash
# Review compiler-generated Yul, labelled Asm, and heimdall Solidity under
# Examples/<C>/compiled/. Prefer runtime.yul / runtime.asm for the compiler
# view; decompiled.sol is heimdall's recovered Solidity (selectors with a
# 0x00 high byte stay missing).
#
# Usage: scripts/review-bytecode.sh [Counter|Token|Vault|Amm|Cpamm|all]
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="${HOME}/.foundry/bin:${HOME}/.bifrost/bin:${PATH}"

CONTRACTS=(Counter Token Vault Amm Cpamm)
TARGET="${1:-all}"
# shellcheck source=heimdall_decompile.sh
source scripts/heimdall_decompile.sh

if [[ ! -f Examples/Token/compiled/runtime.yul ]]; then
  echo "==> artifacts missing; running export"
  scripts/export_bytecode.sh >/dev/null
fi

run_heimdall() {
  local dir
  dir="$(lsc_compiled_dir "$1")"
  HEIMDALL_NOTICE_PREFIX="  " lsc_heimdall_decompile "$1"
  local heimdall="${HEIMDALL:-${HOME}/.bifrost/bin/heimdall}"
  if [[ ! -x "$heimdall" ]]; then
    heimdall="$(command -v heimdall 2>/dev/null || true)"
  fi
  if [[ -n "$heimdall" && -x "$heimdall" && -f "${dir}/runtime.hex" ]]; then
    "$heimdall" disassemble "${dir}/runtime.hex" -o print \
      > "${dir}/disasm.txt" 2>/dev/null || true
  fi
}

review_one() {
  local name="$1"
  local dir
  dir="$(lsc_compiled_dir "$name")"
  echo "==> $name ($dir)"
  for f in runtime.yul deploy.yul runtime.asm runtime.hex deploy.hex decompiled.sol decompiled.yul; do
    local p="${dir}/${f}"
    if [[ -f "$p" ]]; then
      echo "  $p  $(wc -l < "$p") lines"
    else
      echo "  missing $p"
    fi
  done
  if [[ -f "${dir}/runtime.yul" ]]; then
    echo "  --- runtime.yul (head) ---"
    head -n 20 "${dir}/runtime.yul"
  fi
  if [[ -f "${dir}/runtime.asm" ]]; then
    echo "  --- runtime.asm (head) ---"
    head -n 20 "${dir}/runtime.asm"
  fi
  run_heimdall "$name"
  if [[ -f "${dir}/decompiled.sol" ]]; then
    echo "  --- decompiled.sol (head) ---"
    head -n 30 "${dir}/decompiled.sol"
  fi
}

case "$TARGET" in
  Counter|Token|Vault|Amm|Cpamm) review_one "$TARGET" ;;
  all)
    for c in "${CONTRACTS[@]}"; do review_one "$c"; done
    ;;
  *)
    echo "Usage: $0 [Counter|Token|Vault|Amm|Cpamm|all]" >&2
    exit 1
    ;;
esac
