#!/usr/bin/env bash
# Generate human bytecode review artifacts for LSC example contracts.
#
# Layout under examples/{name}/output/local/:
#   contract/bytecode.hex, contract/abi.json
#   functions/{fn}/ir.txt, yul.txt, instr.txt, bytecode.hex
#   heimdall/contract/decompiled.yul, disasm.txt
#   heimdall/functions/{fn}/...  (Escrow release slice, etc.)
#
# Usage: scripts/review-bytecode.sh [counter|escrow|token|interest|all]

set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"

run_heimdall_contract() {
  local hex="$1"
  local out="$2"
  local abi="$3"
  if ! command -v heimdall >/dev/null 2>&1; then
    echo "  skip heimdall (not installed)"
    return 0
  fi
  mkdir -p "$out"
  heimdall decompile "$hex" -o "$out" --include-yul -a "$abi" -d 2>/dev/null || true
  heimdall disassemble "$hex" -o print > "$out/disasm.txt" 2>/dev/null || true
  echo "  heimdall → heimdall/contract/decompiled.yul, disasm.txt"
}

run_heimdall_function() {
  local hex_file="$1"
  local out="$2"
  local abi="$3"
  local name="$4"
  if ! command -v heimdall >/dev/null 2>&1; then
    return 0
  fi
  if [[ ! -f "$hex_file" ]]; then
    return 0
  fi
  local hex
  hex="$(cat "$hex_file")"
  mkdir -p "$out"
  heimdall decompile "$hex" -o "$out" --include-yul -a "$abi" -d 2>/dev/null || true
  heimdall disassemble "$hex" -o print > "$out/disasm.txt" 2>/dev/null || true
  echo "  heimdall → heimdall/functions/$name/decompiled.yul, disasm.txt"
}

review_example() {
  local dir="$1"
  local lib="$2"
  echo "==> $lib"
  cd "$ROOT/examples/$dir"
  lake build "$lib" review 2>&1 | tail -3
  local out="$ROOT/examples/$dir/output/local"
  ./.lake/build/bin/review "$out"
  local abi="$out/contract/abi.json"
  if [[ -f "$out/contract/bytecode.hex" ]]; then
    run_heimdall_contract "$(cat "$out/contract/bytecode.hex")" "$out/heimdall/contract" "$abi"
  fi
  # Escrow: also decompile release function slice (no dispatcher)
  if [[ -f "$out/functions/release/bytecode.hex" ]]; then
    run_heimdall_function "$out/functions/release/bytecode.hex" \
      "$out/heimdall/functions/release" "$abi" "release"
  fi
}

TARGET="${1:-all}"

case "$TARGET" in
  counter) review_example counter Counter ;;
  escrow)  review_example escrow Escrow ;;
  token)   review_example token Token ;;
  interest) review_example interest Interest ;;
  all)
    review_example counter Counter
    review_example escrow Escrow
    review_example token Token
    review_example interest Interest
    ;;
  *)
    echo "Usage: $0 [counter|escrow|token|interest|all]" >&2
    exit 1
    ;;
esac

echo "Done."
