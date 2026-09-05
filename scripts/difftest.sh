#!/usr/bin/env bash
# Differential harness: Lean Tx.run vs anvil/revm on compiled EVM bytecode.
# Usage: scripts/difftest.sh
#        scripts/difftest.sh --skip-export [export.json]
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="${HOME}/.foundry/bin:${PATH}"

if [[ "${1:-}" == "--skip-export" ]]; then
  shift
  exec python3 tests/difftest.py "$@"
fi

python3 tests/difftest.py --check-tools

echo "==> lake build (bytecode exporter deps)"
scripts/lean lake build Lsc.Compiler.Bytecode Lsc.Examples.Counter Lsc.Examples.Token Lsc.Tools.AbiJson

echo "==> export bytecode + Tx.run expectations"
EXPORT_OUT="${LSC_EXPORT_JSON:-$(mktemp "${TMPDIR:-/tmp}/lsc-export.XXXXXX")}"
scripts/lean lake env lean scripts/export_bytecode.lean > "$EXPORT_OUT"
echo "==> anvil/revm differential (export $EXPORT_OUT)"
exec python3 tests/difftest.py "$EXPORT_OUT"
