#!/usr/bin/env bash
# Compile example contracts and write readable compiler artifacts into
#   Examples/<C>/compiled/
#   runtime.hex / deploy.hex
#   runtime.yul / deploy.yul
#   runtime.asm
#   abi.json / selectors.json
#   decompiled.sol / decompiled.yul  (heimdall; skipped if missing)
# JSON for the differential harness is printed on stdout.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="${HOME}/.bifrost/bin:${PATH}"
# shellcheck source=heimdall_decompile.sh
source scripts/heimdall_decompile.sh
CONTRACTS=(Counter Token Vault Amm Cpamm)

echo "==> lake build (bytecode exporter deps)"
scripts/lean lake build Lsc.Compiler.Bytecode Lsc.Tools.Disasm Lsc.Tools.AbiJson \
  Examples.Counter.Contract Examples.Token.Contract Examples.Amm.Contract \
  Examples.Vault.Contract Examples.Cpamm.Contract
echo "==> export bytecode / Yul / labelled Asm → Examples/*/compiled"
scripts/lean lake env lean scripts/export_bytecode.lean >/dev/null
echo "==> wrote Examples/<C>/compiled/{runtime,deploy}.{hex,yul} runtime.asm"
echo "==> heimdall decompile"
if [[ -z "${HEIMDALL:-}" && ! -x "${HOME}/.bifrost/bin/heimdall" ]] && ! command -v heimdall >/dev/null 2>&1; then
  echo "notice: heimdall not found (expected ~/.bifrost/bin/heimdall); skip decompile"
else
  for c in "${CONTRACTS[@]}"; do
    lsc_heimdall_decompile "$c"
  done
fi
