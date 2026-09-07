#!/usr/bin/env bash
# Compile example contracts and write readable compiler artifacts:
#   out/<C>.runtime.hex / .deploy.hex
#   out/<C>.runtime.yul / .deploy.yul
#   out/<C>.runtime.asm          (labelled pre-assembly)
#   out/<C>.abi.json / .selectors.json
#   out/<C>.sol / .decompiled.yul  (heimdall; skipped if missing)
# JSON for the differential harness is printed on stdout.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="${HOME}/.bifrost/bin:${PATH}"
# shellcheck source=heimdall_decompile.sh
source scripts/heimdall_decompile.sh
mkdir -p out
CONTRACTS=(Counter Token Vault Amm)

echo "==> lake build (bytecode exporter deps)"
scripts/lean lake build Lsc.Compiler.Bytecode Lsc.Tools.Disasm Lsc.Tools.AbiJson \
  Examples.Counter.Contract Examples.Token.Contract Examples.Amm.Contract Examples.Vault.Contract
echo "==> export bytecode / Yul / labelled Asm"
scripts/lean lake env lean scripts/export_bytecode.lean > out/lsc-export.raw
echo "==> wrote out/<C>.{runtime,deploy}.{hex,yul} out/<C>.runtime.asm (JSON: out/lsc-export.raw)"
echo "==> heimdall decompile"
if [[ -z "${HEIMDALL:-}" && ! -x "${HOME}/.bifrost/bin/heimdall" ]] && ! command -v heimdall >/dev/null 2>&1; then
  echo "notice: heimdall not found (expected ~/.bifrost/bin/heimdall); skip decompile"
else
  for c in "${CONTRACTS[@]}"; do
    lsc_heimdall_decompile "$c"
  done
fi
