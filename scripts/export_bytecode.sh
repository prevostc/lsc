#!/usr/bin/env bash
# Compile example contracts and write readable compiler artifacts:
#   out/<C>.runtime.hex / .deploy.hex
#   out/<C>.runtime.yul / .deploy.yul
#   out/<C>.runtime.asm          (labelled pre-assembly)
#   out/<C>.abi.json / .selectors.json
# JSON for the differential harness is printed on stdout.
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p out
echo "==> lake build (bytecode exporter deps)"
scripts/lean lake build Lsc.Compiler.Bytecode Lsc.Tools.Disasm Lsc.Tools.AbiJson \
  Examples.Counter.Contract Examples.Token.Contract Examples.Amm.Contract Examples.Vault.Contract
echo "==> export bytecode / Yul / labelled Asm"
scripts/lean lake env lean scripts/export_bytecode.lean > out/lsc-export.raw
echo "==> wrote out/<C>.{runtime,deploy}.{hex,yul} out/<C>.runtime.asm (JSON: out/lsc-export.raw)"
