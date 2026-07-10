LSC bytecode review artifacts

contract/
  bytecode.hex   full runtime bytecode (post IR.Opt.optimizeStmt → codegen → encode)
  abi.json       ABI for heimdall -a (keccak selectors)

functions/{name}/
  ir.txt         optimised IR for one external/view function
  yul.txt        LSC Yul lowering
  instr.txt      LSC codegen Instr dump (authoritative for external CALL shapes)
  bytecode.hex   function body only (no dispatcher)

heimdall/        filled by scripts/review-bytecode.sh when heimdall is installed
  contract/      decompiled.yul + disasm.txt for full runtime
  functions/{name}/  per-function heimdall output (when generated)

Prefer functions/*/instr.txt + heimdall disasm over heimdall Yul for Escrow release.
