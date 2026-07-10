import Lsc.Compile.Lower
import Lsc.Compile.Yul
import Lsc.Compile.Bytecode
import Lsc.Compile.Bytecode.Contract
import Lsc.Compile.Bytecode.Render
import Lsc.Compile.IR.Opt.Pipeline
import Lsc.Tools.AbiJson

namespace Lsc.Tools.BytecodeReview

open Lsc Lsc.Compile Lsc.Compile.IR Lsc.Compile.Bytecode

structure ReviewInput where
  contractName : String
  contractDef : ContractDef
  config : Config
  bytecodeHex : String

private def writeText (path : System.FilePath) (content : String) : IO Unit := do
  let parent := path.parent
  match parent with
  | none => pure ()
  | some p => IO.FS.createDirAll p
  IO.FS.writeFile path content

private def removeIfExists (path : System.FilePath) : IO Unit := do
  if (← path.pathExists) then IO.FS.removeFile path else pure ()

/-- Drop pre-subdirectory layout files so re-runs stay tidy. -/
private def cleanupLegacyFlat (out : System.FilePath) (fns : List FunctionDef) : IO Unit := do
  for legacy in #[out / "bytecode.hex", out / "abi.json", out / "disasm.txt"] do
    removeIfExists legacy
  for fn in fns do
    for legacy in #[
      out / s!"yul.{fn.name}.txt",
      out / s!"ir.{fn.name}.txt",
      out / s!"instr.{fn.name}.txt",
      out / s!"bytecode.{fn.name}.hex"
    ] do
      removeIfExists legacy

private def irRender (s : IR.Stmt) : String :=
  toString (repr s)

private def reviewFunction (outDir : System.FilePath) (cfg : Config) (fn : FunctionDef) : IO Unit := do
  unless (fn.kind == .external || fn.kind == .view) do
    return
  let fnDir := outDir / "functions" / fn.name
  match Lower.function cfg fn with
  | .error e => IO.eprintln s!"warning: failed to lower {fn.name}: {e}"
  | .ok ir =>
    let optIr := IR.Opt.optimizeStmt ir
    writeText (fnDir / "ir.txt") (irRender optIr)
    writeText (fnDir / "yul.txt") (irStmtToYulString optIr)
    match Bytecode.Contract.functionInstrs cfg fn with
    | .error e => IO.eprintln s!"warning: failed to codegen {fn.name}: {e}"
    | .ok instrs =>
      writeText (fnDir / "instr.txt") (renderInstrs instrs)
      match Bytecode.encode instrs with
      | .error e => IO.eprintln s!"warning: failed to encode {fn.name}: {e}"
      | .ok bytes =>
        writeText (fnDir / "bytecode.hex") (Bytecode.toHex bytes)

/-- Write LSC-native review artifacts under `outDir`. -/
def runReview (outDir : String) (input : ReviewInput) : IO Unit := do
  let out := System.FilePath.mk outDir
  IO.FS.createDirAll out
  cleanupLegacyFlat out input.contractDef.functions
  let contractDir := out / "contract"
  writeText (contractDir / "bytecode.hex") input.bytecodeHex
  writeText (contractDir / "abi.json") (contractAbiJson input.contractDef)
  writeText (out / "README.txt") <|
    "LSC bytecode review artifacts\n\n" ++
    "contract/\n" ++
    "  bytecode.hex   full runtime bytecode (post IR.Opt.optimizeStmt → codegen → encode)\n" ++
    "  abi.json       ABI for heimdall -a (keccak selectors)\n\n" ++
    "functions/{name}/\n" ++
    "  ir.txt         optimised IR for one external/view function\n" ++
    "  yul.txt        LSC Yul lowering\n" ++
    "  instr.txt      LSC codegen Instr dump (authoritative for external CALL shapes)\n" ++
    "  bytecode.hex   function body only (no dispatcher)\n\n" ++
    "heimdall/        filled by scripts/review-bytecode.sh when heimdall is installed\n" ++
    "  contract/      decompiled.yul + disasm.txt for full runtime\n" ++
    "  functions/{name}/  per-function heimdall output (when generated)\n\n" ++
    "Prefer functions/*/instr.txt + heimdall disasm over heimdall Yul for Escrow release.\n"
  for fn in input.contractDef.functions do
    reviewFunction out input.config fn
  IO.println s!"BytecodeReview: wrote {input.contractName} artifacts to {outDir}"

end Lsc.Tools.BytecodeReview
