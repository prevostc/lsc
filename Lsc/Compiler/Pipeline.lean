import Lsc.Compiler.Bytecode
import Lsc.Compiler.Yul
import Lsc.Tools.AbiJson
import Lsc.Tools.Disasm
import YulEvmCompiler.Asm
import YulEvmCompiler.Compile
import YulEvmCompiler.Optimizer.Implementation.MemorySpill

/-!
# Contract → bytecode / ABI (single entry point)

Stages, in order. This module does not change them; it names them.

1. **Contract definition** — `lsc_contract` (`Lsc/Lang/Reify.lean`) produces
   `C.contract : ContractDef` with `f.core` and `f.core_denote`.
2. **Core reification** — same command; Core lives in `Lsc/Lang/Core.lean`.
3. **Yul emission** — `toYulFn` / `runtimeBlock` / `deployObject`
   (`Lsc/Compiler/Yul.lean`). Dispatcher is `switch shr(224, calldataload(0))`.
4. **powdr compile** — `compileBlock` (`Lsc/Compiler/Bytecode.lean`): erase
   `memoryguard` then compile, or powdr memory-spill if erasure needs `DUP17+`.
   Deploy is `compileDeploy` (`spillObjectWithFallback`).
5. **Bytecode** — `assembleBytes` of the `Instr` list; deploy is `Layout.code`.
6. **ABI / selectors** — `Lsc.Tools.contractAbiJson` and `selectorsJson` below
   (keccak selectors already on `FnDef` / `ErrorDef`).
7. **Deploy object** — `deployObject` then `compileDeploy`; init code returns
   the nested `"runtime"` slice (`constructorCode`).

`compileContract` (alias `artifacts`) is the function `scripts/export_bytecode.lean`
should call so compilation lives in one place. The exporter currently still
inlines the same steps; wiring it is a follow-up (that script is owned by
another change). Behaviour of `runtimeBlock` / `compileBlock` / `compileDeploy`
is unchanged.
-/

namespace Lsc.Compiler

open Lsc
open Lsc.Tools
open Lsc.Tools.Disasm
open YulEvmCompiler
open YulEvmCompiler.Optimizer.MemorySpill

/-- Compiled artifacts for one `ContractDef`. `asm` is labelled Asm (or a
failure comment); `none` only if there is no listing at all. -/
structure Artifacts where
  runtimeHex : Option (List UInt8)
  deployHex : Option (List UInt8)
  abi : String
  yul : String
  asm : Option String
  deployYul : String
  selectors : String
  deriving Inhabited

private def hexDigit (n : Nat) : Char :=
  Char.ofNat (if n < 10 then '0'.toNat + n else 'a'.toNat + (n - 10))

private def hex2 (n : Nat) : String :=
  String.ofList [hexDigit ((n / 16) % 16), hexDigit (n % 16)]

private def bytesHex (bs : List UInt8) : String :=
  "0x" ++ String.intercalate "" (bs.map fun b => hex2 b.toNat)

private def jStr (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""

/-- Function and error selectors as JSON (same shape as the exporter). -/
def selectorsJson (c : ContractDef) : String :=
  let fns := c.functions.map fun f =>
    jStr f.name ++ ":" ++ jStr (bytesHex (selectorBytes f.selector))
  let errs := c.errors.map fun e =>
    jStr e.name ++ ":" ++ jStr (bytesHex (selectorBytes e.selector))
  "{\"functions\":{" ++ String.intercalate "," fns ++
    "},\"errors\":{" ++ String.intercalate "," errs ++ "}}"

/-- Runtime hex / Yul / Asm. Same cases as `scripts/export_bytecode.lean`
`runtimeArt`: `compileAsmBlock` then `lowerProg`, else `compileProgram` of the
erased block for a listing without hex. -/
def compileRuntimeArtifacts (c : ContractDef) :
    Option (List UInt8) × String × Option String :=
  match runtimeBlock c with
  | none =>
    (none, "// runtimeBlock failed", some "// compileAsm failed\n")
  | some b =>
    let yul := printYul b
    match compileAsmBlock b with
    | some asm =>
      let hex := (lowerProg unpatchedImmutables asm).map assembleBytes
      (hex, yul, some (printAsmFile c asm))
    | none =>
      match compileProgram (eraseMemoryGuardStmts b) with
      | none =>
        (none, yul, some
          ("// compileProgram failed (powdr rejected this Yul; no bytecode).\n" ++
            "// Read the sibling .runtime.yul for the dispatcher and bodies.\n"))
      | some asm =>
        (none, yul, some
          ("// compileAsm rejected (stackOK2/wfCheck); hex not emitted.\n" ++
            printAsmFile c asm))

/-- Deploy Yul listing (`deployObject`), or a failure comment. -/
def compileDeployYul (c : ContractDef) : String :=
  match deployObject c with
  | none => "// deployObject failed\n"
  | some o => printYulFile c (printYulObject o)

/-- All artifacts for `c`. Hex paths are `compileRuntimeArtifacts` (runtime)
and `compileDeploy` (init code). Does not interpret `Tx.run`. -/
def compileContract (c : ContractDef) : Artifacts :=
  let rt := compileRuntimeArtifacts c
  { runtimeHex := rt.1
    deployHex := compileDeploy c
    abi := contractAbiJson c
    yul := rt.2.1
    asm := rt.2.2
    deployYul := compileDeployYul c
    selectors := selectorsJson c }

/-- Alias of `compileContract`. -/
abbrev artifacts := compileContract

end Lsc.Compiler
