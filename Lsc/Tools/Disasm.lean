import Lsc.Lang.Contract
import YulEvmCompiler.Asm

/-!
# Labelled EVM assembly printer

Pretty-prints powdr's pre-assembly `YulEvmCompiler.Asm` (symbolic labels, not
byte offsets). `compileAsm` already exposes this IR; there is no separate
printer in powdr, so this module is the listing. Pure, no proofs.
-/

namespace Lsc.Tools.Disasm

open Lsc
open YulEvmCompiler

private def hexDigit (n : Nat) : Char :=
  Char.ofNat (if n < 10 then '0'.toNat + n else 'a'.toNat + (n - 10))

partial def hexChars (n : Nat) : List Char :=
  if n < 16 then [hexDigit n] else hexChars (n / 16) ++ [hexDigit (n % 16)]

def hexNat (n : Nat) : String :=
  let cs := hexChars n
  let cs := if cs.length % 2 = 1 then '0' :: cs else cs
  "0x" ++ String.ofList cs

def hexPad (width n : Nat) : String :=
  let cs := hexChars n
  "0x" ++ String.ofList (List.replicate (width - cs.length) '0' ++ cs)

/-- Function, error, and event immediates worth annotating on `PUSH`. -/
def selectorTable (c : ContractDef) : List (Nat × String) :=
  c.functions.map (fun f => (f.selector, f.signature)) ++
  c.errors.map (fun e => (e.selector, abiSignature e.name e.params)) ++
  c.events.map (fun e => (e.topic0, abiSignature e.name e.params))

def functionHeader (c : ContractDef) : String :=
  let lines := c.functions.map fun f =>
    "//   " ++ hexPad 8 f.selector ++ "  (" ++ toString f.selector ++ ")  " ++ f.signature
  "// selector → function  (hex and decimal; `switch` cases print decimal)\n" ++
    String.intercalate "\n" lines ++ "\n\n"

/-- Tag `case <selector> {` lines with the ABI signature. -/
def annotateSwitch (c : ContractDef) (yul : String) : String :=
  c.functions.foldl (fun s f =>
    s.replace ("case " ++ toString f.selector ++ " {")
      ("case " ++ toString f.selector ++ " { // " ++ f.signature)) yul

def asmBanner : String :=
  "// Labelled pre-assembly (powdr YulEvmCompiler.Asm, before lowerProg).\n" ++
  "// Each `Ln:` is a JUMPDEST. JUMP/JUMPI take labels, not byte offsets.\n"

private def pushComment (sels : List (Nat × String)) (n : Nat) : String :=
  match sels.find? (fun p => p.1 = n) with
  | none => ""
  | some (_, sig) =>
    if n < 2 ^ 32 then "    // selector: " ++ sig else "    // topic: " ++ sig

private def opName (yop : YulSemantics.EVM.Op) : String :=
  (YulSemantics.EVM.opName yop).map Char.toUpper

private def gasCallName : GasCallKind → String
  | .call => "CALL" | .callcode => "CALLCODE"
  | .delegatecall => "DELEGATECALL" | .staticcall => "STATICCALL"

def printInstr (sels : List (Nat × String)) : Asm → String
  | .push v =>
    "    PUSH " ++ hexNat v.toNat ++ pushComment sels v.toNat
  | .op yop => "    " ++ opName yop
  | .dup n => "    DUP" ++ toString (n.val + 1)
  | .swap n => "    SWAP" ++ toString (n.val + 1)
  | .pop => "    POP"
  | .label l => s!"L{l}:    // JUMPDEST"
  | .jump l => s!"    JUMP L{l}"
  | .jumpi l => s!"    JUMPI L{l}"
  | .pushLabel l => s!"    PUSH L{l}    // -> jumpdest"
  | .dynJump => "    JUMP    // dynamic"
  | .pushImmutable key => s!"    PUSH32 <immutable {key}>"
  | .gasCall k => "    GAS\n    " ++ gasCallName k

def printAsm (sels : List (Nat × String)) (xs : List Asm) : String :=
  String.intercalate "\n" (xs.map (printInstr sels))

def printYulFile (c : ContractDef) (body : String) : String :=
  functionHeader c ++ annotateSwitch c body ++ "\n"

def printAsmFile (c : ContractDef) (xs : List Asm) : String :=
  asmBanner ++ functionHeader c ++ printAsm (selectorTable c) xs ++ "\n"

end Lsc.Tools.Disasm
