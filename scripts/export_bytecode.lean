/-
Export compiled EVM bytecode, Yul, labelled Asm, and Tx.run expectations.

  scripts/export_bytecode.sh
  scripts/lean lake env lean scripts/export_bytecode.lean

Writes `out/<C>.{runtime,deploy}.{hex,yul}`, `out/<C>.runtime.asm`,
`out/<C>.abi.json`, `out/<C>.selectors.json`, and prints JSON on stdout
(BEGIN_LSC_EXPORT … END_LSC_EXPORT) for `scripts/difftest.sh`.

Does not import `Examples.Misc.YulTests` (that file's `#eval`/`#guard` would re-run the
Yul interpreter). Case lists, senders, and mapping slots follow YulTests.
Amm cases are view-only (`getReserves` / `sharesOf` / `quote0for1`); constructor and
swaps CALL out and are not expected to match anvil without token fixtures.
Vault is exported for artifacts only (no Tx.run cases); its constructor CALLs out.
-/
import Lsc.Compiler.Bytecode
import Lsc.Compiler.Yul
import YulEvmCompiler.Asm
import YulEvmCompiler.Compile
import YulEvmCompiler.Optimizer.Implementation.MemorySpill
import Examples.Counter.Contract
import Examples.Token.Contract
import Examples.Amm.Contract
import Examples.Vault.Contract
import Lsc.Tools.AbiJson
import Lsc.Tools.Disasm

set_option maxHeartbeats 16000000

open Lsc
open Lsc.Compiler
open Lsc.Tools

namespace ExportBytecode

def hexDigit (n : Nat) : Char :=
  Char.ofNat (if n < 10 then '0'.toNat + n else 'a'.toNat + (n - 10))

def hex2 (n : Nat) : String :=
  String.ofList [hexDigit ((n / 16) % 16), hexDigit (n % 16)]

def bytesHex (bs : List UInt8) : String :=
  "0x" ++ String.intercalate "" (bs.map fun b => hex2 b.toNat)

def addrHex (n : Nat) : String :=
  "0x" ++ String.intercalate "" ((wordBytes n).drop 12 |>.map fun b => hex2 b.toNat)

def uhex (x : BitVec 256) : String :=
  bytesHex (wordBytes x.toNat)

def jStr (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""

def hexOpt : Option (List UInt8) → String
  | none => "null"
  | some bs => jStr (bytesHex bs)

def u256 (n : Nat) : BitVec 256 := BitVec.ofNat 256 n

def slotJson (p : BitVec 256 × BitVec 256) : String :=
  "{\"slot\":" ++ jStr (uhex p.1) ++ ",\"value\":" ++ jStr (uhex p.2) ++ "}"

def slotsJson (pairs : List (BitVec 256 × BitVec 256)) : String :=
  "[" ++ String.intercalate "," (pairs.map slotJson) ++ "]"

def fnNamed (c : ContractDef) (n : String) : Option FnDef :=
  c.functions.find? (fun f => f.name = n)

def fnCall (c : ContractDef) (fname : String) (args : List Nat) : List UInt8 :=
  match fnNamed c fname with
  | none => []
  | some f => fnCalldata f args

def selectorsJson (c : ContractDef) : String :=
  let fns := c.functions.map fun f =>
    jStr f.name ++ ":" ++ jStr (bytesHex (selectorBytes f.selector))
  let errs := c.errors.map fun e =>
    jStr e.name ++ ":" ++ jStr (bytesHex (selectorBytes e.selector))
  "{\"functions\":{" ++ String.intercalate "," fns ++
    "},\"errors\":{" ++ String.intercalate "," errs ++ "}}"

structure RtArt where
  hex : Option (List UInt8)
  yul : String
  asm : String

/-- One `compileAsm` + `lowerProg` (same pipeline as `compileRuntime`).
If the verified gate rejects the program, still list `compileProgram` Asm. -/
def runtimeArt (c : ContractDef) : RtArt :=
  match runtimeBlock c with
  | none => { hex := none, yul := "// runtimeBlock failed", asm := "// compileAsm failed\n" }
  | some b =>
    let yul := printYul b
    match compileAsmBlock b with
    | some asm =>
      { hex := (YulEvmCompiler.lowerProg YulEvmCompiler.unpatchedImmutables asm).map
          YulEvmCompiler.assembleBytes
      , yul
      , asm := Disasm.printAsmFile c asm }
    | none =>
      match YulEvmCompiler.compileProgram
          (YulEvmCompiler.Optimizer.MemorySpill.eraseMemoryGuardStmts b) with
      | none =>
        { hex := none, yul
        , asm :=
            "// compileProgram failed (powdr rejected this Yul; no bytecode).\n" ++
            "// Read the sibling .runtime.yul for the dispatcher and bodies.\n" }
      | some asm =>
        { hex := none, yul
        , asm := "// compileAsm rejected (stackOK2/wfCheck); hex not emitted.\n" ++
            Disasm.printAsmFile c asm }

def writeContract (name : String) (c : ContractDef) (art : RtArt) : IO Unit := do
  let dyul :=
    match deployObject c with
    | none => "// deployObject failed\n"
    | some o => Disasm.printYulFile c (printYulObject o)
  IO.FS.writeFile s!"out/{name}.runtime.yul" (Disasm.printYulFile c art.yul)
  IO.FS.writeFile s!"out/{name}.deploy.yul" dyul
  IO.FS.writeFile s!"out/{name}.runtime.asm" art.asm
  IO.FS.writeFile s!"out/{name}.abi.json" (contractAbiJson c ++ "\n")
  IO.FS.writeFile s!"out/{name}.selectors.json" (selectorsJson c ++ "\n")
  match art.hex with
  | none => IO.eprintln s!"{name}: compileRuntime failed"
  | some bs => IO.FS.writeFile s!"out/{name}.runtime.hex" (bytesHex bs ++ "\n")
  match compileDeploy c with
  | none => IO.eprintln s!"{name}: compileDeploy failed"
  | some bs => IO.FS.writeFile s!"out/{name}.deploy.hex" (bytesHex bs ++ "\n")

structure Case where
  name : String
  sender : Nat
  calldata : List UInt8
  status : String
  returnData : List UInt8
  pre : List (BitVec 256 × BitVec 256)
  post : List (BitVec 256 × BitVec 256)

def caseJson (c : Case) : String :=
  "{" ++ String.intercalate "," [
    "\"name\":" ++ jStr c.name,
    "\"sender\":" ++ jStr (addrHex c.sender),
    "\"calldata\":" ++ jStr (bytesHex c.calldata),
    "\"status\":" ++ jStr c.status,
    "\"return_data\":" ++ jStr (bytesHex c.returnData),
    "\"pre_storage\":" ++ slotsJson c.pre,
    "\"post_storage\":" ++ slotsJson c.post
  ] ++ "}"

def unitOutcome {S X E ε : Type}
    (c : ContractDef) (errIdx : ε → Nat)
    (tx : Except (Err ε) (Unit × World S X E))
    (pre postOk : List (BitVec 256 × BitVec 256)) :
    String × List UInt8 × List (BitVec 256 × BitVec 256) :=
  match tx with
  | .ok _ => ("ok", [], postOk)
  | .error (.user e) => ("revert", customErrorBytes c (errIdx e) [], pre)
  | .error (.arith a) => ("revert", panicBytes (arithPanicCode a), pre)
  | .error .callFailed => ("revert", [], pre)

def wordOutcome {S X E ε : Type}
    (c : ContractDef) (errIdx : ε → Nat)
    (tx : Except (Err ε) (Nat × World S X E))
    (pre postOk : List (BitVec 256 × BitVec 256)) :
    String × List UInt8 × List (BitVec 256 × BitVec 256) :=
  match tx with
  | .ok (v, _) => ("ok", abiBytes [v], postOk)
  | .error (.user e) => ("revert", customErrorBytes c (errIdx e) [], pre)
  | .error (.arith a) => ("revert", panicBytes (arithPanicCode a), pre)
  | .error .callFailed => ("revert", [], pre)

def pairOutcome {S X E ε : Type}
    (c : ContractDef) (errIdx : ε → Nat)
    (tx : Except (Err ε) ((Nat × Nat) × World S X E))
    (pre postOk : List (BitVec 256 × BitVec 256)) :
    String × List UInt8 × List (BitVec 256 × BitVec 256) :=
  match tx with
  | .ok ((a, b), _) => ("ok", abiBytes [a, b], postOk)
  | .error (.user e) => ("revert", customErrorBytes c (errIdx e) [], pre)
  | .error (.arith a) => ("revert", panicBytes (arithPanicCode a), pre)
  | .error .callFailed => ("revert", [], pre)

def mkCase (c : ContractDef) (name fname : String) (args : List Nat) (sender : Nat)
    (outcome : String × List UInt8 × List (BitVec 256 × BitVec 256))
    (pre : List (BitVec 256 × BitVec 256)) : Case :=
  { name, sender, calldata := fnCall c fname args, status := outcome.1,
    returnData := outcome.2.1, pre, post := outcome.2.2 }

/-! ## Counter (same cases as `YulTests`) -/

def ctrErr : Counter.Error → Nat
  | .Zero => 0

def ctrW (n : Nat) : World Counter.Storage Unit Counter.Event :=
  { self := { count := n }, ext := () }

def ctrSlots (n : Nat) : List (BitVec 256 × BitVec 256) :=
  [(u256 0, u256 n)]

def ctx1 : Ctx := { sender := 1, self := 7 }

def ctrUnit (name fname : String) (args : List Nat) (count : Nat)
    (tx : Except (Err Counter.Error) (Unit × World Counter.Storage Unit Counter.Event)) : Case :=
  let pre := ctrSlots count
  let postOk :=
    match tx with
    | .ok (_, w') => ctrSlots w'.self.count
    | .error _ => pre
  mkCase Counter.contract name fname args ctx1.sender
    (unitOutcome Counter.contract ctrErr tx pre postOk) pre

def ctrWord (name fname : String) (args : List Nat) (count : Nat)
    (tx : Except (Err Counter.Error) (Nat × World Counter.Storage Unit Counter.Event)) : Case :=
  let pre := ctrSlots count
  let postOk :=
    match tx with
    | .ok (_, w') => ctrSlots w'.self.count
    | .error _ => pre
  mkCase Counter.contract name fname args ctx1.sender
    (wordOutcome Counter.contract ctrErr tx pre postOk) pre

def counterCases : List Case :=
  [ ctrUnit "increment_ok" "increment" [] 5 (Tx.run Counter.increment ctx1 (ctrW 5))
  , ctrUnit "increment_overflow" "increment" [] (wordBound - 1)
      (Tx.run Counter.increment ctx1 (ctrW (wordBound - 1)))
  , ctrUnit "incrementBy_ok" "incrementBy" [3] 5 (Tx.run (Counter.incrementBy 3) ctx1 (ctrW 5))
  , ctrUnit "incrementBy_zero" "incrementBy" [0] 5 (Tx.run (Counter.incrementBy 0) ctx1 (ctrW 5))
  , ctrUnit "decrement_from_zero" "decrement" [] 0 (Tx.run Counter.decrement ctx1 (ctrW 0))
  , ctrUnit "decrement_ok" "decrement" [] 5 (Tx.run Counter.decrement ctx1 (ctrW 5))
  , ctrWord "get" "get" [] 42 (Tx.run Counter.get ctx1 (ctrW 42)) ]

/-! ## Token (same cases as `YulTests`) -/

def tokErr : Token.Error → Nat
  | .InsufficientBalance => 0
  | .InsufficientAllowance => 1
  | .NotOwner => 2

def tokAddrs : List Nat := [0, 1, 2, 3]

def tokSlots (σ : Token.Storage) : List (BitVec 256 × BitVec 256) :=
  [(u256 0, u256 σ.owner), (u256 1, u256 σ.totalSupply)] ++
    tokAddrs.map (fun a => (mapSlot1 keccakOf 2 a, u256 (σ.balances a))) ++
    tokAddrs.flatMap (fun a =>
      tokAddrs.map (fun b => (mapSlot2 keccakOf 3 a b, u256 (σ.allowances a b))))

def bals₁ : Nat → Nat
  | 1 => 1000
  | _ => 0

def allow₀ : Nat → Nat → Nat
  | _, _ => 0

def allow₁₂ : Nat → Nat → Nat
  | 1, 2 => 200
  | _, _ => 0

def σ₁ : Token.Storage :=
  { owner := 1, totalSupply := 1000, balances := bals₁, allowances := allow₀ }

def σAllow : Token.Storage := { σ₁ with allowances := allow₁₂ }

def w₁ : World Token.Storage Unit Token.Event := { self := σ₁, ext := () }
def wAllow : World Token.Storage Unit Token.Event := { self := σAllow, ext := () }

def ctxOwner : Ctx := { sender := 1, self := 7 }
def ctx2 : Ctx := { sender := 2, self := 7 }

def tokUnit (name fname : String) (args : List Nat) (ctx : Ctx) (σ : Token.Storage)
    (tx : Except (Err Token.Error) (Unit × World Token.Storage Unit Token.Event)) : Case :=
  let pre := tokSlots σ
  let postOk :=
    match tx with
    | .ok (_, w') => tokSlots w'.self
    | .error _ => pre
  mkCase Token.contract name fname args ctx.sender
    (unitOutcome Token.contract tokErr tx pre postOk) pre

def tokWord (name fname : String) (args : List Nat) (ctx : Ctx) (σ : Token.Storage)
    (tx : Except (Err Token.Error) (Nat × World Token.Storage Unit Token.Event)) : Case :=
  let pre := tokSlots σ
  let postOk :=
    match tx with
    | .ok (_, w') => tokSlots w'.self
    | .error _ => pre
  mkCase Token.contract name fname args ctx.sender
    (wordOutcome Token.contract tokErr tx pre postOk) pre

def tokenCases : List Case :=
  [ tokUnit "transfer_ok" "transfer" [2, 100] ctxOwner σ₁
      (Tx.run (Token.transfer 2 100) ctxOwner w₁)
  , tokUnit "transfer_revert" "transfer" [2, 2000] ctxOwner σ₁
      (Tx.run (Token.transfer 2 2000) ctxOwner w₁)
  , tokUnit "approve_ok" "approve" [2, 50] ctxOwner σ₁
      (Tx.run (Token.approve 2 50) ctxOwner w₁)
  , tokUnit "transferFrom_ok" "transferFrom" [1, 3, 40] ctx2 σAllow
      (Tx.run (Token.transferFrom 1 3 40) ctx2 wAllow)
  , tokUnit "mint_ok" "mint" [2, 25] ctxOwner σ₁
      (Tx.run (Token.mint 2 25) ctxOwner w₁)
  , tokUnit "mint_notOwner" "mint" [2, 25] ctx2 σ₁
      (Tx.run (Token.mint 2 25) ctx2 w₁)
  , tokUnit "burn_ok" "burn" [30] ctxOwner σ₁
      (Tx.run (Token.burn 30) ctxOwner w₁)
  , tokUnit "burn_revert" "burn" [2000] ctxOwner σ₁
      (Tx.run (Token.burn 2000) ctxOwner w₁)
  , tokWord "balanceOf" "balanceOf" [1] ctxOwner σ₁
      (Tx.run (Token.balanceOf 1) ctxOwner w₁)
  , tokWord "allowance" "allowance" [1, 2] ctxOwner σAllow
      (Tx.run (Token.allowance 1 2) ctxOwner wAllow)
  , tokWord "totalSupply" "totalSupply" [] ctxOwner σ₁
      (Tx.run Token.totalSupply ctxOwner w₁) ]

/-! ## Amm (view-only cases; swaps/ctor CALL out) -/

def ammErr : Amm.Error → Nat
  | .Zero => 0
  | .ZeroShares => 1
  | .ZeroOut => 2
  | .InsufficientShares => 3
  | .InsufficientOutput => 4
  | .SameToken => 5
  | .TransferFailed => 6

def ammAddrs : List Nat := [0, 2]

def ammSlots (σ : Amm.Storage) : List (BitVec 256 × BitVec 256) :=
  [(u256 0, u256 σ.reserve0), (u256 1, u256 σ.reserve1), (u256 2, u256 σ.totalShares),
    (u256 4, u256 σ.token0), (u256 5, u256 σ.token1),
    (u256 6, u256 σ.decimals0), (u256 7, u256 σ.decimals1)] ++
    ammAddrs.map (fun a => (mapSlot1 keccakOf 3 a, u256 (σ.shares a)))

def ammWord (name fname : String) (args : List Nat)
    (tx : Except (Err Amm.Error) (Nat × World Amm.Storage Amm.Ext Amm.Event)) : Case :=
  let pre := ammSlots Amm.smokePool.self
  mkCase Amm.contract name fname args Amm.smokeCtx.sender
    (wordOutcome Amm.contract ammErr tx pre pre) pre

def ammPair (name fname : String) (args : List Nat)
    (tx : Except (Err Amm.Error) ((Nat × Nat) × World Amm.Storage Amm.Ext Amm.Event)) : Case :=
  let pre := ammSlots Amm.smokePool.self
  mkCase Amm.contract name fname args Amm.smokeCtx.sender
    (pairOutcome Amm.contract ammErr tx pre pre) pre

def ammCases : List Case :=
  [ ammPair "getReserves" "getReserves" [] (Tx.run Amm.getReserves Amm.smokeCtx Amm.smokePool)
  , ammWord "sharesOf" "sharesOf" [2] (Tx.run (Amm.sharesOf 2) Amm.smokeCtx Amm.smokePool)
  , ammWord "quote0for1_ok" "quote0for1" [100]
      (Tx.run (Amm.quote0for1 (Amount.ofNat 100)) Amm.smokeCtx Amm.smokePool)
  , ammWord "quote0for1_zero" "quote0for1" [0]
      (Tx.run (Amm.quote0for1 (Amount.ofNat 0)) Amm.smokeCtx Amm.smokePool) ]

def contractJson (name : String) (c : ContractDef) (art : RtArt) (cases : List Case)
    (ctorCalldata : Option (List UInt8) := none)
    (ctorChecks : List Case := []) : String :=
  "{" ++ String.intercalate "," [
    "\"name\":" ++ jStr name,
    "\"runtime\":" ++ hexOpt art.hex,
    "\"deploy\":" ++ hexOpt (compileDeploy c),
    "\"ctor_calldata\":" ++ hexOpt ctorCalldata,
    "\"ctor_checks\":[" ++ String.intercalate "," (ctorChecks.map caseJson) ++ "]",
    "\"abi\":" ++ contractAbiJson c,
    "\"selectors\":" ++ selectorsJson c,
    "\"cases\":[" ++ String.intercalate "," (cases.map caseJson) ++ "]"
  ] ++ "}"

def tokenCtorOwner : Nat := 1
def tokenCtorSupply : Nat := 1000
def tokenW0 : World Token.Storage Unit Token.Event :=
  { self := { owner := 0, totalSupply := 0, balances := fun _ => 0, allowances := fun _ _ => 0 }
  , ext := () }
def tokenCtxDeploy : Ctx := { sender := 1, self := 7 }
def tokenW1 : World Token.Storage Unit Token.Event :=
  match Tx.run (Token.constructor tokenCtorOwner tokenCtorSupply) tokenCtxDeploy tokenW0 with
  | .ok (_, w) => w
  | .error _ => tokenW0

def tokenCtorChecks : List Case :=
  [ tokWord "ctor_balanceOf" "balanceOf" [tokenCtorOwner] tokenCtxDeploy tokenW1.self
      (Tx.run (Token.balanceOf tokenCtorOwner) tokenCtxDeploy tokenW1)
  , tokWord "ctor_totalSupply" "totalSupply" [] tokenCtxDeploy tokenW1.self
      (Tx.run Token.totalSupply tokenCtxDeploy tokenW1) ]

/-- Fixed `anvil_setCode` address. YulTests uses `Ctx.self = 7`, but `0x07` is the
ECMUL precompile on a real EVM; Counter/Token do not read `ADDRESS`. -/
def runtimeAddress : String := addrHex 0xC0DE

def counterArt := runtimeArt Counter.contract
def tokenArt := runtimeArt Token.contract
def ammArt := runtimeArt Amm.contract
def vaultArt := runtimeArt Vault.contract

def exportJson : String :=
  "{" ++ String.intercalate "," [
    "\"runtime_address\":" ++ jStr runtimeAddress,
    "\"contracts\":[" ++ String.intercalate "," [
      contractJson "Counter" Counter.contract counterArt counterCases,
      contractJson "Token" Token.contract tokenArt tokenCases
        (some (ctorCalldata [tokenCtorOwner, tokenCtorSupply]))
        tokenCtorChecks,
      contractJson "Amm" Amm.contract ammArt ammCases
        (some (ctorCalldata [10, 11])),
      contractJson "Vault" Vault.contract vaultArt []
        (some (ctorCalldata [1, 10]))
    ] ++ "]"
  ] ++ "}"

def main : IO Unit := do
  IO.FS.createDirAll "out"
  writeContract "Counter" Counter.contract counterArt
  writeContract "Token" Token.contract tokenArt
  writeContract "Amm" Amm.contract ammArt
  writeContract "Vault" Vault.contract vaultArt
  IO.println "BEGIN_LSC_EXPORT"
  IO.println exportJson
  IO.println "END_LSC_EXPORT"

end ExportBytecode

open ExportBytecode

#eval main
