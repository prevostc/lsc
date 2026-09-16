/-
Export compiled EVM bytecode, Yul, labelled Asm, and Tx.run expectations.

  scripts/export_bytecode.sh
  scripts/lean lake env lean scripts/export_bytecode.lean

Writes `Examples/<C>/compiled/{runtime,deploy}.{hex,yul}`, `runtime.asm`,
`abi.json`, `selectors.json` (heimdall decompile is the shell wrapper), and
prints JSON on stdout (BEGIN_LSC_EXPORT … END_LSC_EXPORT) for `scripts/difftest.sh`.

Does not import example Tests files (their `#eval`/`#guard` would re-run).
Case lists, senders, and mapping slots follow the old interpreter fixtures.
Vault and CPAMM are exported for artifacts only (no Tx.run cases); constructors CALL out.
WETH has payable deposit / Native.send withdraw cases.
-/
import Lsc.Compiler.Bytecode
import Lsc.Compiler.Pipeline
import Lsc.Compiler.Yul
import YulEvmCompiler.Asm
import YulEvmCompiler.Compile
import YulEvmCompiler.Optimizer.Implementation.MemorySpill
import Examples.Counter.Contract
import Examples.Token.Contract
import Examples.Vault.Contract
import Examples.Cpamm.Contract
import Examples.WETH.Contract
import Lsc.Lang.Capability
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

/-- Per-example artifact directory. The exporter writes here directly. -/
def compiledDir (name : String) : String := s!"Examples/{name}/compiled"

def writeContract (name : String) (c : ContractDef) (art : Artifacts) : IO Unit := do
  let dir := compiledDir name
  IO.FS.createDirAll dir
  IO.FS.writeFile s!"{dir}/runtime.yul" (Disasm.printYulFile c art.yul)
  IO.FS.writeFile s!"{dir}/deploy.yul" art.deployYul
  IO.FS.writeFile s!"{dir}/runtime.asm" (art.asm.getD "// compileAsm failed\n")
  IO.FS.writeFile s!"{dir}/abi.json" (art.abi ++ "\n")
  IO.FS.writeFile s!"{dir}/selectors.json" (art.selectors ++ "\n")
  match art.runtimeHex with
  | none => IO.eprintln s!"{name}: compileRuntime failed"
  | some bs => IO.FS.writeFile s!"{dir}/runtime.hex" (bytesHex bs ++ "\n")
  match art.deployHex with
  | none => IO.eprintln s!"{name}: compileDeploy failed"
  | some bs => IO.FS.writeFile s!"{dir}/deploy.hex" (bytesHex bs ++ "\n")

structure Case where
  name : String
  sender : Nat
  calldata : List UInt8
  status : String
  returnData : List UInt8
  pre : List (BitVec 256 × BitVec 256)
  post : List (BitVec 256 × BitVec 256)
  value : Nat := 0
  selfBalance : Nat := 0
  setCode : List (Nat × String) := []

def setCodeJson (ps : List (Nat × String)) : String :=
  "[" ++ String.intercalate "," (ps.map fun p =>
    "{\"addr\":" ++ jStr (addrHex p.1) ++ ",\"code\":" ++ jStr p.2 ++ "}") ++ "]"

def caseJson (c : Case) : String :=
  "{" ++ String.intercalate "," [
    "\"name\":" ++ jStr c.name,
    "\"sender\":" ++ jStr (addrHex c.sender),
    "\"calldata\":" ++ jStr (bytesHex c.calldata),
    "\"status\":" ++ jStr c.status,
    "\"return_data\":" ++ jStr (bytesHex c.returnData),
    "\"pre_storage\":" ++ slotsJson c.pre,
    "\"post_storage\":" ++ slotsJson c.post,
    "\"value\":" ++ toString c.value,
    "\"self_balance\":" ++ toString c.selfBalance,
    "\"set_code\":" ++ setCodeJson c.setCode
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

def boolOutcome {S X E ε : Type}
    (c : ContractDef) (errIdx : ε → Nat)
    (tx : Except (Err ε) (Bool × World S X E))
    (pre postOk : List (BitVec 256 × BitVec 256)) :
    String × List UInt8 × List (BitVec 256 × BitVec 256) :=
  match tx with
  | .ok (true, _) => ("ok", abiBytes [1], postOk)
  | .ok (false, _) => ("ok", abiBytes [0], postOk)
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

def ctrW (n : Nat) : World Counter.Storage ExtState Counter.Event :=
  { self := { count := n }, ext := {} }

def ctrSlots (n : Nat) : List (BitVec 256 × BitVec 256) :=
  [(u256 0, u256 n)]

def ctx1 : Ctx := { sender := 1, self := 7 }

def ctrUnit (name fname : String) (args : List Nat) (count : Nat)
    (tx : Except (Err Counter.Error) (Unit × World Counter.Storage ExtState Counter.Event)) : Case :=
  let pre := ctrSlots count
  let postOk :=
    match tx with
    | .ok (_, w') => ctrSlots w'.self.count
    | .error _ => pre
  mkCase Counter.contract name fname args ctx1.sender
    (unitOutcome Counter.contract ctrErr tx pre postOk) pre

def ctrWord (name fname : String) (args : List Nat) (count : Nat)
    (tx : Except (Err Counter.Error) (Nat × World Counter.Storage ExtState Counter.Event)) : Case :=
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
  , { ctrUnit "increment_value_revert" "increment" [] 5
        (Tx.run Counter.increment ctx1 (ctrW 5)) with
      status := "revert", returnData := [], post := ctrSlots 5, value := 1 }
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

/-- Flattened `ERC20.Storage` then `owner`: balances 0, allowances 1,
totalSupply 2, owner 3. -/
def tokSlots (σ : Token.Storage) : List (BitVec 256 × BitVec 256) :=
  tokAddrs.map (fun a => (mapSlot1 keccakOf 0 a, u256 (σ.balances a).raw)) ++
    tokAddrs.flatMap (fun a =>
      tokAddrs.map (fun b => (mapSlot2 keccakOf 1 a b, u256 (σ.allowances a b).raw))) ++
    [(u256 2, u256 σ.totalSupply.raw), (u256 3, u256 σ.owner)]

def bals₁ : Nat → Nat
  | 1 => 1000
  | _ => 0

def allow₀ : Nat → Nat → Nat
  | _, _ => 0

def allow₁₂ : Nat → Nat → Nat
  | 1, 2 => 200
  | _, _ => 0

def σ₁ : Token.Storage :=
  { owner := 1, totalSupply := 1000
    balances := fun a => Amount.ofWord (bals₁ a)
    allowances := fun a b => Amount.ofWord (allow₀ a b) }

def σAllow : Token.Storage :=
  { σ₁ with allowances := fun a b => Amount.ofWord (allow₁₂ a b) }

def w₁ : World Token.Storage ExtState Token.Event := { self := σ₁, ext := {} }
def wAllow : World Token.Storage ExtState Token.Event := { self := σAllow, ext := {} }

def ctxOwner : Ctx := { sender := 1, self := 7 }
def ctx2 : Ctx := { sender := 2, self := 7 }

def tokUnit (name fname : String) (args : List Nat) (ctx : Ctx) (σ : Token.Storage)
    (tx : Except (Err Token.Error) (Unit × World Token.Storage ExtState Token.Event)) : Case :=
  let pre := tokSlots σ
  let postOk :=
    match tx with
    | .ok (_, w') => tokSlots w'.self
    | .error _ => pre
  mkCase Token.contract name fname args ctx.sender
    (unitOutcome Token.contract tokErr tx pre postOk) pre

def tokBool (name fname : String) (args : List Nat) (ctx : Ctx) (σ : Token.Storage)
    (tx : Except (Err Token.Error) (Bool × World Token.Storage ExtState Token.Event)) : Case :=
  let pre := tokSlots σ
  let postOk :=
    match tx with
    | .ok (_, w') => tokSlots w'.self
    | .error _ => pre
  mkCase Token.contract name fname args ctx.sender
    (boolOutcome Token.contract tokErr tx pre postOk) pre

def tokWord (name fname : String) (args : List Nat) (ctx : Ctx) (σ : Token.Storage)
    (tx : Except (Err Token.Error) (Nat × World Token.Storage ExtState Token.Event)) : Case :=
  let pre := tokSlots σ
  let postOk :=
    match tx with
    | .ok (_, w') => tokSlots w'.self
    | .error _ => pre
  mkCase Token.contract name fname args ctx.sender
    (wordOutcome Token.contract tokErr tx pre postOk) pre

def tokenCases : List Case :=
  [ tokBool "transfer_ok" "transfer" [2, 100] ctxOwner σ₁
      (Tx.run (Token.transfer 2 100) ctxOwner w₁)
  , tokBool "transfer_revert" "transfer" [2, 2000] ctxOwner σ₁
      (Tx.run (Token.transfer 2 2000) ctxOwner w₁)
  , { tokBool "transfer_value_revert" "transfer" [2, 100] ctxOwner σ₁
        (Tx.run (Token.transfer 2 100) ctxOwner w₁) with
      status := "revert", returnData := [], post := tokSlots σ₁, value := 1 }
  , tokBool "approve_ok" "approve" [2, 50] ctxOwner σ₁
      (Tx.run (Token.approve 2 50) ctxOwner w₁)
  , tokBool "transferFrom_ok" "transferFrom" [1, 3, 40] ctx2 σAllow
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
      ((Tx.run (Token.balanceOf 1) ctxOwner w₁).map fun (n, w) => (n.raw, w))
  , tokWord "allowance" "allowance" [1, 2] ctxOwner σAllow
      ((Tx.run (Token.allowance 1 2) ctxOwner wAllow).map fun (n, w) => (n.raw, w))
  , tokWord "totalSupply" "totalSupply" [] ctxOwner σ₁
      ((Tx.run Token.totalSupply ctxOwner w₁).map fun (n, w) => (n.raw, w)) ]

def contractJson (name : String) (c : ContractDef) (art : Artifacts) (cases : List Case)
    (ctorCalldata : Option (List UInt8) := none)
    (ctorChecks : List Case := []) : String :=
  "{" ++ String.intercalate "," [
    "\"name\":" ++ jStr name,
    "\"runtime\":" ++ hexOpt art.runtimeHex,
    "\"deploy\":" ++ hexOpt art.deployHex,
    "\"ctor_calldata\":" ++ hexOpt ctorCalldata,
    "\"ctor_checks\":[" ++ String.intercalate "," (ctorChecks.map caseJson) ++ "]",
    "\"abi\":" ++ contractAbiJson c,
    "\"selectors\":" ++ selectorsJson c,
    "\"cases\":[" ++ String.intercalate "," (cases.map caseJson) ++ "]"
  ] ++ "}"

def tokenCtorOwner : Nat := 1
def tokenCtorSupply : Nat := 1000
def tokenW0 : World Token.Storage ExtState Token.Event :=
  { self := { owner := 0, totalSupply := 0, balances := fun _ => 0, allowances := fun _ _ => 0 }
  , ext := {} }
def tokenCtxDeploy : Ctx := { sender := 1, self := 7 }
def tokenW1 : World Token.Storage ExtState Token.Event :=
  match Tx.run (Token.constructor tokenCtorOwner (Amount.ofWord tokenCtorSupply))
    tokenCtxDeploy tokenW0 with
  | .ok (_, w) => w
  | .error _ => tokenW0

def tokenCtorChecks : List Case :=
  [ tokWord "ctor_balanceOf" "balanceOf" [tokenCtorOwner] tokenCtxDeploy tokenW1.self
      ((Tx.run (Token.balanceOf tokenCtorOwner) tokenCtxDeploy tokenW1).map
        fun (n, w) => (n.raw, w))
  , tokWord "ctor_totalSupply" "totalSupply" [] tokenCtxDeploy tokenW1.self
      ((Tx.run Token.totalSupply tokenCtxDeploy tokenW1).map
        fun (n, w) => (n.raw, w)) ]

/-! ## WETH (payable deposit, Native.send withdraw) -/

def wnErr : WETH.Error → Nat
  | .InsufficientBalance => 0
  | .InsufficientAllowance => 1
  | .TransferFailed => 2

/-- Receiver for `withdraw_reject_value`. Not a precompile (`0x01`–`0x11`). -/
abbrev wnFe : Nat := 0x1000

def wnAddrs : List Nat := [0, 1, 2, wnFe]

def wnSlots (σ : WETH.Storage) : List (BitVec 256 × BitVec 256) :=
  wnAddrs.map (fun a => (mapSlot1 keccakOf 0 a, u256 (σ.balances a).raw)) ++
    wnAddrs.flatMap (fun a =>
      wnAddrs.map (fun b => (mapSlot2 keccakOf 1 a b, u256 (σ.allowances a b).raw))) ++
    [(u256 2, u256 σ.totalSupply.raw)]

def wnEmpty : WETH.Storage :=
  { balances := fun _ => 0, allowances := fun _ _ => 0, totalSupply := 0 }

def wnWrap1 : WETH.Storage :=
  { balances := fun a => Amount.ofWord (if a = (1 : Address) then 40 else 0)
    allowances := fun _ _ => 0
    totalSupply := 40 }

def wnWrapFe : WETH.Storage :=
  { balances := fun a => Amount.ofWord (if a = (0x1000 : Address) then 40 else 0)
    allowances := fun _ _ => 0
    totalSupply := 40 }

def wnAccept : Oracle ExtState where
  send _ _ x := some x

def wnW0 : World WETH.Storage ExtState WETH.Event := { self := wnEmpty, ext := {} }
def wnW1 : World WETH.Storage ExtState WETH.Event := { self := wnWrap1, ext := {} }
def wnW1s : World WETH.Storage ExtState WETH.Event :=
  { self := wnWrap1, ext := {}, oracle := wnAccept }
def wnWFe : World WETH.Storage ExtState WETH.Event := { self := wnWrapFe, ext := {} }

def wnCtx : Ctx := { sender := 1, self := 7 }
def wnCtxVal : Ctx := { sender := 1, value := 40, self := 7 }
def wnCtxFe : Ctx := { sender := wnFe, self := 7 }

def wnUnit (name fname : String) (args : List Nat) (ctx : Ctx) (σ : WETH.Storage)
    (tx : Except (Err WETH.Error) (Unit × World WETH.Storage ExtState WETH.Event))
    (value : Nat := 0) (selfBalance : Nat := 0)
    (setCode : List (Nat × String) := []) : Case :=
  let pre := wnSlots σ
  let postOk :=
    match tx with
    | .ok (_, w') => wnSlots w'.self
    | .error _ => pre
  { mkCase WETH.contract name fname args ctx.sender
      (unitOutcome WETH.contract wnErr tx pre postOk) pre with
    value, selfBalance, setCode }

def wnBool (name fname : String) (args : List Nat) (ctx : Ctx) (σ : WETH.Storage)
    (tx : Except (Err WETH.Error) (Bool × World WETH.Storage ExtState WETH.Event))
    (value : Nat := 0) : Case :=
  let pre := wnSlots σ
  let postOk :=
    match tx with
    | .ok (_, w') => wnSlots w'.self
    | .error _ => pre
  { mkCase WETH.contract name fname args ctx.sender
      (boolOutcome WETH.contract wnErr tx pre postOk) pre with value }

def wethCases : List Case :=
  [ wnUnit "deposit_ok" "deposit" [] wnCtxVal wnEmpty
      (Tx.run (@WETH.deposit Payable.entrypoint) wnCtxVal wnW0) (value := 40)
  , wnUnit "withdraw_ok" "withdraw" [10] wnCtx wnWrap1
      (Tx.run (WETH.withdraw 10) wnCtx wnW1s) (selfBalance := 1000)
  , wnBool "transfer_ok" "transfer" [2, 15] wnCtx wnWrap1
      (Tx.run (WETH.transfer 2 15) wnCtx wnW1)
  , { wnBool "transfer_value_revert" "transfer" [2, 15] wnCtx wnWrap1
        (Tx.run (WETH.transfer 2 15) wnCtx wnW1) with
      status := "revert", returnData := [], post := wnSlots wnWrap1, value := 1 }
  , wnUnit "withdraw_reject_value" "withdraw" [10] wnCtxFe wnWrapFe
      (Tx.run (WETH.withdraw 10) wnCtxFe wnWFe) (selfBalance := 1000)
      (setCode := [(wnFe, "0xfe")]) ]

/-- Fixed `anvil_setCode` address. `Ctx.self = 7` would be the ECMUL precompile
on a real EVM; Counter/Token do not read `ADDRESS`. -/
def runtimeAddress : String := addrHex 0xC0DE

def counterArt := compileContract Counter.contract
def tokenArt := compileContract Token.contract
def vaultArt := compileContract Vault.contract
def cpammArt := compileContract Cpamm.contract
def wethArt := compileContract WETH.contract

def exportJson : String :=
  "{" ++ String.intercalate "," [
    "\"runtime_address\":" ++ jStr runtimeAddress,
    "\"contracts\":[" ++ String.intercalate "," [
      contractJson "Counter" Counter.contract counterArt counterCases,
      contractJson "Token" Token.contract tokenArt tokenCases
        (some (ctorCalldata [tokenCtorOwner, tokenCtorSupply]))
        tokenCtorChecks,
      contractJson "Vault" Vault.contract vaultArt []
        (some (ctorCalldata [1, 10])),
      contractJson "Cpamm" Cpamm.contract cpammArt []
        (some (ctorCalldata [1, 10, 11])),
      contractJson "WETH" WETH.contract wethArt wethCases
    ] ++ "]"
  ] ++ "}"

def main : IO Unit := do
  writeContract "Counter" Counter.contract counterArt
  writeContract "Token" Token.contract tokenArt
  writeContract "Vault" Vault.contract vaultArt
  writeContract "Cpamm" Cpamm.contract cpammArt
  writeContract "WETH" WETH.contract wethArt
  IO.println "BEGIN_LSC_EXPORT"
  IO.println exportJson
  IO.println "END_LSC_EXPORT"

end ExportBytecode

open ExportBytecode

#eval main
