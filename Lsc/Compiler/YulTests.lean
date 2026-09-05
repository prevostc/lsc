import Lsc.Compiler.Yul
import Lsc.Compiler.YulExec
import Lsc.Compiler.Bytecode
import Lsc.Examples.Counter
import Lsc.Examples.Token
import YulEvmCompiler.Compile

set_option maxHeartbeats 8000000


/-!
# Differential tests: `Tx.run` vs `Interp.run` on emitted Yul

Each case checks success/revert, return words, and storage on the slots the call
touches. Mapping slots use `keccakOf` (KeccakEngine).
-/

namespace Lsc.Compiler.YulTests

open Lsc
open Lsc.Compiler
open YulSemantics.EVM (HaltKind U256)

def fnNamed (c : ContractDef) (n : String) : Option FnDef :=
  c.functions.find? (fun f => f.name = n)

def slotsEq (pairs : List (U256 × U256)) (st : U256 → U256) : Bool :=
  pairs.all fun p => st p.1 == p.2

def haltEq (y : RunOut) (k : HaltKind) (bs : List UInt8) : Bool :=
  !y.stuck && y.halt == some (k, bs)

def checkUnitOk (y : RunOut) (post : List (U256 × U256)) : Bool :=
  haltEq y .stop [] && slotsEq post y.storage

def checkWordOk (y : RunOut) (n : Nat) (post : List (U256 × U256)) : Bool :=
  haltEq y .ret (abiBytes [n]) && slotsEq post y.storage

def checkRevert (y : RunOut) (bs : List UInt8) (pre : List (U256 × U256)) : Bool :=
  haltEq y .revert bs && slotsEq pre y.storage

def runFn (c : ContractDef) (f : FnDef) (args : List Nat)
    (store : U256 → U256) (ctx : Ctx) : Option RunOut :=
  runContract c (fnCalldata f args) store ctx

/-! ## Counter -/

def ctrW (n : Nat) : World Counter.Storage Unit Counter.Event :=
  { self := { count := n }, ext := () }

def ctrSlots (n : Nat) : List (U256 × U256) :=
  [(u256 0, u256 n)]

def ctrStore (n : Nat) : U256 → U256 := storageOf (ctrSlots n)

def ctx1 : Ctx := { sender := 1, self := 7 }

def checkCtrUnit (fname : String) (args : List Nat) (count : Nat)
    (tx : Except (Err Counter.Error) (Unit × World Counter.Storage Unit Counter.Event)) : Bool :=
  match fnNamed Counter.contract fname with
  | none => false
  | some f =>
    let pre := ctrSlots count
    match runFn Counter.contract f args (ctrStore count) ctx1 with
    | none => false
    | some y =>
      match tx with
      | .ok (_, w') => checkUnitOk y (ctrSlots w'.self.count)
      | .error (.user .Zero) =>
        checkRevert y (customErrorBytes Counter.contract 0 []) pre
      | .error (.arith a) =>
        checkRevert y (panicBytes (arithPanicCode a)) pre
      | .error .callFailed => false

def checkCtrWord (fname : String) (args : List Nat) (count : Nat)
    (tx : Except (Err Counter.Error) (Nat × World Counter.Storage Unit Counter.Event)) : Bool :=
  match fnNamed Counter.contract fname with
  | none => false
  | some f =>
    match runFn Counter.contract f args (ctrStore count) ctx1 with
    | none => false
    | some y =>
      match tx with
      | .ok (v, w') => checkWordOk y v (ctrSlots w'.self.count)
      | .error (.user .Zero) =>
        checkRevert y (customErrorBytes Counter.contract 0 []) (ctrSlots count)
      | .error (.arith a) =>
        checkRevert y (panicBytes (arithPanicCode a)) (ctrSlots count)
      | .error .callFailed => false

def counter_increment_ok : Bool :=
  checkCtrUnit "increment" [] 5 (Tx.run Counter.increment ctx1 (ctrW 5))

def counter_increment_overflow : Bool :=
  checkCtrUnit "increment" [] (wordBound - 1)
    (Tx.run Counter.increment ctx1 (ctrW (wordBound - 1)))

def counter_incrementBy_ok : Bool :=
  checkCtrUnit "incrementBy" [3] 5 (Tx.run (Counter.incrementBy 3) ctx1 (ctrW 5))

def counter_incrementBy_zero : Bool :=
  checkCtrUnit "incrementBy" [0] 5 (Tx.run (Counter.incrementBy 0) ctx1 (ctrW 5))

def counter_decrement_from_zero : Bool :=
  checkCtrUnit "decrement" [] 0 (Tx.run Counter.decrement ctx1 (ctrW 0))

def counter_decrement_ok : Bool :=
  checkCtrUnit "decrement" [] 5 (Tx.run Counter.decrement ctx1 (ctrW 5))

def counter_get : Bool :=
  checkCtrWord "get" [] 42 (Tx.run Counter.get ctx1 (ctrW 42))

def counterAll : List (String × Bool) :=
  [ ("increment_ok", counter_increment_ok)
  , ("increment_overflow", counter_increment_overflow)
  , ("incrementBy_ok", counter_incrementBy_ok)
  , ("incrementBy_zero", counter_incrementBy_zero)
  , ("decrement_from_zero", counter_decrement_from_zero)
  , ("decrement_ok", counter_decrement_ok)
  , ("get", counter_get) ]

/-! ## Token (call-free entrypoints) -/

def tokW (owner supply : Nat) (bals : Nat → Nat) (allows : Nat → Nat → Nat) :
    World Token.Storage Unit Token.Event :=
  { self := { owner := owner, totalSupply := supply, balances := bals, allowances := allows },
    ext := () }

def tokAddrs : List Nat := [0, 1, 2, 3]

def tokSlots (σ : Token.Storage) : List (U256 × U256) :=
  [(u256 0, u256 σ.owner), (u256 1, u256 σ.totalSupply)] ++
    tokAddrs.map (fun a => (mapSlot1 keccakOf 2 a, u256 (σ.balances a))) ++
    tokAddrs.flatMap (fun a =>
      tokAddrs.map (fun b => (mapSlot2 keccakOf 3 a b, u256 (σ.allowances a b))))

def tokStore (σ : Token.Storage) : U256 → U256 := storageOf (tokSlots σ)

def bals₁ : Nat → Nat
  | 1 => 1000
  | _ => 0

def allow₀ : Nat → Nat → Nat
  | _, _ => 0

def allow₁₂ : Nat → Nat → Nat
  | 1, 2 => 200
  | _, _ => 0

def σ₁ : Token.Storage := { owner := 1, totalSupply := 1000, balances := bals₁, allowances := allow₀ }

def σAllow : Token.Storage := { σ₁ with allowances := allow₁₂ }

def w₁ : World Token.Storage Unit Token.Event := { self := σ₁, ext := () }
def wAllow : World Token.Storage Unit Token.Event := { self := σAllow, ext := () }

def ctxOwner : Ctx := { sender := 1, self := 7 }
def ctx2 : Ctx := { sender := 2, self := 7 }

def checkTokUnit (fname : String) (args : List Nat) (ctx : Ctx) (σ : Token.Storage)
    (tx : Except (Err Token.Error) (Unit × World Token.Storage Unit Token.Event)) : Bool :=
  match fnNamed Token.contract fname with
  | none => false
  | some f =>
    let pre := tokSlots σ
    match runFn Token.contract f args (tokStore σ) ctx with
    | none => false
    | some y =>
      match tx with
      | .ok (_, w') => checkUnitOk y (tokSlots w'.self)
      | .error (.user .InsufficientBalance) =>
        checkRevert y (customErrorBytes Token.contract 0 []) pre
      | .error (.user .InsufficientAllowance) =>
        checkRevert y (customErrorBytes Token.contract 1 []) pre
      | .error (.user .NotOwner) =>
        checkRevert y (customErrorBytes Token.contract 2 []) pre
      | .error (.arith a) =>
        checkRevert y (panicBytes (arithPanicCode a)) pre
      | .error .callFailed => false

def checkTokWord (fname : String) (args : List Nat) (ctx : Ctx) (σ : Token.Storage)
    (tx : Except (Err Token.Error) (Nat × World Token.Storage Unit Token.Event)) : Bool :=
  match fnNamed Token.contract fname with
  | none => false
  | some f =>
    match runFn Token.contract f args (tokStore σ) ctx with
    | none => false
    | some y =>
      match tx with
      | .ok (v, w') => checkWordOk y v (tokSlots w'.self)
      | .error (.user .InsufficientBalance) =>
        checkRevert y (customErrorBytes Token.contract 0 []) (tokSlots σ)
      | .error (.user .InsufficientAllowance) =>
        checkRevert y (customErrorBytes Token.contract 1 []) (tokSlots σ)
      | .error (.user .NotOwner) =>
        checkRevert y (customErrorBytes Token.contract 2 []) (tokSlots σ)
      | .error (.arith a) =>
        checkRevert y (panicBytes (arithPanicCode a)) (tokSlots σ)
      | .error .callFailed => false

def token_transfer_ok : Bool :=
  checkTokUnit "transfer" [2, 100] ctxOwner σ₁ (Tx.run (Token.transfer 2 100) ctxOwner w₁)

def token_transfer_revert : Bool :=
  checkTokUnit "transfer" [2, 2000] ctxOwner σ₁ (Tx.run (Token.transfer 2 2000) ctxOwner w₁)

def token_approve_ok : Bool :=
  checkTokUnit "approve" [2, 50] ctxOwner σ₁ (Tx.run (Token.approve 2 50) ctxOwner w₁)

def token_transferFrom_ok : Bool :=
  checkTokUnit "transferFrom" [1, 3, 40] ctx2 σAllow
    (Tx.run (Token.transferFrom 1 3 40) ctx2 wAllow)

def token_mint_ok : Bool :=
  checkTokUnit "mint" [2, 25] ctxOwner σ₁ (Tx.run (Token.mint 2 25) ctxOwner w₁)

def token_mint_notOwner : Bool :=
  checkTokUnit "mint" [2, 25] ctx2 σ₁ (Tx.run (Token.mint 2 25) ctx2 w₁)

def token_burn_ok : Bool :=
  checkTokUnit "burn" [30] ctxOwner σ₁ (Tx.run (Token.burn 30) ctxOwner w₁)

def token_burn_revert : Bool :=
  checkTokUnit "burn" [2000] ctxOwner σ₁ (Tx.run (Token.burn 2000) ctxOwner w₁)

def token_balanceOf : Bool :=
  checkTokWord "balanceOf" [1] ctxOwner σ₁ (Tx.run (Token.balanceOf 1) ctxOwner w₁)

def token_allowance : Bool :=
  checkTokWord "allowance" [1, 2] ctxOwner σAllow (Tx.run (Token.allowance 1 2) ctxOwner wAllow)

def token_totalSupply : Bool :=
  checkTokWord "totalSupply" [] ctxOwner σ₁ (Tx.run Token.totalSupply ctxOwner w₁)

def tokenAll : List (String × Bool) :=
  [ ("transfer_ok", token_transfer_ok)
  , ("transfer_revert", token_transfer_revert)
  , ("approve_ok", token_approve_ok)
  , ("transferFrom_ok", token_transferFrom_ok)
  , ("mint_ok", token_mint_ok)
  , ("mint_notOwner", token_mint_notOwner)
  , ("burn_ok", token_burn_ok)
  , ("burn_revert", token_burn_revert)
  , ("balanceOf", token_balanceOf)
  , ("allowance", token_allowance)
  , ("totalSupply", token_totalSupply) ]

def allPass (cs : List (String × Bool)) : Bool := cs.all (·.2)

def failed (cs : List (String × Bool)) : List String :=
  cs.filterMap fun p => if p.2 then none else some p.1

def counter_runtime_some : Bool := (runtimeBlock Counter.contract).isSome
def token_runtime_some : Bool := (runtimeBlock Token.contract).isSome
def counter_deploy_some : Bool := (deployObject Counter.contract).isSome
def token_deploy_some : Bool := (deployObject Token.contract).isSome

def bytecode_counter_runtime_some : Bool := (compileRuntime Counter.contract).isSome
def bytecode_token_runtime_some : Bool := (compileRuntime Token.contract).isSome
def bytecode_counter_deploy_some : Bool := (compileDeploy Counter.contract).isSome
def bytecode_token_deploy_some : Bool := (compileDeploy Token.contract).isSome

def compileStatus (c : ContractDef) : String :=
  match runtimeBlock c with
  | none => "runtimeBlock none"
  | some b =>
    match YulEvmCompiler.compileProgram b with
    | none => "compileProgram none"
    | some asm =>
      let opt := YulEvmCompiler.optimizeAsm asm
      if YulEvmCompiler.stackOK2 opt then "ok"
      else "stackOK2 failed"

end Lsc.Compiler.YulTests

open Lsc.Compiler.YulTests

#eval failed counterAll
#eval failed tokenAll
#eval compileStatus Counter.contract
#eval compileStatus Token.contract

#guard counter_runtime_some
#guard token_runtime_some
#guard counter_deploy_some
#guard token_deploy_some

#guard allPass counterAll
#guard allPass tokenAll

#eval (Lsc.Compiler.compileRuntime Counter.contract).map List.length
#eval (Lsc.Compiler.compileDeploy Counter.contract).map List.length
#eval (Lsc.Compiler.compileRuntime Token.contract).map List.length
#eval (Lsc.Compiler.compileDeploy Token.contract).map List.length

#guard bytecode_counter_runtime_some
#guard bytecode_token_runtime_some
#guard bytecode_counter_deploy_some
#guard bytecode_token_deploy_some
