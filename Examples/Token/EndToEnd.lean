import Lsc.Compiler.TransportTheorems
import Examples.Token.CompileTheorems
import Examples.Token.Security
import Examples.Token.SecurityTheorems
import YulEvmCompiler.Compile

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

/-!
Bytecode-level Token theorems via `Transport`. Main theorems are universal over
arbitrary halted calldata (`EvmTraceRunAll`); `_exists` encodes a Security trace.
Trace-predicted-calldata forms are dropped.
-/

open Lsc Lsc.Compiler Lsc.Security Token
open YulSemantics.EVM
open YulEvmCompiler (compile Instr)

lsc_codec Token

namespace Token

def mkTokenSetup (hκ : KeccakSep Token.contract evmKeccak)
    (rt : YBlock) (hrt : runtimeBlock Token.contract = some rt)
    (is : List Instr) (hcomp : compile rt = some is) :
    TransportSetup Storage Unit Event Error where
  c := Token.contract
  Γ := Token.schema
  spec := Token.spec
  codec := Token.codec
  lawful := Token.schema_lawful
  hκ := hκ
  hctor := fun f hf => token_fn_not_ctor hf
  hlen := token_fields_lt
  hbound := fun f hf => token_fn_params_bound hf
  rt := rt
  hrt := hrt
  is := is
  hcomp := hcomp

theorem token_noAuthAlong_callsOf (a : Address) (tr : List (Step spec))
    (w : World Storage Unit Event) (h : NoAuthAlong Auth a tr w) :
    NoAuthAlong Auth a (callsOf tr) w := by
  induction tr generalizing w with
  | nil => trivial
  | cons s rest ih =>
    match s with
    | .env x' =>
      have hw : { w with ext := x' } = w := by cases w.ext; cases x'; rfl
      simpa [callsOf, hw] using ih (w := { w with ext := x' }) (by simpa [NoAuthAlong] using h)
    | .call c =>
      rcases h with ⟨hAc, hAtl⟩
      exact ⟨hAc, ih (w := step (.call c) w) hAtl⟩

theorem token_balances_fd :
    Token.contract.fields[2]? =
      some { name := "balances", kind := .map1, ty := .uint256 } := by
  simp [Token.contract]

theorem token_schema_balances (s : Storage) (k : Address) :
    Token.schema.st.map1 2 s k = s.balances k := rfl

theorem token_claim_slot (s : Storage) (σ : U256 → U256) (a : Address)
    (hs : storageRel Token.contract Token.schema evmKeccak s σ)
    (ha : Nat.lt a wordBound) (hb : s.balances a < wordBound) :
    (σ (mapSlot1 evmKeccak 2 a)).toNat = claim a s := by
  simpa [claim, token_schema_balances] using
    storageRel_map1_toNat hs token_balances_fd rfl (by rw [token_schema_balances]) ha hb

theorem token_map1_bound (w : World Storage Unit Event) (a : Address)
    (hwf : WorldWF Token.contract Token.schema w) (ha : Nat.lt a wordBound) :
    w.self.balances a < wordBound := by
  have h := hwf 2 _ token_balances_fd a ha
  simpa [token_schema_balances] using h

end Token
