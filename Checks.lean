import Examples.Counter.Theorems
import Examples.Token.Theorems
import Examples.Vault.Theorems
import Examples.Cpamm.Theorems
import Examples.WETH.Theorems
import Lsc.Security.WealthTheorems
import Lsc.Security.InvariantTheorems
import Lsc.Compiler.DispatchTheorems
import Lsc.Compiler.CoreTheorems
import Lsc.Compiler.CoreExtSimTheorems
import Lsc.Compiler.EndToEndTheorems
import Lsc.Compiler.EndToEndExtTheorems
import Lsc.Compiler.DispatchExtTheorems
import Lsc.Compiler.ProgressCoreTheorems
import Lsc.Compiler.ConstructorTheorems
import Lsc.Compiler.DeployTheorems

/-!
# Axiom and statement footprint checks

Every certificate and end-to-end theorem must depend on nothing beyond the three
standard axioms. `#guard_msgs` turns a widened footprint into a build error (see
`docs/internals/TRUSTED_COMPUTING_BASE.md`). Beside each axiom pin, an
`example` restates the theorem's type against `@thm`, so a silent weakening of
the statement fails the build. Agents update this file when a pinned theorem is
added, renamed, or has its statement changed; the commit message records why.
-/

set_option linter.unusedVariables false

open Lsc
open Lsc.Security
open Lsc.Stdlib
open Lsc.Compiler
open YulSemantics
open YulSemantics.EVM
open YulEvmCompiler

/-! ## Lsc.Security -/

/-- statement pin -/
example :
    ∀ (S X E ε : Type) (C : Spec S X E ε)
      [HasCreditValue X] [HasPayable C] [HasSelfBalance X]
      (Inv : World S X E → Prop) (claim : Claim S X E)
      (Auth : AuthPred C) (rely : World S X E → X → Prop) (self : Address)
      (hN : NoUnauthorizedDecrease C self Inv claim Auth)
      (hP : PreservesInv C self Inv) (hE : PreservesInvEnv C Inv rely)
      (hM : ClaimMonoEnv claim rely)
      (tr : List (Step C)) (w : World S X E) (a : Address)
      (hw : Inv w) (hR : RelyAlong self rely tr w)
      (hA : NoAuthAlong self Auth a tr w),
      claim a w ≤ claim a (run self tr w) :=
  @Lsc.Security.no_unauthorized_extraction

/-- info: 'Lsc.Security.no_unauthorized_extraction' depends on axioms: [propext] -/
#guard_msgs in #print axioms Lsc.Security.no_unauthorized_extraction

/-- statement pin -/
example :
    ∀ (X S E ε : Type) [HasCreditValue X] (C : Spec S X E ε)
      [HasPayable C] [HasSelfBalance X] [HasDeploy C]
      (Inv : World S X E → Prop) (rely : World S X E → X → Prop)
      (self : Address) (w : World S X E)
      (hD : ∀ w, Deployed C w → Inv w)
      (hP : PreservesInvAt C Inv self)
      (hE : PreservesInvEnv C Inv rely)
      (h : Reachable (C := C) rely self w),
      Inv w :=
  @Lsc.Security.inv_of_reachable

/-- info: 'Lsc.Security.inv_of_reachable' does not depend on any axioms -/
#guard_msgs in #print axioms Lsc.Security.inv_of_reachable

/-! ## Counter -/

/-- statement pin -/
example :
    ∀ (msg : Ctx) (w : Counter.World) (w' : Counter.World),
      Tx.run Counter.increment msg w = .ok ((), w') →
        w'.self.count = w.self.count + 1 :=
  @Counter.increment_adds

/-- info: 'Counter.increment_adds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Counter.increment_adds

/-! ## Token -/

/-- statement pin -/
example :
    ∀ (msg : Ctx) (w : Token.World) (dst : Address)
      (amount : Amount Token.tokenAsset) (w' : Token.World),
      Tx.run (Token.transfer dst amount) msg w = .ok (true, w') →
        w'.self.balances msg.sender + w'.self.balances dst =
          w.self.balances msg.sender + w.self.balances dst :=
  @Token.transfer_conserves

/-- info: 'Token.transfer_conserves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Token.transfer_conserves

/-- statement pin -/
example :
    ∀ (w : Token.State) (t : Txs w) (a : Address),
      w.self.balances a ≤ t.end.self.balances a + t.spent a :=
  @Token.token_no_unauthorized_extraction

/-- info: 'Token.token_no_unauthorized_extraction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Token.token_no_unauthorized_extraction

/-- statement pin -/
example :
    ∀ (w : Token.State) (A : Finset Address),
      ∑ a ∈ A, w.self.balances a ≤ w.self.totalSupply :=
  @Token.token_solvent

/-- info: 'Token.token_solvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Token.token_solvent

/-- statement pin -/
example : IERC20.Spec Token.impl :=
  @Token.token_spec

/-- info: 'Token.token_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Token.token_spec

/-! ## Vault -/

/-- statement pin -/
example :
    ∀ (w : Vault.State), w.owed ≤ w.holdings :=
  @Vault.vault_solvent

/-- info: 'Vault.vault_solvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Vault.vault_solvent

/-- statement pin -/
example :
    ∀ (w : Vault.State) (t : Txs w) (a : Address),
      w.self.shares a ≤ t.end.self.shares a + t.spent a :=
  @Vault.vault_no_unauthorized_extraction

/-- info: 'Vault.vault_no_unauthorized_extraction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Vault.vault_no_unauthorized_extraction

/-- statement pin -/
example :
    ∀ (w : Vault.State) (msg : Msg w) (assets : Amount Vault.vaultAsset)
      (minted : Amount Vault.vShare) (w' : Vault.World),
      Tx.run (Vault.deposit assets) msg w = .ok (minted, w') →
        Vault.holdingsAt w.addr w' = w.holdings + assets :=
  @Vault.deposit_holdings

/-- info: 'Vault.deposit_holdings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Vault.deposit_holdings

/-- statement pin -/
example :
    ∀ (w : Vault.State) (msg : Msg w) (sharesIn : Amount Vault.vShare)
      (paid : Amount Vault.vaultAsset) (w' : Vault.World),
      Tx.run (Vault.withdraw sharesIn) msg w = .ok (paid, w') →
        Vault.holdingsAt w.addr w' + paid = w.holdings :=
  @Vault.withdraw_holdings

/-- info: 'Vault.withdraw_holdings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Vault.withdraw_holdings

/-! ## Cpamm -/

/-- statement pin -/
example :
    ∀ (msg : Ctx) (w : Cpamm.World) (dx : Amount Cpamm.asset0)
      (minOut : Amount Cpamm.asset1) (out : Amount Cpamm.asset1)
      (w' : Cpamm.World),
      Tx.run (Cpamm.swap0for1 dx minOut) msg w = .ok (out, w') →
        w'.self.reserve0.raw * w'.self.reserve1.raw ≥
          w.self.reserve0.raw * w.self.reserve1.raw :=
  @Cpamm.swap0for1_k

/-- info: 'Cpamm.swap0for1_k' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Cpamm.swap0for1_k

/-- statement pin -/
example :
    ∀ (w : Cpamm.State),
      w.self.reserve0 + w.self.protocolFees0 ≤ w.holdings0 ∧
        w.self.reserve1 + w.self.protocolFees1 ≤ w.holdings1 :=
  @Cpamm.cpamm_solvent

/-- info: 'Cpamm.cpamm_solvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Cpamm.cpamm_solvent

/-- statement pin -/
example :
    ∀ (w : Cpamm.State) (t : Txs w) (a : Address),
      w.self.shares a ≤ t.end.self.shares a + t.spent a :=
  @Cpamm.cpamm_no_unauthorized_extraction

/-- info: 'Cpamm.cpamm_no_unauthorized_extraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Cpamm.cpamm_no_unauthorized_extraction

/-! ## WETH -/

/-- statement pin -/
example : IERC20.Exact WETH.impl :=
  @WETH.weth_exact

/-- info: 'WETH.weth_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WETH.weth_exact

/-- statement pin -/
example :
    ∀ (w : WETH.State), w.self.totalSupply ≤ w.nativeBalance :=
  @WETH.weth_backed

/-- info: 'WETH.weth_backed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WETH.weth_backed

/-- statement pin -/
example :
    ∀ (w : WETH.State) (t : Txs w) (a : Address),
      w.self.balances a ≤ t.end.self.balances a + t.spent a :=
  @WETH.weth_no_unauthorized_extraction

/-- info: 'WETH.weth_no_unauthorized_extraction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms WETH.weth_no_unauthorized_extraction

/-- statement pin -/
example :
    ∀ (msg : Ctx) (w : WETH.World) (w' : WETH.World),
      Tx.run WETH.depositTx msg w = .ok ((), w') →
        w'.self.balances msg.sender =
            w.self.balances msg.sender + ⟨msg.value⟩ ∧
          w'.self.totalSupply = w.self.totalSupply + ⟨msg.value⟩ ∧
          World.nativeBalance w' = World.nativeBalance w :=
  @WETH.deposit_delta

/-- info: 'WETH.deposit_delta' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms WETH.deposit_delta

/-- statement pin -/
example :
    ∀ (msg : Ctx) (w : WETH.World) (amount : Amount WETH.native)
      (w' : WETH.World),
      Tx.run (WETH.withdraw amount) msg w = .ok ((), w') →
        w'.self.balances msg.sender + amount = w.self.balances msg.sender ∧
          w'.self.totalSupply + amount = w.self.totalSupply :=
  @WETH.withdraw_delta

/-- info: 'WETH.withdraw_delta' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms WETH.withdraw_delta

/-! ## Compiler -/

/-- statement pin -/
example :
    ∀ (S X E ε : Type) (c : ContractDef) (Γ : ContractSchema S X E ε)
      (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
      (f : FnDef) (hf : f.kind ≠ .constructor)
      (hM1 : CallFree f.core) (hlen : c.fields.length < wordBound)
      (hbound : 4 + 32 * f.params.length < wordBound)
      (yul : YBlock) (hyul : toYulFn c f = some yul)
      (ctx : Ctx) (w : World S X E) (st0 : EvmState)
      (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0),
      ToYulFnCorrect c Γ κ f yul ctx w st0 :=
  @Lsc.Compiler.toYulFn_correct_callFree

/-- info: 'Lsc.Compiler.toYulFn_correct_callFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.toYulFn_correct_callFree

/-- statement pin -/
example :
    ∀ (S E ε : Type) (c : ContractDef) (Γ : ContractSchema S ExtState E ε)
      (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
      (o : ExtOracle) (f : FnDef) (hf : f.kind ≠ .constructor)
      (hS2 : S2Frag f.core) (hlen : c.fields.length < wordBound)
      (hbound : 4 + 32 * f.params.length < wordBound)
      (yul : YBlock) (hyul : toYulFn c f = some yul)
      (ctx : Ctx) (w : World S ExtState E) (st0 : EvmState)
      (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0)
      (hAgr : ExtAgree ctx.self w.ext st0)
      (hOr : w.oracle = Oracle.ofExt o),
      ToYulFnCorrectExt c Γ κ o f yul ctx w st0 :=
  @Lsc.Compiler.toYulFn_correct_ext

/-- info: 'Lsc.Compiler.toYulFn_correct_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.toYulFn_correct_ext

/-- statement pin -/
example :
    ∀ (tag : String) (S E ε : Type) (c : ContractDef)
      (Γ : ContractSchema S ExtState E ε) (κ : List UInt8 → U256)
      (ctx : Ctx) (haltUnit : Bool) (o : ExtOracle)
      (hhalt : haltUnit = true) (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c κ)
      (hlen : c.fields.length < wordBound)
      (t : RetTy) (core : Core t) (hM1 : CallFree core),
      SimExt tag c Γ κ o ctx haltUnit core :=
  @Lsc.Compiler.core_sim_ext_callFree

/-- info: 'Lsc.Compiler.core_sim_ext_callFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.core_sim_ext_callFree

/-- statement pin -/
example :
    ∀ (S X E ε : Type) (c : ContractDef) (Γ : ContractSchema S X E ε)
      (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
      (hcf : ∀ f ∈ c.functions, CallFree f.core)
      (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
      (hlen : c.fields.length < wordBound)
      (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
      (yul : YBlock) (hyul : runtimeBlock c = some yul)
      (ctx : Ctx) (w : World S X E) (st0 : EvmState)
      (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0) (hLock : LockFree st0),
      RuntimeBlockCorrectCallFree c Γ κ yul ctx w st0 :=
  @Lsc.Compiler.runtimeBlock_correct_callFree

/-- info: 'Lsc.Compiler.runtimeBlock_correct_callFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.runtimeBlock_correct_callFree

/-- statement pin -/
example :
    ∀ (S X E ε : Type) (c : ContractDef) (Γ : ContractSchema S X E ε)
      (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
      (hcf : ∀ f ∈ c.functions, CallFree f.core)
      (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
      (hlen : c.fields.length < wordBound)
      (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
      (rt : YBlock) (hrt : runtimeBlock c = some rt)
      (is : List Instr) (hcomp : compileBlock rt = some is)
      (ctx : Ctx) (w : World S X E) (yst0 : EvmState)
      (hctx : ctxRel ctx yst0) (hR : R c Γ evmKeccak w yst0)
      (himm0 : ∀ k, yst0.env.immutable k = 0) (hLock : LockFree yst0),
      BytecodeCallCorrect c Γ evmKeccak ctx w yst0 is :=
  @Lsc.Compiler.bytecode_call_correct

/-- info: 'Lsc.Compiler.bytecode_call_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.bytecode_call_correct

/-- statement pin -/
example :
    ∀ (S E ε : Type) (c : ContractDef) (Γ : ContractSchema S ExtState E ε)
      (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
      (o : ExtOracle)
      (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
      (hS2 : ∀ f ∈ c.functions, S2Frag f.core)
      (hlen : c.fields.length < wordBound)
      (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
      (yul : YBlock) (hyul : runtimeBlock c = some yul)
      (ctx : Ctx) (w : World S ExtState E) (st0 : EvmState)
      (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0)
      (hAgr : ExtAgree ctx.self w.ext st0)
      (hOr : w.oracle = Oracle.ofExt o)
      (hLock : LockFree st0),
      RuntimeBlockCorrectExt c Γ κ o yul ctx w st0 :=
  @Lsc.Compiler.runtimeBlock_correct_ext

/-- info: 'Lsc.Compiler.runtimeBlock_correct_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.runtimeBlock_correct_ext

/-- statement pin -/
example :
    ∀ (S E ε : Type) (c : ContractDef) (Γ : ContractSchema S ExtState E ε)
      (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
      (o : ExtOracle) (hCalls : CallsRealized (toCalls o))
      (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
      (hS2 : ∀ f ∈ c.functions, S2Frag f.core)
      (hlen : c.fields.length < wordBound)
      (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
      (rt : YBlock) (hrt : runtimeBlock c = some rt)
      (is : List Instr) (hcomp : compileBlock rt = some is)
      (ctx : Ctx) (w : World S ExtState E) (yst0 : EvmState)
      (hctx : ctxRel ctx yst0) (hR : R c Γ evmKeccak w yst0)
      (hAgr : ExtAgree ctx.self w.ext yst0)
      (hOr : w.oracle = Oracle.ofExt o)
      (himm0 : ∀ k, yst0.env.immutable k = 0)
      (hLock : LockFree yst0),
      BytecodeCallCorrectExt c Γ evmKeccak o ctx w yst0 rt is :=
  @Lsc.Compiler.bytecode_call_correct_ext

/-- info: 'Lsc.Compiler.bytecode_call_correct_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.bytecode_call_correct_ext

/-- statement pin -/
example :
    ∀ (S E ε : Type) (c : ContractDef) (Γ : ContractSchema S ExtState E ε)
      (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
      (o : ExtOracle)
      (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
      (hS2 : ∀ f ∈ c.functions, S2Frag f.core)
      (hlen : c.fields.length < wordBound)
      (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
      (yul : YBlock) (hyul : runtimeBlock c = some yul)
      (ctx : Ctx) (w : World S ExtState E) (st0 : EvmState)
      (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0),
      ∃ st' out, Run (yulD (toCalls o))
        (YulEvmCompiler.Optimizer.MemorySpill.eraseMemoryGuardStmts yul)
        st0 [] st' out :=
  @Lsc.Compiler.yul_progress

/-- info: 'Lsc.Compiler.yul_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.yul_progress

/-- statement pin -/
example :
    ∀ (S E ε : Type) (c : ContractDef) (Γ : ContractSchema S ExtState E ε)
      (hΓ : Γ.st.Lawful c.fields) (hκ : KeccakSep c evmKeccak)
      (o : ExtOracle) (hCalls : CallsRealized (toCalls o))
      (hctor : ∀ f ∈ c.functions, f.kind ≠ .constructor)
      (hS2 : ∀ f ∈ c.functions, S2Frag f.core)
      (hlen : c.fields.length < wordBound)
      (hbound : ∀ f ∈ c.functions, 4 + 32 * f.params.length < wordBound)
      (rt : YBlock) (hrt : runtimeBlock c = some rt)
      (is : List Instr) (hcomp : compileBlock rt = some is)
      (ctx : Ctx) (w : World S ExtState E) (yst0 : EvmState)
      (hctx : ctxRel ctx yst0) (hR : R c Γ evmKeccak w yst0)
      (hAgr : ExtAgree ctx.self w.ext yst0)
      (hOr : w.oracle = Oracle.ofExt o)
      (himm0 : ∀ k, yst0.env.immutable k = 0)
      (hLock : LockFree yst0),
      ∃ σ' ξ', EvmCallRunExtAll c Γ evmKeccak o ctx w is yst0 σ' ξ' :=
  @Lsc.Compiler.evmCallRunExtAll_of_progress

/-- info: 'Lsc.Compiler.evmCallRunExtAll_of_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.evmCallRunExtAll_of_progress

/-- statement pin -/
example :
    ∀ (S X E ε : Type) (c : ContractDef) (Γ : ContractSchema S X E ε)
      (hΓ : Γ.st.Lawful c.fields) (κ : List UInt8 → U256) (hκ : KeccakSep c κ)
      (f : FnDef) (hk : f.kind = .constructor) (hret : f.ret = .unit)
      (hM1 : CallFree f.core) (hNo : NoIte f.core)
      (hlen : c.fields.length < wordBound)
      (hbound : 32 * f.params.length < wordBound)
      (hptr : abiPtr + 32 * f.params.length < wordBound)
      (yul : YBlock) (hyul : toYulCtor c f = some yul)
      (ctx : Ctx) (w : World S X E) (st0 : EvmState)
      (hctx : ctxRel ctx st0) (hR : R c Γ κ w st0)
      (hle : 32 * f.params.length ≤ st0.env.code.length)
      (hcode : st0.env.code.length < wordBound),
      ConstructorCorrect c Γ κ f yul ctx w st0 :=
  @Lsc.Compiler.constructor_correct

/-- info: 'Lsc.Compiler.constructor_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.constructor_correct

/-- statement pin -/
example :
    ∀ (model : ExternalModel) (hexternal : ExternalsRealized model)
      (o : Object YulSemantics.EVM.Op) (L : Layout)
      (hcomp : compileObject o = some L)
      (V : VEnv (evmWithExternal model.calls model.creates model.gas))
      (yst : EvmState) (out : Outcome)
      (hrun : RunResolvedObject o L V yst out),
      ∃ b : Nat, ∀ s0 : EvmSemantics.EVM.State,
        FrameOK (mkCode L.code) s0 → StateMatch L.initState s0 →
          s0.pc = EvmSemantics.UInt256.ofNat 0 → s0.stack = [] →
            b ≤ s0.gasAvailable →
              ∃ s', EvmSemantics.EVM.Steps s0 s' ∧ s'.callStack = [] ∧
                StateMatch yst s' ∧
                  ((out = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
                    (out = .halt ∧ HaltedMatch yst s')) :=
  @Lsc.Compiler.bytecode_deploy_correct

/-- info: 'Lsc.Compiler.bytecode_deploy_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lsc.Compiler.bytecode_deploy_correct
