import Lsc.Lang.Tx
import Lsc.Lang.Amount
import Lsc.Lang.Interface
import Lsc.Stdlib.ERC20
import Lsc.Lang.Core
import Lsc.Lang.Spec
import Lsc.Lang.Reify
import Lsc.Lang.Contract
import Lsc.Tools.AbiJson
import Lsc.Examples.Counter
import Lsc.Examples.AmountDemo
import Lsc.Examples.Token
import Lsc.Examples.TokenProofs
import Lsc.Examples.TokenSecurity
import Lsc.Examples.Vault
import Lsc.Examples.VaultProofs
import Lsc.Examples.VaultSecurity
import Lsc.Compiler.Yul
import Lsc.Compiler.YulExec
import Lsc.Compiler.Bytecode
import Lsc.Compiler.YulTests
import Lsc.Security.Trace
import Lsc.Security.Invariant
import Lsc.Security.Wealth

/-!
# LSC — a provable DeFi language compiling to EVM

Shallow Lean surface (`Lsc.Lang.Tx`), certified reification to a tiny ANF core
(`Lsc.Lang.Core`, `Lsc.Lang.Reify`), a security model over traces (`Lsc.Security`), and a
Core → Yul compiler (`Lsc.Compiler`) composed with powdr's verified Yul → EVM compiler.

See `docs/architecture/` for the decision records.
-/
