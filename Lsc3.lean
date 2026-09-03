import Lsc3.Tx
import Lsc3.Amount
import Lsc3.Core
import Lsc3.Reify
import Lsc3.Contract
import Lsc3.EVM.State
import Lsc3.EVM.Step
import Lsc3.EVM.Lemmas
import Lsc3.EVM.EvmYulRefinement
import Lsc3.Compile.Contract
import Lsc3.Compile.Exec
import Lsc3.Compile.GetBody
import Lsc3.Compile.Dispatch
import Lsc3.Compile.DispatchGet
import Lsc3.Compile.CalldataCheck
import Lsc3.Compile.GetContract
import Lsc3.Compile.GetMiss
import Lsc3.Compile.IncBody
import Lsc3.Compile.IncByBody
import Lsc3.Compile.IncByHit
import Lsc3.Compile.IncByOverflow
import Lsc3.Compile.DecBody
import Lsc3.Compile.DecHit
import Lsc3.Compile.IncOverflow
import Lsc3.Compile.GetInc
import Lsc3.Compile.GetIncHit
import Lsc3.Compile.GetIncIncHit
import Lsc3.Compile.Cert
import Lsc3.Examples.Counter
import Lsc3.Examples.CounterCert
import Lsc3.Examples.Token
import Lsc3.Examples.TokenProofs
import Lsc3.Examples.Vault
import Lsc3.Examples.VaultProofs
import Lsc3.Examples.CounterEndToEnd
import Lsc3.Examples.TokenEndToEnd
import Lsc3.Examples.VaultEndToEnd

/-!
# LSC v3

Shallow Lean surface (`Lsc3.Tx`), certified reification to a tiny ANF core (`Lsc3.Core`,
`Lsc3.Reify`), Core→EVM codegen (`Lsc3.Compile`) with per-contract assembly (`lsc_contract`),
and an executable subset machine (`Lsc3.EVM`) that runs the emitted bytecode.
-/
