import Lsc.Lang.AST
import KeccakEngine.Sponge

namespace Lsc

/-- Render a `Ty` as its ABI type string. -/
def Ty.abiStr : Ty → String
  | .uint256 => "uint256"
  | .bool    => "bool"
  | .address => "address"
  | .wei     => "uint256"
  | .wad     => "uint256"
  | .unit    => ""

/-- Build the canonical ABI function signature, e.g. `"increment()"` or `"transfer(address,uint256)"`. -/
def fnSignature (fn : FunctionDef) : String :=
  let params := String.intercalate "," (fn.params.map fun (_, t) => t.abiStr)
  s!"{fn.name}({params})"

/-- Compute the 4-byte EVM ABI selector via Keccak256.
    selector = keccak256(fnSignature)[0:4] interpreted as big-endian UInt32. -/
def computeSelector (fn : FunctionDef) : UInt32 :=
  let sig  := fnSignature fn
  let hash := KeccakEngine.keccak256 sig.toUTF8
  -- Pack first 4 bytes big-endian into UInt32
  if h : hash.size >= 4 then
    let b0 := (hash[0]'(by omega)).toUInt32
    let b1 := (hash[1]'(by omega)).toUInt32
    let b2 := (hash[2]'(by omega)).toUInt32
    let b3 := (hash[3]'(by omega)).toUInt32
    (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3
  else 0

/-- Compute an ABI selector from a function name and parameter types directly. -/
def computeSelectorFromParams (name : String) (paramTys : List Ty) : UInt32 :=
  let params := paramTys.map fun ty => ("_", ty)
  computeSelector ⟨name, .external, params, .unit, .skip, false⟩

/-- Build the canonical ABI event signature, e.g. `"Incremented(uint256)"` — same shape as
    `fnSignature`, but for a `derive_contract_def`-derived event entry
    (`(name, params) : Ident × List (Ident × Ty)`, see `ContractDef.events`). -/
def eventSignature (name : String) (params : List (Ident × Ty)) : String :=
  let types := String.intercalate "," (params.map fun (_, t) => t.abiStr)
  s!"{name}({types})"

/-- Compute the full 256-bit LOG topic0 via Keccak256, e.g. Solidity's
    `keccak256("Incremented(uint256)")` — big-endian bytes packed into a `Nat`
    (arbitrary precision, so no truncation like `computeSelector`'s 4-byte selector). -/
def computeEventTopic0 (name : String) (params : List (Ident × Ty)) : Nat :=
  let hash := KeccakEngine.keccak256 (eventSignature name params).toUTF8
  hash.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Build the canonical ABI custom-error signature, e.g. `"NotOwner()"` or `"Overflow(uint256)"`. -/
def errorSignature (name : String) (params : List (Ident × Ty)) : String :=
  let types := String.intercalate "," (params.map fun (_, t) => t.abiStr)
  s!"{name}({types})"

/-- Compute the 4-byte EVM ABI custom-error selector via Keccak256
    (`keccak256(errorSignature)[0:4]`, same rule as function selectors). -/
def computeErrorSelector (name : String) (params : List (Ident × Ty)) : UInt32 :=
  let sig := errorSignature name params
  let hash := KeccakEngine.keccak256 sig.toUTF8
  if h : hash.size >= 4 then
    let b0 := (hash[0]'(by omega)).toUInt32
    let b1 := (hash[1]'(by omega)).toUInt32
    let b2 := (hash[2]'(by omega)).toUInt32
    let b3 := (hash[3]'(by omega)).toUInt32
    (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3
  else 0

end Lsc
