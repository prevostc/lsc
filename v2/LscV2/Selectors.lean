import LscV2.Lang.AST
import KeccakEngine.Sponge

namespace LscV2

/-- Render a `Ty` as its ABI type string. -/
def Ty.abiStr : Ty → String
  | .uint256 => "uint256"
  | .bool    => "bool"
  | .address => "address"
  | .wei     => "uint256"
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

end LscV2
