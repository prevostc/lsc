import LscV2.AST

namespace LscV2.Compile

/-- ABI selector = first 4 bytes of keccak256(signature); stub uses String.hash for now. -/
def computeSelector (fn : FunctionDef) : UInt32 :=
  let params := String.intercalate "," (fn.params.map fun (n, t) => s!"{n}:{repr t}")
  s!"{fn.name}({params})".hash.toUInt32

def externalSelectors (c : ContractDef) : List (Ident × UInt32) :=
  c.functions.filter (·.kind == .external) |>.map fun fn => (fn.name, computeSelector fn)

/-- Skeleton dispatch table: selector → function name. -/
def dispatchTable (c : ContractDef) : List (UInt32 × Ident) :=
  externalSelectors c |>.map fun (name, sel) => (sel, name)

end LscV2.Compile
