import LscV2.Lang.AST

namespace LscV2

def fnSignature (fn : FunctionDef) : String :=
  let params := String.intercalate "," (fn.params.map fun (n, t) => s!"{n}:{repr t}")
  s!"{fn.name}({params})"

/-- Stub selector: deterministic hash (Keccak deferred). -/
def computeSelector (fn : FunctionDef) : UInt32 :=
  fnSignature fn |>.hash.toUInt32

end LscV2
