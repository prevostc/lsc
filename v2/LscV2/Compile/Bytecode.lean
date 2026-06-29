import LscV2.Compile.Lower
import LscV2.Compile.Bytecode.Codegen
import LscV2.Compile.Bytecode.Encode
import LscV2.Compile.Bytecode.Contract
import LscV2.Compile.IR.Opt.Pipeline
import LscV2.Lang.AST

namespace LscV2.Compile

def stmtToBytecode (cfg : Config) (s : Stmt) : Except String ByteArray :=
  match Lower.stmt cfg s with
  | .ok ir =>
    match Bytecode.Codegen.stmtFresh (IR.Opt.optimizeStmt ir) with
    | .ok instrs => Bytecode.encode instrs
    | .error e => .error e
  | .error e => .error e

def stmtToBytecodeHex (cfg : Config) (s : Stmt) : Except String String :=
  stmtToBytecode cfg s |>.map Bytecode.toHex

end LscV2.Compile
