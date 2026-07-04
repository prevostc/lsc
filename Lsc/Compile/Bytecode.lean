import Lsc.Compile.Lower
import Lsc.Compile.Bytecode.Codegen
import Lsc.Compile.Bytecode.Encode
import Lsc.Compile.Bytecode.Contract
import Lsc.Compile.IR.Opt.Pipeline
import Lsc.Lang.AST

namespace Lsc.Compile

def stmtToBytecode (cfg : Config) (s : Stmt) : Except String ByteArray :=
  match Lower.stmt cfg s with
  | .ok ir =>
    match Bytecode.Codegen.stmtFresh (IR.Opt.optimizeStmt ir) with
    | .ok instrs => Bytecode.encode instrs
    | .error e => .error e
  | .error e => .error e

def stmtToBytecodeHex (cfg : Config) (s : Stmt) : Except String String :=
  stmtToBytecode cfg s |>.map Bytecode.toHex

end Lsc.Compile
