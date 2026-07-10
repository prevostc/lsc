import Token
import Lsc.Tools.BytecodeReview

open Lsc.Tools.BytecodeReview

def main (args : List String) : IO Unit := do
  let outDir := args.getD 0 "output/local"
  runReview outDir {
    contractName := "Token"
    contractDef := Token.contractDef
    config := Token.config
    bytecodeHex := Token.bytecodeHex
  }
