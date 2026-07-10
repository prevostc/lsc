import Interest
import Lsc.Tools.BytecodeReview

open Lsc.Tools.BytecodeReview

def main (args : List String) : IO Unit := do
  let outDir := args.getD 0 "output/local"
  runReview outDir {
    contractName := "Interest"
    contractDef := Interest.contractDef
    config := Interest.config
    bytecodeHex := Interest.bytecodeHex
  }
