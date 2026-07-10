import Counter
import Lsc.Tools.BytecodeReview

open Lsc.Tools.BytecodeReview

def main (args : List String) : IO Unit := do
  let outDir := args.getD 0 "output/local"
  runReview outDir {
    contractName := "Counter"
    contractDef := Counter.contractDef
    config := Counter.config
    bytecodeHex := Counter.bytecodeHex
  }
