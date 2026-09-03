import FixedMath
import Lsc.Tools.BytecodeReview

open Lsc.Tools.BytecodeReview

def main (args : List String) : IO Unit := do
  let outDir := args.getD 0 "output/local"
  runReview outDir {
    contractName := "FixedMath"
    contractDef := FixedMath.contractDef
    config := FixedMath.config
    bytecodeHex := FixedMath.bytecodeHex
  }
