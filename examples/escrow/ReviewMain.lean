import Escrow
import Lsc.Tools.BytecodeReview

open Lsc.Tools.BytecodeReview

def main (args : List String) : IO Unit := do
  let outDir := args.getD 0 "output/local"
  runReview outDir {
    contractName := "Escrow"
    contractDef := Escrow.contractDef
    config := Escrow.config
    bytecodeHex := Escrow.bytecodeHex
  }
