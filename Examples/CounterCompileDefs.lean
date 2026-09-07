import Examples.Counter
import Lsc.Lang.Contract

/-!
Counter runtime `FnDef`s used by the per-entrypoint `toYulFn` theorems.
-/

namespace Lsc.Compiler

open Lsc

def incrementFn : FnDef where
  name := "increment"
  decl := ``Counter.increment
  kind := .tx
  params := []
  ret := .unit
  core := Counter.increment.core

def incrementByFn : FnDef where
  name := "incrementBy"
  decl := ``Counter.incrementBy
  kind := .tx
  params := [{ name := "n", ty := .uint256 }]
  ret := .unit
  core := Counter.incrementBy.core

def decrementFn : FnDef where
  name := "decrement"
  decl := ``Counter.decrement
  kind := .tx
  params := []
  ret := .unit
  core := Counter.decrement.core

def getFn : FnDef where
  name := "get"
  decl := ``Counter.get
  kind := .view
  params := []
  ret := .word
  core := Counter.get.core

end Lsc.Compiler
