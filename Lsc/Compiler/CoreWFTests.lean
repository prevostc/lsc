import Lsc.Lang.Contract
import Lsc.Compiler.YulDefs

/-!
`coreWF` / `internalsWF` for internal calls: arity and topological
index (`i < bound`, callee body checked at bound `i`).
-/

namespace Lsc.Compiler.CoreWFTests

open Lsc Lsc.Compiler

def idWord : Core .word := .ret (.word (.var 0))
def call0 : Core .word := .callTail 0 [.var 0]
def call1 : Core .word := .callTail 1 [.var 0]
def badArity : Core .word := .callTail 0 []

def emptyC : ContractDef :=
  { name := "", fields := [], functions := [], ctor := none,
    events := [], errors := [] }

def cOk : ContractDef :=
  { emptyC with internals := [⟨"id", 1, .word, idWord⟩, ⟨"fwd", 1, .word, call0⟩] }

def cCycle : ContractDef :=
  { emptyC with internals := [⟨"id", 1, .word, call1⟩, ⟨"fwd", 1, .word, call0⟩] }

def cArity : ContractDef :=
  { emptyC with internals := [⟨"id", 1, .word, idWord⟩] }

#guard internalsWF cOk
#guard coreWF cOk (.callTail (t := .word) 1 [.lit 1])
#guard !internalsWF cCycle
#guard !coreWF cArity badArity
#guard !coreWF cOk (.callTail (t := .word) 2 [.lit 1])

end Lsc.Compiler.CoreWFTests
