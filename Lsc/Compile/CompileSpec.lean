import Lsc.Compile.ExternalCallSpec
import Lsc.Compile.Bytecode.CodegenInvariant

/-!
Shared compile-test spec facade.

Import `Lsc.Compile.CompileSpec` to pull in both `ExternalCallSpec` and `Bytecode.CodegenInvariant`.
Tests should state plain-English properties in `/-- **Property:** ... -/` comments first,
then encode them with `externalCallSites`, `YulSpec.*`, or `Bytecode.*` helpers — never raw
opcode hex substrings. -/
