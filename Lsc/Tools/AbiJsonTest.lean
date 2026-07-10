import Lsc.Tools.AbiJson
import Lsc.Selectors
import Lsc.Compile.BytecodeTest

open Lsc Lsc.Tools Lsc.BytecodeTest

namespace Lsc.AbiJsonTest

example : contractAbiJson counterDef |>.contains "\"type\":\"error\"" := by native_decide

example : contractAbiJson counterDef |>.contains "\"name\":\"Paused\"" := by native_decide

example : contractAbiJson counterDef |>.contains "\"name\":\"Overflow\"" := by native_decide

example :
    computeErrorSelector "NotOwner" [] = computeSelectorFromParams "NotOwner" [] := by native_decide

end Lsc.AbiJsonTest
