import LscV2.Lang.Syntax
import LscV2.TestFixtures.SyntaxSmoke

open LscV2 LscV2.DSL LscV2.TestFixtures

namespace LscV2.SyntaxTest

def smokeFields : FieldMap := #[("number", .wei), ("paused", .bool), ("owner", .address)]

macro "lsc!" s:lsc_stmt : term => expandLscStmtWith smokeFields s

example : lsc! let n ← $.number +? 1; = incrementLet := rfl
example : lsc! $.number := n; = incrementSet := rfl
example : lsc! emit Incremented(n); = incrementEmit := rfl
example : lsc! require (!$.paused) else revert Paused; = incrementRequire := rfl
example :
    lsc! require (!$.paused) else revert Paused; let n ← $.number +? 1; $.number := n; emit Incremented(n);
    = incrementAst := rfl
example :
    lsc! require (msg.sender == $.owner) else revert NotOwner;
    = pauseRequireOwner := rfl
example : lsc! emit Paused(); = pauseEmit := rfl

end LscV2.SyntaxTest
