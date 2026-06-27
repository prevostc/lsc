import LscV2.Syntax
import LscV2.TestFixtures.Counter

open LscV2 LscV2.TestFixtures

namespace LscV2.SyntaxTest

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
