import Lsc.Lang.Syntax.Grammar
import Lsc.Lang.Syntax.Params
import Lsc.Lang.Syntax.ElabExpr
import Lsc.Lang.Syntax.ElabStmt
import Lsc.Lang.Syntax.CrossCall
import Lsc.Lang.Syntax.Commands

/-!
# Contract DSL surface (`tx` / `view` / `constructor` / `derive_contract`)

Re-exports the split implementation under `Lsc/Lang/Syntax/`:

| Module | Responsibility |
|--------|----------------|
| `Grammar` | `lscExpr` / `lscStmt` syntax categories |
| `Params` | `tx` / `view` / `constructor` parameter resolution |
| `ElabExpr` | `lscExpr` → `Expr` elaboration |
| `ElabStmt` | `lscStmt` → `Stmt` elaboration (incl. `exec`/`read` Stmt nodes) |
| `CrossCall` | `PairM` proof-layer sequencing for cross-module `exec`/`read` |
| `Commands` | `tx` / `view` / `constructor` / `derive_contract` commands |
-/
