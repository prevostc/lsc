import Lake
open Lake DSL

package lsc where
  version := v!"0.1.0"

lean_lib Lsc where
  globs := #[Glob.submodules `Lsc]
