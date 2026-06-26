import Lake
open Lake DSL

package lscV1 where
  version := v!"0.1.0"

lean_lib LscV1 where
  globs := #[Glob.submodules `LscV1]
