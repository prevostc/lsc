#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"

build_no_warnings() {
  local dir="$1"
  local target="$2"
  local out
  out="$(cd "$dir" && lake build "$target" 2>&1)" || {
    echo "$out"
    return 1
  }
  if echo "$out" | grep -q 'warning:'; then
    echo "$out"
    echo "error: build emitted compiler/linter warnings (expected zero)"
    return 1
  fi
  echo "$out" | tail -3
}

echo "==> v2 library tests"
build_no_warnings "$ROOT/v2" "LscV2.Compile.YulTest"
build_no_warnings "$ROOT/v2" "LscV2.Compile.BytecodeTest"
build_no_warnings "$ROOT/v2" "LscV2.Compile.Correctness"
build_no_warnings "$ROOT/v2" "LscV2.ChecksTest"
build_no_warnings "$ROOT/v2" "LscV2.SyntaxTest"

echo "==> counter example"
build_no_warnings "$ROOT/v2/examples/counter" "Counter"

echo "All v2 build gates passed (zero warnings)."
