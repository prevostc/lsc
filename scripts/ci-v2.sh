#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
echo "==> v2 library"
(cd "$ROOT/v2" && lake build LscV2.Compile.YulTest)
echo "==> counter example"
(cd "$ROOT/v2/examples/counter" && lake build)
echo "All v2 build gates passed."
