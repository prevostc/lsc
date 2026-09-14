#!/usr/bin/env bash
# Examples layout lint (see Examples/AGENTS.md).
#
# Fails if:
# - any Examples/*/Contract.lean contains a forbidden token
# - any Examples/*/Theorems.lean has a multi-line `by` proof body
# - Examples/Misc exists
#
# Usage: scripts/check-examples.sh
#        scripts/check-examples.sh --self-test
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"

# Identifiers / commands that must not appear in a user-facing Contract.lean.
# Grep-level: comments and docstrings count.
CONTRACT_PATTERNS=(
  '(^|[[:space:]])theorem([[:space:]]|$)'
  '(^|[[:space:]])lemma([[:space:]]|$)'
  '(^|[[:space:]])example([[:space:]]|$)'
  '(^|[[:space:]])instance([[:space:]]|$)'
  '@\[simp\]'
  '#guard_msgs'
  '#guard'
  '#eval'
  '#check'
  'core_denote'
  '\.core([^A-Za-z0-9_]|$)'
  'Core\.'
  'Spec\.exec'
  'Amount\.ofWord'
  '\.raw([^A-Za-z0-9_]|$)'
  '[A-Za-z0-9]Raw([^A-Za-z0-9]|$)'
  '[A-Za-z0-9]Unit([^A-Za-z0-9]|$)'
  '[A-Za-z0-9]Impl([^A-Za-z0-9]|$)'
  '[a-z]U([^A-Za-z0-9]|$)'
  'mulDivDown'
  'mulDivUp'
)

scan_contract() {
  local file="$1"
  local pat hits
  for pat in "${CONTRACT_PATTERNS[@]}"; do
    if command -v rg >/dev/null 2>&1; then
      hits="$(rg -n --pcre2 "$pat" "$file" || true)"
    else
      hits="$(grep -nE "$pat" "$file" || true)"
    fi
    if [ -n "$hits" ]; then
      printf '%s: forbidden token /%s/\n%s\n' "$file" "$pat" "$hits"
      return 1
    fi
  done
  return 0
}

# A `by` block is longer than one line when `:= by` is the last non-space
# token on its line (the tactics continue below).
scan_theorems() {
  local file="$1"
  if command -v rg >/dev/null 2>&1; then
    hits="$(rg -n ':=[[:space:]]*by[[:space:]]*$' "$file" || true)"
  else
    hits="$(grep -nE ':=[[:space:]]*by[[:space:]]*$' "$file" || true)"
  fi
  if [ -n "$hits" ]; then
    printf '%s: multi-line proof body (Theorems.lean must be a one-line reference):\n%s\n' \
      "$file" "$hits"
    return 1
  fi
  return 0
}

check_root() {
  local root="$1"
  local status=0
  (
    cd "$root" || exit 1
    if [ -e Examples/Misc ] || [ -e Examples/Misc.lean ]; then
      echo "error: Examples/Misc must not exist" >&2
      exit 1
    fi
    shopt -s nullglob
    for f in Examples/*/Contract.lean; do
      case "$f" in
        Examples/Cpamm/*) continue ;;
      esac
      scan_contract "$f" || status=1
    done
    for f in Examples/*/Theorems.lean; do
      case "$f" in
        Examples/Cpamm/*) continue ;;
      esac
      scan_theorems "$f" || status=1
    done
    exit "$status"
  )
}

self_test() {
  local out rc
  tmp="$(mktemp -d "${TMPDIR:-/tmp}/check-examples.XXXXXX")"
  trap 'rm -rf "$tmp"' EXIT

  mkdir -p "$tmp/good/Examples/Token/Proofs" \
           "$tmp/badc/Examples/Token" \
           "$tmp/badt/Examples/Token" \
           "$tmp/misc/Examples/Misc" \
           "$tmp/misc/Examples/Token"

  cat > "$tmp/good/Examples/Token/Contract.lean" << 'EOF'
/-- A tiny token. -/
def transfer (to : Address) (amount : Amount tokenAsset) : M Bool := do
  write balances[to] (← (← read balances[to]) +? amount)
  return true

lsc_contract Token transfer
EOF
  cat > "$tmp/good/Examples/Token/Theorems.lean" << 'EOF'
/-- A successful transfer conserves the two balances. -/
theorem transfer_conserves ... :=
  Proof.transfer_conserves ctx w dst amount h
EOF

  cat > "$tmp/badc/Examples/Token/Contract.lean" << 'EOF'
theorem hidden : True := trivial
def transferU (to : Address) : M Unit := pure ()
def depositRaw (n : Amount a) : M Nat := pure n.raw
EOF
  cat > "$tmp/badc/Examples/Token/Theorems.lean" << 'EOF'
theorem ok : True := trivial
EOF

  cat > "$tmp/badt/Examples/Token/Contract.lean" << 'EOF'
def ping : M Unit := pure ()
EOF
  cat > "$tmp/badt/Examples/Token/Theorems.lean" << 'EOF'
theorem foo : True := by
  trivial
EOF

  cat > "$tmp/misc/Examples/Misc/YulTests.lean" << 'EOF'
#guard true
EOF
  cat > "$tmp/misc/Examples/Token/Contract.lean" << 'EOF'
def ping : M Unit := pure ()
EOF
  cat > "$tmp/misc/Examples/Token/Theorems.lean" << 'EOF'
theorem foo : True := Proof.foo
EOF

  set +e
  out="$(check_root "$tmp/badc" 2>&1)"
  rc=$?
  set -e
  if [ "$rc" -ne 1 ] || ! printf '%s\n' "$out" | grep -q 'theorem'; then
    echo "self-test FAIL (contract tokens): expected exit 1 mentioning theorem" >&2
    echo "exit=$rc" >&2
    printf '%s\n' "$out" >&2
    exit 1
  fi
  echo "self-test: Contract.lean forbidden tokens ok"

  set +e
  out="$(check_root "$tmp/badt" 2>&1)"
  rc=$?
  set -e
  if [ "$rc" -ne 1 ] || ! printf '%s\n' "$out" | grep -q 'multi-line proof body'; then
    echo "self-test FAIL (theorems by-block): expected multi-line proof body" >&2
    echo "exit=$rc" >&2
    printf '%s\n' "$out" >&2
    exit 1
  fi
  echo "self-test: Theorems.lean multi-line by ok"

  set +e
  out="$(check_root "$tmp/misc" 2>&1)"
  rc=$?
  set -e
  if [ "$rc" -ne 1 ] || ! printf '%s\n' "$out" | grep -q 'Examples/Misc'; then
    echo "self-test FAIL (Misc exists): expected Examples/Misc error" >&2
    echo "exit=$rc" >&2
    printf '%s\n' "$out" >&2
    exit 1
  fi
  echo "self-test: Examples/Misc rejected ok"

  set +e
  out="$(check_root "$tmp/good" 2>&1)"
  rc=$?
  set -e
  if [ "$rc" -ne 0 ]; then
    echo "self-test FAIL (positive): expected pass" >&2
    printf '%s\n' "$out" >&2
    exit 1
  fi
  echo "self-test: positive fixture ok"
  echo "self-test: passed"
}

case "${1:-}" in
  --self-test)
    self_test
    ;;
  "")
    if ! check_root "$ROOT"; then
      echo "error: Examples layout lint failed (Examples/AGENTS.md)" >&2
      exit 1
    fi
    ;;
  *)
    echo "usage: $0 [--self-test]" >&2
    exit 2
    ;;
esac
