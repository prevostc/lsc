#!/usr/bin/env bash
# Every theorem in a *Theorems.lean file must carry a natural-language docstring
# (see AGENTS.md, "Theorem organization"). Exits 1 and lists `file:line:`
# offenders otherwise.
#
# A theorem is documented when a `/-- … -/` docstring is the closest
# non-blank, non-attribute construct above it. Inline or preceding attributes
# (`@[simp]`) and `private`/`protected`/`nonrec`/`noncomputable` are allowed
# between the docstring and `theorem`. Module docs (`/-! … -/`), other block
# comments, and `--` line comments do not count and break the association.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"

# POSIX awk: track an open `/--` docstring separately from `/-!` / `/-`.
# `prev_doc` stays set across blanks and attribute-only lines only.
AWK_PROG='
BEGIN { bad = 0; prev_doc = 0; in_doc = 0; in_blk = 0 }
{
  line = $0
  if (in_doc) {
    if (index(line, "-/") != 0) { in_doc = 0; prev_doc = 1 }
    next
  }
  if (in_blk) {
    if (index(line, "-/") != 0) in_blk = 0
    next
  }
  if (match(line, /^[[:space:]]*\/--/)) {
    if (index(line, "-/") != 0) prev_doc = 1
    else in_doc = 1
    next
  }
  if (match(line, /^[[:space:]]*\/-/)) {
    prev_doc = 0
    if (index(line, "-/") == 0) in_blk = 1
    next
  }
  if (match(line, /^[[:space:]]*$/)) next
  if (match(line, /^[[:space:]]*--/)) { prev_doc = 0; next }
  rest = line
  sub(/^[[:space:]]+/, "", rest)
  while (substr(rest, 1, 2) == "@[") {
    p = index(rest, "]")
    if (p == 0) break
    rest = substr(rest, p + 1)
    sub(/^[[:space:]]+/, "", rest)
  }
  if (rest == "") next
  while (match(rest, /^(private|protected|nonrec|noncomputable)[[:space:]]+/)) {
    rest = substr(rest, RLENGTH + 1)
    sub(/^[[:space:]]+/, "", rest)
  }
  if (match(rest, /^theorem([[:space:]]|$)/)) {
    if (!prev_doc) {
      printf "%s:%d: undocumented theorem: %s\n", file, NR, $0
      bad = 1
    }
    prev_doc = 0
    next
  }
  prev_doc = 0
}
END { if (bad) exit 1 }
'

check_root() {
  local root="$1"
  (
    cd "$root" || exit 1
    set --
    for d in Lsc Stdlib Examples; do
      [ -d "$d" ] && set -- "$@" "$d"
    done
    [ $# -eq 0 ] && exit 0
    if command -v rg >/dev/null 2>&1; then
      files=$(rg --files -g '*Theorems.lean' "$@" || true)
    else
      files=$(find "$@" -name '*Theorems.lean' -print)
    fi
    status=0
    while IFS= read -r file; do
      [ -n "$file" ] || continue
      awk -v file="$file" "$AWK_PROG" "$file" || status=1
    done <<EOF
$files
EOF
    exit "$status"
  )
}

self_test() {
  local out rc n
  tmp="$(mktemp -d "${TMPDIR:-/tmp}/check-theorem-docs.XXXXXX")"
  trap 'rm -rf "$tmp"' EXIT
  mkdir -p "$tmp/bad/Lsc" "$tmp/good/Lsc" "$tmp/mod/Lsc" "$tmp/cmt/Lsc"

  cat > "$tmp/bad/Lsc/XTheorems.lean" << 'EOF'
/-- doc -/
@[simp] theorem a : True := trivial

theorem b : True := trivial
/-- doc
more -/
theorem c : True := trivial
EOF

  cat > "$tmp/good/Lsc/GoodTheorems.lean" << 'EOF'
/-!
Module docstring must not count as a theorem docstring.
-/
namespace Foo
/-- If `Inv` holds initially and is preserved, `claim a` does not fall. -/
  theorem indented : True := trivial

/-- one-line docstring. -/
@[simp]
theorem attr_line : True := trivial

/-- inline attribute. -/
@[simp] theorem inline_attr : True := trivial

/-- private modifier. -/
private theorem priv : True := trivial

/-- protected modifier. -/
protected theorem prot : True := trivial

/-- nonrec modifier. -/
nonrec theorem nr : True := trivial

/-- noncomputable modifier. -/
noncomputable theorem nc : True := trivial

section Bar
/-- section-indented. -/
  theorem in_section : True := trivial
end Bar

/--
multi
line
-/
theorem multi : True := trivial
end Foo
EOF

  cat > "$tmp/mod/Lsc/MTheorems.lean" << 'EOF'
/-! module only -/
theorem from_module : True := trivial
EOF

  cat > "$tmp/cmt/Lsc/CTheorems.lean" << 'EOF'
/-- doc -/
-- interrupting comment
theorem interrupted : True := trivial
EOF

  set +e
  out="$(check_root "$tmp/bad")"
  rc=$?
  set -e
  n="$(printf '%s\n' "$out" | grep -c 'undocumented theorem:' || true)"
  if [ "$rc" -ne 1 ] || [ "$n" -ne 1 ] || ! printf '%s\n' "$out" | grep -q 'XTheorems.lean:4:.*theorem b'; then
    echo "self-test FAIL (negative): expected exit 1 and exactly theorem b" >&2
    echo "exit=$rc count=$n" >&2
    printf '%s\n' "$out" >&2
    exit 1
  fi
  echo "self-test: negative fixture (exit 1, theorem b) ok"
  printf '%s\n' "$out"

  set +e
  out="$(check_root "$tmp/good")"
  rc=$?
  set -e
  if [ "$rc" -ne 0 ]; then
    echo "self-test FAIL (positive): expected pass" >&2
    printf '%s\n' "$out" >&2
    exit 1
  fi
  echo "self-test: positive fixture ok"

  set +e
  out="$(check_root "$tmp/mod")"
  rc=$?
  set -e
  if [ "$rc" -ne 1 ] || ! printf '%s\n' "$out" | grep -q 'theorem from_module'; then
    echo "self-test FAIL (module docstring must not count)" >&2
    echo "exit=$rc" >&2
    printf '%s\n' "$out" >&2
    exit 1
  fi
  echo "self-test: module docstring does not count ok"

  set +e
  out="$(check_root "$tmp/cmt")"
  rc=$?
  set -e
  if [ "$rc" -ne 1 ] || ! printf '%s\n' "$out" | grep -q 'theorem interrupted'; then
    echo "self-test FAIL (line comment must break association)" >&2
    echo "exit=$rc" >&2
    printf '%s\n' "$out" >&2
    exit 1
  fi
  echo "self-test: line comment breaks association ok"
  echo "self-test: passed"
}

case "${1:-}" in
  --self-test)
    self_test
    ;;
  "")
    if ! check_root "$ROOT"; then
      echo "error: undocumented theorems in *Theorems.lean files (AGENTS.md: Theorem organization)" >&2
      exit 1
    fi
    ;;
  *)
    echo "usage: $0 [--self-test]" >&2
    exit 2
    ;;
esac
