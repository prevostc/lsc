#!/usr/bin/env bash
# Sourced by export_bytecode.sh and review-bytecode.sh.
# Decompile Examples/<C>/compiled/runtime.hex with heimdall. Non-fatal if missing
# or failing. `--include-sol` and `--include-yul` are mutually exclusive, so two
# runs. Writes compiled/decompiled.sol and, when produced, compiled/decompiled.yul.
# If --abi is rejected (e.g. Lean names like `paused?`), retries without it.

lsc_compiled_dir() {
  echo "Examples/${1}/compiled"
}

lsc_heimdall_decompile() {
  local name="$1"
  local dir
  dir="$(lsc_compiled_dir "$name")"
  local hex="${dir}/runtime.hex"
  local abi="${dir}/abi.json"
  local prefix="${HEIMDALL_NOTICE_PREFIX:-}"
  local heimdall="${HEIMDALL:-${HOME}/.bifrost/bin/heimdall}"
  if [[ ! -x "$heimdall" ]]; then
    heimdall="$(command -v heimdall 2>/dev/null || true)"
  fi
  if [[ -z "$heimdall" || ! -x "$heimdall" ]]; then
    echo "${prefix}notice: heimdall not found (expected ~/.bifrost/bin/heimdall); skip decompile"
    return 0
  fi
  if [[ ! -f "$hex" ]]; then
    echo "${prefix}notice: $hex missing; skip heimdall for $name"
    return 0
  fi
  local work
  work="$(mktemp -d "${TMPDIR:-/tmp}/lsc-heimdall-${name}.XXXXXX")"
  mkdir -p "$work/sol" "$work/yul"

  lsc_heimdall_one() {
    local flag="$1" outdir="$2" dest="$3" label="$4"
    local log="$outdir/decompile.log"
    local ok=0
    if [[ -f "$abi" ]] && "$heimdall" decompile "$hex" "$flag" --abi "$abi" \
        --output "$outdir" --name "$name" --default >"$log" 2>&1; then
      ok=1
    else
      local abi_failed=0
      if [[ -f "$abi" ]] && grep -q 'ABI' "$log" 2>/dev/null; then
        abi_failed=1
      fi
      if "$heimdall" decompile "$hex" "$flag" \
          --output "$outdir" --name "$name" --default >"$log" 2>&1; then
        if [[ "$abi_failed" -eq 1 ]]; then
          echo "${prefix}notice: heimdall $flag rejected ABI for $name; wrote without --abi"
        fi
        ok=1
      fi
    fi
    if [[ "$ok" -ne 1 ]]; then
      echo "${prefix}notice: heimdall $flag failed for $name"
      tail -n 8 "$log" || true
      return 0
    fi
    local found
    found="$(find "$outdir" -name "*.${label}" -print -quit 2>/dev/null || true)"
    if [[ -n "$found" ]]; then
      # Heimdall only writes under --output; place the recovered file in compiled/.
      cat "$found" > "$dest"
      echo "${prefix}heimdall → $dest"
    elif [[ "$label" == sol ]]; then
      echo "${prefix}notice: heimdall produced no .sol for $name"
    fi
  }

  lsc_heimdall_one --include-sol "$work/sol" "${dir}/decompiled.sol" sol
  lsc_heimdall_one --include-yul "$work/yul" "${dir}/decompiled.yul" yul
  rm -rf "$work"
  return 0
}
