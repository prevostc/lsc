#!/usr/bin/env python3
"""Compare Lean Tx.run expectations against anvil/revm on compiled EVM bytecode.

Reads export JSON produced by `scripts/export_bytecode.lean` (optionally wrapped in
BEGIN_LSC_EXPORT / END_LSC_EXPORT markers from `#eval`).
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import signal
import socket
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

ANVIL_DEFAULT_KEY = "0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80"
ANVIL_DEFAULT_ADDR = "0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266"
GAS_LIMIT = "5000000"
HARD_FORKS = ("osaka", "prague", "latest")
FOUNDRY_HINT = """Foundry (anvil/cast) not found.

Install into ~/.foundry (does not need a system package):
  curl -L https://foundry.paradigm.xyz | bash
  foundryup

Then re-run scripts/difftest.sh
"""


class HarnessError(Exception):
    pass


def die(msg: str, code: int) -> None:
    print(msg, file=sys.stderr)
    raise SystemExit(code)


def which(name: str) -> str | None:
    return shutil.which(name)


def prepend_foundry_bin() -> None:
    home_bin = Path.home() / ".foundry" / "bin"
    if home_bin.is_dir():
        os.environ["PATH"] = str(home_bin) + os.pathsep + os.environ.get("PATH", "")


def ensure_foundry() -> tuple[str, str]:
    prepend_foundry_bin()
    anvil, cast = which("anvil"), which("cast")
    if anvil and cast:
        return anvil, cast
    foundryup = which("foundryup")
    if foundryup:
        print("anvil/cast missing; running foundryup (already on PATH)…", file=sys.stderr)
        r = subprocess.run([foundryup], check=False)
        prepend_foundry_bin()
        anvil, cast = which("anvil"), which("cast")
        if anvil and cast:
            return anvil, cast
        die("foundryup ran but anvil/cast are still missing.\n" + FOUNDRY_HINT, 2)
    die(FOUNDRY_HINT, 2)


def tool_version(bin_path: str) -> str:
    r = subprocess.run([bin_path, "--version"], capture_output=True, text=True)
    line = (r.stdout or r.stderr).strip().splitlines()
    return line[0] if line else bin_path


def extract_json(text: str) -> dict[str, Any]:
    start_m = "BEGIN_LSC_EXPORT"
    end_m = "END_LSC_EXPORT"
    if start_m in text and end_m in text:
        text = text.split(start_m, 1)[1].split(end_m, 1)[0]
    start = text.find("{")
    end = text.rfind("}")
    if start < 0 or end < start:
        die("Lean export produced no JSON object", 3)
    try:
        return json.loads(text[start : end + 1])
    except json.JSONDecodeError as e:
        die(f"failed to parse Lean export JSON: {e}", 3)


def norm_hex(s: str | None) -> str:
    if s is None:
        return "0x"
    s = s.strip().lower()
    if s.startswith("0x"):
        s = s[2:]
    s = re.sub(r"[^0-9a-f]", "", s)
    if len(s) % 2 == 1:
        s = "0" + s
    return "0x" + s


def hex_eq(a: str | None, b: str | None) -> bool:
    return norm_hex(a) == norm_hex(b)


def hex_len(s: str | None) -> int:
    return (len(norm_hex(s)) - 2) // 2 if s else 0


def hex_suffix_diff(expected: str, actual: str) -> str:
    e, a = norm_hex(expected)[2:], norm_hex(actual)[2:]
    n = min(len(e), len(a))
    i = 0
    while i < n and e[i] == a[i]:
        i += 1
    return (
        f"    common_prefix {i // 2} bytes\n"
        f"    expected extra {e[i:] or '(none)'}\n"
        f"    actual extra   {a[i:] or '(none)'}"
    )


def pad32(s: str) -> str:
    h = norm_hex(s)[2:]
    return "0x" + h.zfill(64)


def free_port() -> int:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.bind(("127.0.0.1", 0))
        return int(s.getsockname()[1])


@dataclass
class Row:
    contract: str
    case: str
    status: str = ""
    ret: str = ""
    storage: str = ""
    result: str = "PASS"
    details: list[str] = field(default_factory=list)

    def fail(self, msg: str) -> None:
        self.result = "FAIL"
        self.details.append(msg)


class Anvil:
    def __init__(self, anvil: str, cast: str, hardfork: str, port: int) -> None:
        self.anvil = anvil
        self.cast = cast
        self.hardfork = hardfork
        self.port = port
        self.proc: subprocess.Popen[str] | None = None
        self.log = tempfile.NamedTemporaryFile("w+", prefix="lsc-anvil-", suffix=".log", delete=False)
        self.env = os.environ.copy()
        self.env["ETH_RPC_URL"] = f"http://127.0.0.1:{port}"

    def start(self) -> None:
        cmd = [
            self.anvil,
            "--hardfork",
            self.hardfork,
            "--host",
            "127.0.0.1",
            "--port",
            str(self.port),
            "--auto-impersonate",
            "--silent",
        ]
        self.proc = subprocess.Popen(
            cmd,
            stdout=self.log,
            stderr=subprocess.STDOUT,
            text=True,
        )
        deadline = time.time() + 15
        last_err = ""
        while time.time() < deadline:
            if self.proc.poll() is not None:
                self.log.flush()
                die(
                    f"anvil exited while starting (hardfork={self.hardfork}):\n"
                    + Path(self.log.name).read_text()[-2000:],
                    3,
                )
            r = subprocess.run(
                [self.cast, "block-number"],
                capture_output=True,
                text=True,
                env=self.env,
            )
            if r.returncode == 0:
                return
            last_err = (r.stderr or r.stdout or "").strip()
            time.sleep(0.1)
        die(f"anvil did not become ready: {last_err}", 3)

    def stop(self) -> None:
        if self.proc is None:
            return
        if self.proc.poll() is None:
            self.proc.send_signal(signal.SIGTERM)
            try:
                self.proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                self.proc.kill()
        self.log.close()

    def run_cast(self, args: list[str], check: bool = False) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [self.cast, *args],
            capture_output=True,
            text=True,
            env=self.env,
        )

    def rpc(self, method: str, *params: str) -> subprocess.CompletedProcess[str]:
        return self.run_cast(["rpc", method, *params])

    def impersonate(self, addr: str) -> None:
        self.rpc("anvil_impersonateAccount", addr)
        self.rpc("anvil_setBalance", addr, "0x56BC75E2D63100000")

    def set_code(self, addr: str, code: str) -> None:
        r = self.rpc("anvil_setCode", addr, code)
        if r.returncode != 0:
            die(f"anvil_setCode failed: {r.stderr or r.stdout}", 3)

    def set_storage(self, addr: str, slot: str, value: str) -> None:
        r = self.rpc("anvil_setStorageAt", addr, pad32(slot), pad32(value))
        if r.returncode != 0:
            die(f"anvil_setStorageAt failed: {r.stderr or r.stdout}", 3)

    def snapshot(self) -> str:
        r = self.rpc("evm_snapshot")
        if r.returncode != 0:
            die(f"evm_snapshot failed: {r.stderr or r.stdout}", 3)
        return (r.stdout or "").strip().strip('"')

    def revert(self, snap: str) -> None:
        r = self.rpc("evm_revert", snap)
        if r.returncode != 0:
            die(f"evm_revert failed: {r.stderr or r.stdout}", 3)

    def storage_at(self, addr: str, slot: str) -> str:
        r = self.run_cast(["storage", addr, pad32(slot)])
        if r.returncode != 0:
            return ""
        return norm_hex((r.stdout or "").strip())

    def code(self, addr: str) -> str:
        r = self.run_cast(["code", addr])
        return norm_hex((r.stdout or "").strip()) if r.returncode == 0 else "0x"


REVERT_DATA_RE = re.compile(
    r"""(?:data["']?\s*:\s*["']?(0x[0-9a-fA-F]*)["']?)""",
    re.IGNORECASE,
)


def parse_call_result(r: subprocess.CompletedProcess[str]) -> tuple[bool, str]:
    out = ((r.stdout or "") + "\n" + (r.stderr or "")).strip()
    if r.returncode == 0:
        lines = [ln.strip() for ln in (r.stdout or "").splitlines() if ln.strip()]
        data = lines[-1] if lines else "0x"
        if data.startswith("{") or data.startswith("Error"):
            m = REVERT_DATA_RE.search(out)
            return False, norm_hex(m.group(1) if m else "0x")
        return True, norm_hex(data)
    m = REVERT_DATA_RE.search(out)
    if m:
        return False, norm_hex(m.group(1))
    if re.search(r"revert", out, re.IGNORECASE):
        return False, "0x"
    raise HarnessError(f"cast call failed unexpectedly:\n{out}")


def parse_send_ok(r: subprocess.CompletedProcess[str]) -> tuple[bool, str]:
    out = ((r.stdout or "") + "\n" + (r.stderr or "")).strip()
    if r.returncode == 0:
        try:
            js = json.loads(r.stdout or "{}")
            status = str(js.get("status", "0x1")).lower()
            ok = status in ("0x1", "1", "true")
            return ok, json.dumps(js)
        except json.JSONDecodeError:
            if re.search(r"revert", out, re.IGNORECASE):
                return False, out
            return True, out
    if re.search(r"revert|failed", out, re.IGNORECASE):
        return False, out
    raise HarnessError(f"cast send failed unexpectedly:\n{out}")


def start_anvil(anvil: str, cast: str) -> Anvil:
    last_err: str | None = None
    for fork in HARD_FORKS:
        node = Anvil(anvil, cast, fork, free_port())
        try:
            node.start()
            return node
        except SystemExit as e:
            last_err = str(e)
            node.stop()
            if fork == HARD_FORKS[-1]:
                raise
            continue
    die(last_err or "failed to start anvil", 3)


def apply_pre(node: Anvil, addr: str, slots: list[dict[str, str]]) -> None:
    for p in slots:
        node.set_storage(addr, p["slot"], p["value"])


def check_storage(node: Anvil, addr: str, slots: list[dict[str, str]], row: Row) -> None:
    mismatches: list[str] = []
    for p in slots:
        actual = node.storage_at(addr, p["slot"])
        expected = pad32(p["value"])
        if pad32(actual) != expected:
            mismatches.append(
                f"    slot {pad32(p['slot'])}\n"
                f"      expected {expected}\n"
                f"      actual   {pad32(actual)}"
            )
    if mismatches:
        row.storage = "DIFF"
        row.fail("storage mismatch:\n" + "\n".join(mismatches))
    else:
        row.storage = "match"


def run_call_case(node: Anvil, addr: str, case: dict[str, Any], row: Row) -> None:
    sender = case["sender"]
    calldata = case["calldata"]
    node.impersonate(sender)
    apply_pre(node, addr, case.get("pre_storage") or [])

    call = node.run_cast(
        [
            "call",
            "--from",
            sender,
            "--gas-limit",
            GAS_LIMIT,
            "--data",
            calldata,
            addr,
        ]
    )
    call_ok, ret = parse_call_result(call)
    expected_ok = case["status"] == "ok"
    expected_ret = norm_hex(case.get("return_data") or "0x")
    actual_status = "ok" if call_ok else "revert"
    row.status = f"{case['status']}/{actual_status}"

    if call_ok != expected_ok:
        row.ret = "DIFF"
        row.fail(
            f"status: expected {case['status']} actual {actual_status}; return {ret}"
        )
    elif not hex_eq(ret, expected_ret):
        row.ret = "DIFF"
        row.fail(f"return: expected {expected_ret} actual {ret}")
    else:
        row.ret = "match"

    send = node.run_cast(
        [
            "send",
            "--from",
            sender,
            "--unlocked",
            "--gas-limit",
            GAS_LIMIT,
            "--json",
            addr,
            calldata,
        ]
    )
    send_ok, send_out = parse_send_ok(send)
    if send_ok != expected_ok:
        row.fail(
            f"send status: expected {'ok' if expected_ok else 'revert'} "
            f"actual {'ok' if send_ok else 'revert'}\n{send_out[-500:]}"
        )

    check_storage(node, addr, case.get("post_storage") or [], row)


def run_deploy_create(node: Anvil, contract: dict[str, Any], rows: list[Row]) -> None:
    row = Row(contract=contract["name"], case="deploy_create")
    deploy = contract.get("deploy")
    runtime = contract.get("runtime")
    if not deploy or not runtime:
        row.status = "-/-"
        row.fail("missing deploy or runtime bytecode")
        rows.append(row)
        return
    node.impersonate(ANVIL_DEFAULT_ADDR)
    send = node.run_cast(
        [
            "send",
            "--private-key",
            ANVIL_DEFAULT_KEY,
            "--gas-limit",
            GAS_LIMIT,
            "--json",
            "--create",
            deploy,
        ]
    )
    ok, out = parse_send_ok(send)
    if not ok:
        row.status = "ok/revert"
        row.fail(f"CREATE reverted:\n{out[-800:]}")
        rows.append(row)
        return
    created = ""
    try:
        js = json.loads(send.stdout or "{}")
        created = js.get("contractAddress") or js.get("contract_address") or ""
    except json.JSONDecodeError:
        created = ""
    if not created:
        m = re.search(r"contractAddress[\"': ]+(0x[0-9a-fA-F]{40})", out)
        created = m.group(1) if m else ""
    if not created:
        row.fail("CREATE receipt had no contractAddress")
        rows.append(row)
        return
    actual = node.code(created)
    exp, got = norm_hex(runtime), norm_hex(actual)
    extra = got[len(exp) :]
    if got == exp:
        row.status = "ok/ok"
        row.ret = "runtime"
        row.storage = "n/a"
        row.result = "PASS"
    elif got.startswith(exp) and extra and set(extra) <= {"0"}:
        # compileObject appends an unreachable STOP to the runtime object; `compile` does not.
        row.status = "ok/ok"
        row.ret = "runtime+STOP"
        row.storage = "n/a"
        row.result = "PASS"
        print(
            f"note: {contract['name']} CREATE runtime is compileRuntime + "
            f"{len(extra) // 2} trailing STOP byte(s) (powdr compileObject)"
        )
    else:
        row.status = "ok/ok"
        row.ret = "DIFF"
        row.fail(
            f"deployed runtime != exported runtime\n"
            f"    address  {created}\n"
            f"    expected {runtime[:74]}… ({hex_len(runtime)} bytes)\n"
            f"    actual   {actual[:74]}… ({hex_len(actual)} bytes)\n"
            + hex_suffix_diff(runtime, actual)
        )
    rows.append(row)


def print_table(rows: list[Row], evm_line: str) -> int:
    print(evm_line)
    print()
    cols = ("Contract", "Case", "Status", "Return", "Storage", "Result")
    data = [
        (r.contract, r.case, r.status, r.ret, r.storage, r.result) for r in rows
    ]
    widths = [len(c) for c in cols]
    for row in data:
        for i, cell in enumerate(row):
            widths[i] = max(widths[i], len(cell))
    fmt = "  ".join(f"{{:<{w}}}" for w in widths)
    print(fmt.format(*cols))
    print("  ".join("-" * w for w in widths))
    for row in data:
        print(fmt.format(*row))
    fails = [r for r in rows if r.result != "PASS"]
    print()
    if fails:
        print(f"{len(fails)} failed / {len(rows)} cases")
        for r in fails:
            print(f"\n[FAIL] {r.contract}/{r.case}")
            for d in r.details:
                print(d)
        return 1
    print(f"all {len(rows)} cases passed")
    return 0


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument(
        "export",
        nargs="?",
        help="path to Lean export output (JSON or marked text); stdin if omitted",
    )
    p.add_argument(
        "--check-tools",
        action="store_true",
        help="verify anvil/cast are available and exit",
    )
    args = p.parse_args(argv)
    if args.check_tools:
        anvil, cast = ensure_foundry()
        print(f"foundry ok: {tool_version(anvil)}")
        print(f"  anvil={anvil}")
        print(f"  cast={cast}")
        return 0
    raw = Path(args.export).read_text() if args.export else sys.stdin.read()
    data = extract_json(raw)
    for contract in data.get("contracts") or []:
        name = contract.get("name") or "?"
        rt = contract.get("runtime")
        dp = contract.get("deploy")
        nrt = (len(norm_hex(rt)) - 2) // 2 if rt else 0
        ndp = (len(norm_hex(dp)) - 2) // 2 if dp else 0
        ncases = len(contract.get("cases") or [])
        print(f"export {name}: runtime {nrt} bytes, deploy {ndp} bytes, {ncases} Tx.run cases")

    anvil, cast = ensure_foundry()
    node = start_anvil(anvil, cast)
    evm_line = (
        f"EVM: {tool_version(anvil)} (revm via Foundry)  "
        f"hardfork={node.hardfork}  rpc={node.env['ETH_RPC_URL']}"
    )
    rows: list[Row] = []
    try:
        addr = data.get("runtime_address") or "0x000000000000000000000000000000000000c0de"
        # 0x01–0x11 (and 0x100 on some forks) are precompiles; YulTests uses self=7.
        if int(addr, 16) < 0x10000:
            addr = "0x000000000000000000000000000000000000c0de"
        print(f"runtime address {addr}")
        for contract in data.get("contracts") or []:
            name = contract.get("name") or "?"
            runtime = contract.get("runtime")
            if not runtime:
                row = Row(contract=name, case="(compileRuntime)")
                row.fail("compileRuntime returned none")
                rows.append(row)
                continue
            if name == "Counter":
                try:
                    run_deploy_create(node, contract, rows)
                except HarnessError as e:
                    row = Row(contract=name, case="deploy_create")
                    row.fail(str(e))
                    rows.append(row)
            snap = None
            node.set_code(addr, runtime)
            snap = node.snapshot()
            for case in contract.get("cases") or []:
                row = Row(contract=name, case=case.get("name") or "?")
                try:
                    run_call_case(node, addr, case, row)
                except HarnessError as e:
                    row.fail(str(e))
                finally:
                    if snap:
                        node.revert(snap)
                        snap = node.snapshot()
                rows.append(row)
    finally:
        node.stop()
    return print_table(rows, evm_line)


if __name__ == "__main__":
    raise SystemExit(main())
