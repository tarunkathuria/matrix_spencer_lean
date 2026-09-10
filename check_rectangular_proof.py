#!/usr/bin/env python3
"""Fail-closed build, statement, and axiom checks for the rectangular theorem.

Success concerns only MatrixSpencer.matrix_spencer_rectangular. Compiling a
statement or an auxiliary lemma never produces a successful verification.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
from datetime import datetime, timezone


ROOT = Path(__file__).resolve().parent
TARGET = "MatrixSpencer.matrix_spencer_rectangular"
STATEMENT = "MatrixSpencer.rectangularStatement"
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
FORBIDDEN_TOKENS = frozenset({"sorry", "admit", "axiom", "sorryAx"})
AXIOMS_BEGIN = "MATRIX_SPENCER_AXIOMS_BEGIN_9D73B1"
AXIOMS_END = "MATRIX_SPENCER_AXIOMS_END_9D73B1"
MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z")


def source_admissions(source: str) -> list[tuple[int, str]]:
    """Lexical screen ignoring nested comments, literals, and quoted names.

    Interpolated-string expressions are scanned as code. This is a screen,
    not a substitute for elaboration or checking actual axiom dependencies.
    """
    findings: list[tuple[int, str]] = []
    length = len(source)

    def string(pos: int, interpolated: bool) -> int:
        pos += 1
        while pos < length:
            if source[pos] == "\\":
                pos += 2
            elif source[pos] == '"':
                return pos + 1
            elif interpolated and source.startswith("{{", pos):
                pos += 2
            elif interpolated and source[pos] == "{":
                pos = code(pos + 1, brace_depth=1)
            else:
                pos += 1
        return pos

    def code(pos: int, brace_depth: int = 0) -> int:
        while pos < length:
            if source.startswith("--", pos):
                end = source.find("\n", pos + 2)
                pos = length if end < 0 else end + 1
                continue
            if source.startswith("/-", pos):
                depth = 1
                pos += 2
                while pos < length and depth:
                    if source.startswith("/-", pos):
                        depth += 1
                        pos += 2
                    elif source.startswith("-/", pos):
                        depth -= 1
                        pos += 2
                    else:
                        pos += 1
                continue
            if source[pos] == "«":
                end = source.find("»", pos + 1)
                pos = length if end < 0 else end + 1
                continue
            raw = re.match(r'r(#+)?"', source[pos:]) if source[pos] == "r" else None
            if raw:
                hashes = raw.group(1) or ""
                start = pos + len(raw.group(0))
                end = source.find('"' + hashes, start)
                pos = length if end < 0 else end + 1 + len(hashes)
                continue
            if source[pos] == '"':
                interpolated = bool(re.search(r"[A-Za-z_][A-Za-z_0-9]*!$", source[:pos]))
                pos = string(pos, interpolated)
                continue
            if brace_depth and source[pos] == "{":
                brace_depth += 1
                pos += 1
                continue
            if brace_depth and source[pos] == "}":
                brace_depth -= 1
                pos += 1
                if not brace_depth:
                    return pos
                continue
            if source[pos].isalpha() or source[pos] == "_":
                start = pos
                pos += 1
                while pos < length and (source[pos].isalnum() or source[pos] in "_'!"):
                    pos += 1
                token = source[start:pos]
                if token in FORBIDDEN_TOKENS:
                    findings.append((source.count("\n", 0, start) + 1, token))
                continue
            pos += 1
        return pos

    code(0)
    return findings


def parse_axioms(output: str, begin: str = AXIOMS_BEGIN, end: str = AXIOMS_END) -> set[str]:
    lines = output.splitlines()
    starts = [index for index, line in enumerate(lines) if line == begin]
    stops = [index for index, line in enumerate(lines) if line == end]
    if len(starts) != 1 or len(stops) != 1:
        raise ValueError("missing or duplicate axiom-output markers")
    if starts[0] >= stops[0]:
        raise ValueError("axiom-output markers appear in the wrong order")
    body = "\n".join(lines[starts[0] + 1:stops[0]])
    if re.search(r"does not depend on any axioms", body):
        return set()
    match = re.search(r"depends on axioms:\s*\[([^\]]*)\]", body, re.DOTALL)
    if match is None:
        raise ValueError("Lean did not produce a recognizable axiom report")
    names = {part.strip() for part in match.group(1).split(",") if part.strip()}
    if not all(MODULE_NAME.fullmatch(name) for name in names):
        raise ValueError("unrecognized axiom name in Lean report")
    return names


def local_sources() -> list[Path]:
    excluded = {".lake", ".git", ".verification", ".tools"}
    return sorted(
        path for path in ROOT.rglob("*.lean")
        if not any(part in excluded for part in path.relative_to(ROOT).parts)
    )


def source_fingerprint() -> dict[str, str]:
    paths = set(local_sources())
    for name in ("lean-toolchain", "lakefile.toml", "lakefile.lean", "lake-manifest.json", "run_lake.sh", "check_proof.py", "check_rectangular_proof.py"):
        path = ROOT / name
        if path.is_file():
            paths.add(path)
    return {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(paths)}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", help="Path to Lake or its wrapper; defaults to run_lake.sh")
    parser.add_argument("--module", default="MatrixSpencer.Rectangular", help="Root module importing the final theorem")
    parser.add_argument("--partial", action="append", metavar="MODULE",
                        help="Build an auxiliary module only; always report INCOMPLETE (exit 2)")
    parser.add_argument("--audit-lemma", action="append", metavar="DECLARATION",
                        help="Also print and audit the transitive axioms of an auxiliary theorem")
    parser.add_argument("--kernel-replay", choices=("auto", "imports", "fresh"), default="auto",
                        help="Require replay when an adapter is present; auto otherwise uses bundled leanchecker")
    parser.add_argument("--timeout", type=int, default=1800, help="Timeout in seconds for each command")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    if any(not MODULE_NAME.fullmatch(name) for name in
           [args.module, *(args.partial or []), *(args.audit_lemma or [])]):
        parser.error("module names must be dot-separated ordinary Lean identifiers")

    audit_dir = ROOT / ".verification" / "rectangular"
    audit_dir.mkdir(exist_ok=True)
    result: dict[str, object] = {
        "target": TARGET, "statement": STATEMENT,
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "started_at": datetime.now(timezone.utc).isoformat(),
        "status": "INCOMPLETE", "commands": [],
    }

    def finish(status: str, reason: str, exit_code: int) -> int:
        result.update(status=status, reason=reason, exit_code=exit_code,
                      finished_at=datetime.now(timezone.utc).isoformat())
        (audit_dir / "last_result.json").write_text(json.dumps(result, indent=2) + "\n")
        print(f"{status}: {reason}", flush=True)
        print(f"Audit record: {audit_dir / 'last_result.json'}", flush=True)
        return exit_code

    sources = local_sources()
    initial_fingerprint = source_fingerprint()
    result["source_sha256"] = initial_fingerprint
    result["source_files_scanned"] = [str(path.relative_to(ROOT)) for path in sources]
    admissions = [
        f"{path.relative_to(ROOT)}:{line}: {token}"
        for path in sources for line, token in source_admissions(path.read_text())
    ]
    result["source_admissions"] = admissions
    if admissions:
        return finish("FAILED", "local source contains an admission token: " + "; ".join(admissions), 1)
    if not any((ROOT / name).is_file() for name in ("lakefile.toml", "lakefile.lean")):
        return finish("INCOMPLETE", "Lake project configuration is missing", 2)
    if not sources:
        return finish("INCOMPLETE", "no local Lean source modules exist", 2)

    env = os.environ.copy()
    local_elan = ROOT.parent / ".tools" / "elan"
    if local_elan.is_dir():
        env["ELAN_HOME"] = str(local_elan)
        env["PATH"] = str(local_elan / "bin") + os.pathsep + env.get("PATH", "")
    wrapper = ROOT / "run_lake.sh"
    lake = args.lake or (str(wrapper) if wrapper.is_file() else
                         shutil.which("lake", path=env.get("PATH")))
    if lake is None:
        return finish("INCOMPLETE", "Lake executable is unavailable", 2)

    def run(label: str, command: list[str]) -> tuple[int, str]:
        print(f"Checking {label}...", flush=True)
        try:
            completed = subprocess.run(command, cwd=ROOT, env=env, text=True,
                                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                       timeout=args.timeout, check=False)
            code, output = completed.returncode, completed.stdout
        except subprocess.TimeoutExpired as exc:
            captured = exc.stdout or b""
            output = captured.decode(errors="replace") if isinstance(captured, bytes) else captured
            output += f"\nCommand exceeded {args.timeout} seconds.\n"
            code = 124
        except OSError as exc:
            code, output = 127, str(exc) + "\n"
        (audit_dir / f"{label}.log").write_text(output)
        result["commands"].append({"label": label, "argv": command, "exit_code": code})
        if output:
            print(output, end="" if output.endswith("\n") else "\n", flush=True)
        return code, output

    build_targets = args.partial or [args.module]
    code, _ = run("build", [lake, "build", *build_targets])
    if code:
        return finish("INCOMPLETE", "the requested Lean build did not succeed", 2)
    if args.audit_lemma:
        audit_source = "\n".join(f"import {name}" for name in build_targets) + "\nimport Lean\n"
        for index, name in enumerate(args.audit_lemma):
            audit_source += f'''
run_cmd Lean.Elab.Command.liftTermElabM do
  let info ← Lean.getConstInfo `{name}
  match info with
  | .thmInfo _ => pure ()
  | _ => throwError "Requested auxiliary declaration must be a theorem."
#check {name}
#eval IO.println "{AXIOMS_BEGIN}_{index}"
#print axioms {name}
#eval IO.println "{AXIOMS_END}_{index}"
'''
        audit_path = audit_dir / "AuxiliaryAxioms.lean"
        audit_path.write_text(audit_source)
        code, output = run("auxiliary_axioms", [lake, "env", "lean", str(audit_path)])
        if code:
            return finish("INCOMPLETE", "a requested auxiliary theorem could not be audited", 2)
        result["auxiliary_axioms"] = {}
        for index, name in enumerate(args.audit_lemma):
            try:
                axioms = parse_axioms(output, f"{AXIOMS_BEGIN}_{index}", f"{AXIOMS_END}_{index}")
            except ValueError as exc:
                return finish("FAILED", f"{name}: {exc}", 1)
            result["auxiliary_axioms"][name] = sorted(axioms)
            if axioms - ALLOWED_AXIOMS:
                return finish("FAILED", f"{name} uses disallowed axioms: " +
                              ", ".join(sorted(axioms - ALLOWED_AXIOMS)), 1)
    if args.partial:
        result["partial_modules_built"] = args.partial
        adapter = ROOT / "tools" / "Replay.lean"
        if adapter.is_file():
            mode_flags = ["--fresh"] if args.kernel_replay == "fresh" else []
            code, output = run("kernel_replay", [lake, "env", "lean", "--run", str(adapter),
                                                 *mode_flags, *args.partial])
            if code or "PROJECT_CLOSURE_REPLAYED:" not in output or "PANIC" in output:
                return finish("FAILED", "local-adapter replay of auxiliary modules failed", 1)
            result["kernel_replay"] = "project import closures of the requested auxiliary modules"
        return finish("INCOMPLETE", "auxiliary modules compiled; the final theorem was not verified", 2)

    # Compare the declaration's actual type before term elaboration can
    # insert implicit arguments or coercions. Then check a proof term too.
    probe_source = f'''import {args.module}
import Lean

open scoped BigOperators Matrix

namespace MatrixSpencerVerification
def ExpectedRectangularStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (n d : ℕ), 1 ≤ n → n ≤ d →
      ∀ (B : Fin n → Matrix (Fin d) (Fin d) ℂ),
        (∀ i, (B i).IsHermitian) →
        (∀ i, ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (B i)‖ ≤ 1) →
        ∃ ε : Fin n → ℝ,
          (∀ i, ε i = 1 ∨ ε i = -1) ∧
          ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)
            (∑ i : Fin n, (ε i : ℂ) • B i)‖ ≤ C * Real.sqrt ((n : ℝ) * Real.log (2 * (d : ℝ) / (n : ℝ)))
end MatrixSpencerVerification

run_cmd Lean.Elab.Command.liftTermElabM do
  let info ← Lean.getConstInfo `{TARGET}
  match info with
  | .thmInfo _ => pure ()
  | _ => throwError "The final target must be a theorem declaration."
  unless (← Lean.Meta.isDefEq info.type (Lean.mkConst `{STATEMENT})) do
    throwError "The final theorem declaration has the wrong type."
  unless (← Lean.Meta.isDefEq info.type
      (Lean.mkConst `MatrixSpencerVerification.ExpectedRectangularStatement)) do
    throwError "The final theorem does not match the independently frozen mathematical statement."

#check ({TARGET} : {STATEMENT})
example : MatrixSpencerVerification.ExpectedRectangularStatement := {TARGET}
#print MatrixSpencerVerification.ExpectedRectangularStatement
#print {STATEMENT}
#print MatrixSpencer.rectangularStatementWithConstant
#eval IO.println "{AXIOMS_BEGIN}"
#print axioms {TARGET}
#eval IO.println "{AXIOMS_END}"
'''
    with tempfile.NamedTemporaryFile("w", suffix=".lean", prefix="VerifyRectangular", dir=audit_dir,
                                     delete=False) as probe:
        probe.write(probe_source)
        probe_path = Path(probe.name)
    try:
        code, output = run("final_theorem", [lake, "env", "lean", str(probe_path)])
    finally:
        probe_path.unlink(missing_ok=True)
    if code:
        return finish("INCOMPLETE", "final target is absent or does not establish the exact rectangularStatement", 2)
    try:
        axioms = parse_axioms(output)
    except ValueError as exc:
        return finish("FAILED", str(exc), 1)
    result["actual_axioms"] = sorted(axioms)
    unexpected = axioms - ALLOWED_AXIOMS
    if unexpected:
        return finish("FAILED", "final theorem depends on disallowed axioms: " + ", ".join(sorted(unexpected)), 1)

    adapter = ROOT / "tools" / "Replay.lean"
    if adapter.is_file():
        mode_flags = ["--fresh"] if args.kernel_replay == "fresh" else []
        code, output = run("kernel_replay", [lake, "env", "lean", "--run", str(adapter),
                                             *mode_flags, args.module])
        if code or "PROJECT_CLOSURE_REPLAYED:" not in output or "PANIC" in output:
            return finish("FAILED", "mandatory local-adapter kernel replay failed", 1)
        result["kernel_replay"] = "all project modules in the target import closure, against imported environments"
    else:
        prefix_code, prefix_output = run("lean_prefix", [lake, "env", "lean", "--print-prefix"])
        prefix = Path(prefix_output.strip()) if prefix_code == 0 else None
        leanchecker = prefix / "bin" / "leanchecker" if prefix else None
        if leanchecker is None or not leanchecker.is_file():
            result["kernel_replay"] = "unavailable"
            if args.kernel_replay != "auto":
                return finish("INCOMPLETE", "requested leanchecker executable is unavailable", 2)
            print("Optional leanchecker replay unavailable; normal Lean checking succeeded.", flush=True)
        else:
            mode_flags = ["--fresh"] if args.kernel_replay == "fresh" else []
            code, replay_output = run("kernel_replay", [lake, "env", str(leanchecker), *mode_flags, args.module])
            if code or "PANIC" in replay_output:
                return finish("FAILED", "leanchecker kernel replay failed", 1)
            result["kernel_replay"] = "fresh" if mode_flags else "local modules against imports"

    if source_fingerprint() != initial_fingerprint:
        return finish("INCOMPLETE", "local sources or project configuration changed during verification; rerun", 2)
    return finish("VERIFIED", "the final rectangular theorem matches the independent mathematical statement and only allowed standard axioms", 0)


if __name__ == "__main__":
    sys.exit(main())
