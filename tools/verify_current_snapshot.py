#!/usr/bin/env python3
"""Verify every shipped local Lean proof module in a cumulative snapshot.

The manifest fixes the route, endpoints, primitive statement probes, complete
local source inventory, and verification inputs. This checker does not create
or repair that manifest. It replays the complete local declaration graph using
the installed Lean kernel from an environment containing external imports only.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import re
import shutil
import subprocess
import sys


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lean_code(source):
    """Remove nested comments and strings before auditing Lean source tokens."""
    result, i, depth = [], 0, 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
            result.append("\n")
        elif source[i] == '"':
            i += 1
            while i < len(source) and source[i] != '"':
                i += 2 if source[i] == "\\" else 1
            i += 1
            result.append(" ")
        else:
            result.append(source[i])
            i += 1
    if depth:
        raise RuntimeError("Unterminated Lean comment")
    return "".join(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout", type=int, default=7200,
                        help="Maximum seconds for each build, probe, or replay command")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    root = Path(__file__).resolve().parents[1]
    name = "CURRENT_SNAPSHOT_MANIFEST_20260911.json"
    manifest_path = root / name
    manifest = json.loads(manifest_path.read_text())
    manifest_digest = digest(manifest_path)
    out = root / ".verification" / "current_snapshot_20260911"
    out.mkdir(parents=True, exist_ok=True)
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    forbidden = ["sorry", "admit", "axiom", "unsafe", "partial", "native_decide"]
    commands, evidence, axiom_count = [], [], 0

    def check_hashes():
        if digest(manifest_path) != manifest_digest:
            raise RuntimeError("Manifest changed during verification")
        for filename, expected in manifest["source_sha256"].items():
            path = root / filename
            if not path.is_file() or digest(path) != expected:
                raise RuntimeError(f"Source hash mismatch: {filename}")

    def run(argv, filename):
        print(f"Checking {filename}...", flush=True)
        with (out / filename).open("w") as stream:
            result = subprocess.run(argv, cwd=root, stdout=stream,
                                    stderr=subprocess.STDOUT, timeout=args.timeout)
        commands.append({"argv": argv, "log": filename, "exit_code": result.returncode})
        evidence.append(filename)
        if result.returncode:
            raise RuntimeError(f"Command failed; inspect {out / filename}")
        return (out / filename).read_text()

    try:
        check_hashes()
        actual = set()

        def visit(module):
            if module in actual:
                return
            if module != "MatrixSpencer" and not module.startswith("MatrixSpencer."):
                raise RuntimeError(f"Invalid project endpoint: {module}")
            actual.add(module)
            relative = module.replace(".", "/") + ".lean"
            if relative not in manifest["source_sha256"]:
                raise RuntimeError(f"Unfingerprinted project source: {relative}")
            code = lean_code((root / relative).read_text())
            admission = re.search(r"\b(" + "|".join(forbidden) + r")\b", code)
            if admission:
                raise RuntimeError(f"Forbidden proof-source token {admission.group()} in {relative}")
            for line in code.splitlines():
                if line.strip().startswith("import "):
                    for dependency in line.strip().split()[1:]:
                        if dependency == "MatrixSpencer" or dependency.startswith("MatrixSpencer."):
                            visit(dependency)

        for endpoint in manifest["endpoints"]:
            visit(endpoint)
        declared = set(manifest["modules"])
        if len(declared) != len(manifest["modules"]) or actual != declared:
            raise RuntimeError("Manifest differs from the complete endpoint import closure")
        inventory = {"MatrixSpencer"} | {
            str(p.relative_to(root).with_suffix("")).replace("/", ".")
            for p in (root / "MatrixSpencer").rglob("*.lean")
        }
        if inventory != actual:
            raise RuntimeError("Cumulative closure does not cover exactly all shipped project proof sources")
        for previous in manifest.get("prior_source_manifests", []):
            data = json.loads((root / previous["file"]).read_text())
            for filename, expected in data[previous["hash_field"]].items():
                if not (root / filename).is_file() or digest(root / filename) != expected:
                    raise RuntimeError(f"Earlier current manifest mismatch: {previous['file']}: {filename}")

        launcher = str(root / "run_lake.sh")
        run([launcher, "build", *manifest["endpoints"]], "build.log")
        for index, probe in enumerate(manifest["probes"]):
            text = run([launcher, "env", "lean", probe["file"]],
                       f"probe_{index:02d}_{Path(probe['file']).stem}.log")
            dependencies = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", text)
            if len(dependencies) != probe["axiom_probes"]:
                raise RuntimeError(f"Missing axiom probes in {probe['file']}")
            for group in dependencies:
                used = {x.strip() for x in group.split(",") if x.strip()}
                if not used <= allowed:
                    raise RuntimeError(f"Disallowed probe axioms: {used - allowed}")
            if "sorryAx" in text:
                raise RuntimeError(f"Admitted proof in {probe['file']}")
            axiom_count += len(dependencies)
        replay = run([launcher, "env", "lean", "--run", manifest["replay_driver"],
                      *manifest["modules"]], "replay.log")
        matches = re.findall(r"REPLAYED ([^:]+): (\d+) local declarations", replay)
        if len(matches) != len(actual) or {m for m, _ in matches} != actual:
            raise RuntimeError("Kernel replay did not cover every shipped local proof module")
        if "REPLAY_BASE_EXTERNAL_ONLY:" not in replay or "PROJECT_CLOSURE_REPLAYED:" not in replay:
            raise RuntimeError("Missing external-only-base replay certificate")
        if "sorryAx" in replay:
            raise RuntimeError("Admitted proof in replay")
        check_hashes()
        receipt = {
            "status": "VERIFIED",
            "checked_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "scope": manifest["scope"],
            "model": manifest["model"],
            "endpoints": manifest["endpoints"],
            "project_modules_including_entry": len(actual),
            "proof_modules_excluding_entry": len(actual) - 1,
            "replayed_project_declaration_records": sum(int(c) for _, c in matches),
            "axiom_probes": axiom_count,
            "allowed_axioms": sorted(allowed),
            "forbidden_source_tokens_checked": forbidden,
            "all_shipped_local_proof_sources_checked": True,
            "external_only_base_kernel_replay": True,
            "independent_kernel_implementation": False,
            "manifest_sha256": manifest_digest,
            "source_sha256": manifest["source_sha256"],
            "commands": commands,
            "evidence_sha256": {f: digest(out / f) for f in evidence},
        }
        encoded = json.dumps(receipt, indent=2) + "\n"
        (out / "verification.json").write_text(encoded)
        (root / "CURRENT_SNAPSHOT_VERIFICATION_20260911.json").write_text(encoded)
        provenance = root / "provenance" / "current_snapshot_20260911"
        provenance.mkdir(parents=True, exist_ok=True)
        for filename in [*evidence, "verification.json"]:
            shutil.copy2(out / filename, provenance / filename)
        shutil.copy2(manifest_path, provenance / name)
        print(f"VERIFIED: {len(actual)} modules including entry; "
              f"{receipt['replayed_project_declaration_records']} declaration records; "
              f"{axiom_count} endpoint axiom probes", flush=True)
        return 0
    except Exception as error:
        (out / "verification.json").write_text(json.dumps({
            "status": "FAILED", "reason": str(error), "commands": commands,
            "checked_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        }, indent=2) + "\n")
        print(f"FAILED: {error}", file=sys.stderr, flush=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
