#!/usr/bin/env python3
"""Read-only audit/replay of the bounded MAX5 convex-core checkpoint.

The default only reads source, logs and manifests. --replay additionally
builds every selected Lean import in a temporary private library and
leaves the repository and frozen evidence unchanged.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(r"\b(?:sorry|admit|sorryAx|axiom|unsafe|native_decide)\b|Lean\.ofReduceBool")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lean_code(source: str) -> str:
    result, depth, quoted, i = [], 0, False, 0
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                depth += 1
                i += 2
            elif source.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                i += 1
        elif quoted:
            if source[i] == "\\":
                i += 2
            elif source[i] == '"':
                quoted = False
                i += 1
            else:
                i += 1
        elif source.startswith("/-", i):
            depth, i = 1, i + 2
            result.append(" ")
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        elif source[i] == '"':
            quoted = True
            i += 1
            result.append(" ")
        else:
            result.append(source[i])
            i += 1
    if depth or quoted:
        raise ValueError("Unterminated Lean comment/string")
    return "".join(result)


def closure(heads: list[str], selected: set[str]) -> list[str]:
    seen, active, order = set(), set(), []

    def visit(name: str) -> None:
        if name in seen:
            return
        if name in active:
            raise ValueError(f"Import cycle at {name}")
        if name not in selected:
            raise ValueError(f"Unbound local import {name}")
        active.add(name)
        source = lean_code((ROOT / name).read_text())
        found = FORBIDDEN.search(source)
        if found:
            raise ValueError(f"Forbidden construct {found.group()} in {name}")
        for line in source.splitlines():
            if line.startswith("import "):
                for module in line[7:].split():
                    candidate = module.replace(".", "/") + ".lean"
                    if (ROOT / candidate).is_file():
                        visit(candidate)
        active.remove(name)
        seen.add(name)
        order.append(name)

    for head in heads:
        visit(head)
    return order


def receipt_audits(receipt: dict) -> int:
    audits = receipt["axiom_audits"]
    if isinstance(audits, dict):
        values = audits.items()
    else:
        values = [(entry["declaration"], entry["axioms"]) for entry in audits]
    count = 0
    for declaration, axioms in values:
        if not set(axioms) <= ALLOWED:
            raise ValueError(f"Unexpected recorded axioms for {declaration}: {axioms}")
        count += 1
    return count


def lean_environment() -> tuple[str, list[str]]:
    # Querying Elan does not load/build the repository's Lake configuration.
    # Derive the external package paths from the frozen manifest instead of
    # running `lake env`, which could refresh a stale lakefile artifact.
    lean = subprocess.check_output(["elan", "which", "lean"],
                                   cwd=ROOT, text=True).strip()
    lake = json.loads((ROOT / "lake-manifest.json").read_text())
    external = [str((ROOT / lake["packagesDir"] / package["name"] /
                     (package.get("subDir") or "") / ".lake/build/lib").resolve())
                for package in lake["packages"]]
    external.append(str((Path(lean).parent.parent / "lib/lean").resolve()))
    return lean, external


def replay(order: list[str]) -> int:
    # Cached project artifacts are absent; every local import is rebuilt.
    lean, external = lean_environment()
    audit_count = 0
    with tempfile.TemporaryDirectory(prefix="max5-convex-checkpoint-") as temporary:
        library = Path(temporary) / "lib"
        library.mkdir()
        env = dict(os.environ)
        env["LEAN_PATH"] = os.pathsep.join([str(library), *external])
        for index, name in enumerate(order):
            artifact = library / Path(name).with_suffix(".olean")
            artifact.parent.mkdir(parents=True, exist_ok=True)
            command = ["python3", str(ROOT / "research/sN/overnight_20261103/lean_pool.py"),
                       lean, "-j1", "-o", str(artifact), name]
            result = subprocess.run(command, cwd=ROOT, env=env, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                    check=False)
            if result.returncode or "error:" in result.stdout:
                raise RuntimeError(f"Fresh build failed for {name}:\n{result.stdout}")
            for declaration, body in re.findall(
                    r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", result.stdout, re.S):
                used = {word.strip() for word in body.split(",") if word.strip()}
                if not used <= ALLOWED:
                    raise ValueError(f"Unexpected fresh axioms for {declaration}: {used}")
                audit_count += 1
            print(f"{index + 1}/{len(order)} {name}", flush=True)
    return audit_count


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--replay", action="store_true",
                        help="rebuild all local Lean imports in temporary artifacts")
    args = parser.parse_args()
    manifest = json.loads((HERE / "manifest.json").read_text())
    selected = manifest["files"]
    for name, expected in selected.items():
        path = ROOT / name
        if not path.is_file() or digest(path) != expected:
            raise ValueError(f"Missing or changed selected file: {name}")
    audits = 0
    for name in manifest["proof_receipts"]:
        receipt = json.loads((ROOT / name).read_text())
        if receipt["status"] not in {"PASS", "LEAN_VERIFIED_TARGETED_DIRTY_TREE_RECEIPT"}:
            raise ValueError(f"Unsuccessful proof receipt: {name}")
        for dependency, expected in receipt["files"].items():
            if selected.get(dependency) != expected:
                raise ValueError(f"Receipt dependency missing/mismatched: {dependency}")
        audits += receipt_audits(receipt)
    order = closure(manifest["lean_heads"], set(selected))
    selected_lean = {name for name in selected if name.endswith(".lean")}
    if not selected_lean <= set(order) | {"lakefile.lean"}:
        raise ValueError(f"Unexpected unbuilt Lean sources: {selected_lean - set(order)}")
    expected_paths = sorted([*selected, str((HERE / "manifest.json").relative_to(ROOT)),
                             str((HERE / "paths.json").relative_to(ROOT))])
    if json.loads((HERE / "paths.json").read_text()) != expected_paths:
        raise ValueError("Path-list/manifest mismatch")
    fresh_audits = replay(order) if args.replay else None
    # Detect concurrent changes and guarantee the frozen evidence was not changed.
    for name, expected in selected.items():
        if digest(ROOT / name) != expected:
            raise ValueError(f"Selected file changed during verification: {name}")
    print(json.dumps({"status": "PASS", "hashed_files": len(selected),
                      "local_lean_sources": len(order),
                      "recorded_axiom_audits": audits,
                      "fresh_axiom_audits": fresh_audits,
                      "repository_writes": 0}, sort_keys=True))


if __name__ == "__main__":
    main()
