#!/usr/bin/env python3
"""Fresh private Lean build of the general convex-core theorem's local closure.

Run through the repository Lean pool. Mathlib/Lean artifacts are the pinned
external dependencies; every repository-local Lean import is rebuilt in a
fresh private library, so stale repository artifacts cannot supply a proof.
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

ROOT = Path(__file__).resolve().parents[6]
HERE = Path(__file__).resolve().parent
REL = HERE.relative_to(ROOT)
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
HEADS = [HERE / "Check.lean"]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build_order(heads: list[Path]) -> list[Path]:
    order: list[Path] = []
    seen: set[Path] = set()
    active: set[Path] = set()

    def visit(path: Path) -> None:
        if path in seen:
            return
        if path in active:
            raise RuntimeError(f"Local import cycle: {path}")
        active.add(path)
        for line in path.read_text().splitlines():
            if not line.startswith("import "):
                continue
            for name in line[7:].split():
                dependency = ROOT / (name.replace(".", "/") + ".lean")
                if dependency.is_file():
                    visit(dependency)
        active.remove(path)
        seen.add(path)
        order.append(path)

    for head in heads:
        visit(head)
    return order


def clean_lean(text: str) -> str:
    """Remove strings and nested comments before the forbidden-token scan."""
    out: list[str] = []
    i = 0
    depth = 0
    quoted = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                i += 1
        elif quoted:
            if text[i] == "\\":
                i += 2
            elif text[i] == '"':
                quoted = False
                i += 1
            else:
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            out.append(" ")
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end == -1 else end
        elif text[i] == '"':
            quoted = True
            out.append(" ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    if depth or quoted:
        raise RuntimeError("Unterminated comment or string")
    return "".join(out)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--hash-only", action="store_true")
    args = parser.parse_args()
    receipt_path = HERE / "receipt.json"
    if args.hash_only:
        receipt = json.loads(receipt_path.read_text())
        bad = [name for name, expected in receipt["files"].items()
               if digest(ROOT / name) != expected]
        if bad:
            raise SystemExit(f"Hash drift: {bad}")
        print(json.dumps({"status": "PASS", "files": len(receipt["files"])}))
        return

    sources = build_order(HEADS)
    frozen = {str(path.relative_to(ROOT)): digest(path) for path in sources}
    forbidden = re.compile(r"\b(?:sorry|admit|sorryAx|axiom|unsafe|native_decide)\b|Lean\.ofReduceBool")
    for source in sources:
        bad = forbidden.search(clean_lean(source.read_text()))
        if bad:
            raise SystemExit(f"Forbidden construct {bad.group()} in {source}")
    lean = subprocess.check_output(["lake", "env", "which", "lean"], cwd=ROOT,
                                   text=True).strip()
    base_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"],
                                        cwd=ROOT, text=True).strip()
    version = subprocess.check_output([lean, "--version"], cwd=ROOT, text=True).strip()
    logroot = HERE / "verification"
    logroot.mkdir(exist_ok=True)
    audits: list[dict[str, object]] = []
    builds: list[dict[str, object]] = []
    evidence: set[Path] = set()
    with tempfile.TemporaryDirectory(prefix="max5-convex-lean-") as temporary:
        library = Path(temporary) / "lib"
        library.mkdir()
        env = dict(os.environ)
        env["LEAN_PATH"] = str(library) + os.pathsep + base_path
        for index, source in enumerate(sources):
            relative = source.relative_to(ROOT)
            artifact = library / relative.with_suffix(".olean")
            artifact.parent.mkdir(parents=True, exist_ok=True)
            log = logroot / f"{index:03d}_{source.stem}.log"
            exit_path = log.with_suffix(".exit")
            command = [lean, "-j1", "-o", str(artifact), str(relative)]
            with log.open("w") as handle:
                result = subprocess.run(command, cwd=ROOT, env=env,
                                        stdout=handle, stderr=subprocess.STDOUT,
                                        check=False)
            exit_path.write_text(f"{result.returncode}\n")
            evidence.update((log, exit_path))
            builds.append({"source": str(relative), "exit_code": result.returncode,
                           "log": str(log.relative_to(ROOT))})
            if result.returncode:
                raise SystemExit(f"Fresh Lean build failed: {log}")
            for declaration, body in re.findall(
                    r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log.read_text(), re.S):
                used = {word.strip() for word in body.split(",") if word.strip()}
                if not used <= ALLOWED:
                    raise SystemExit(f"Unexpected axioms for {declaration}: {used}")
                audits.append({"declaration": declaration, "axioms": sorted(used)})
            print(f"{index+1}/{len(sources)} {relative}", flush=True)

    changed = [name for name, sha in frozen.items() if digest(ROOT / name) != sha]
    if changed:
        raise SystemExit(f"Source changed during fresh build: {changed}")
    controls = {ROOT / "lean-toolchain", ROOT / "lake-manifest.json",
                ROOT / "lakefile.lean", Path(__file__).resolve(),
                ROOT / "research/sN/overnight_20261103/lean_pool.py"}
    files = set(sources) | controls | evidence
    report = {
        "status": "PASS",
        "scope": "Fresh sequential build of every repository-local Lean import of Check.lean "
                 "in a new private artifact library; pinned external Lean/Mathlib artifacts reused.",
        "lean_version": version,
        "source_count": len(sources),
        "builds": builds,
        "axiom_audits": audits,
        "files": {str(path.relative_to(ROOT)): digest(path) for path in sorted(files)},
    }
    receipt_path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "sources": len(sources),
                      "hashes": len(files), "axiom_audits": len(audits)}), flush=True)


if __name__ == "__main__":
    main()
