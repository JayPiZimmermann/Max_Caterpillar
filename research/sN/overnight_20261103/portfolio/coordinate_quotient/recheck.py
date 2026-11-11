#!/usr/bin/env python3
"""Rebuild and content-bind the isolated coordinate-identification contracts."""
from __future__ import annotations

import argparse
import ast
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
OWN = [HERE / (name + ".lean") for name in ("Model", "Section", "Bounds", "Check")]


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def local_imports(path: Path) -> list[Path]:
    result = []
    for line in path.read_text().splitlines():
        if line.strip().startswith("import "):
            for name in line.strip()[7:].split():
                candidate = ROOT / Path(*name.split(".")).with_suffix(".lean")
                if candidate.exists():
                    result.append(candidate)
    return result


def closure() -> list[Path]:
    seen, order = set(), []
    def visit(path: Path):
        if path in seen:
            return
        seen.add(path)
        for child in local_imports(path):
            visit(child)
        order.append(path)
    for path in OWN:
        visit(path)
    return order


def run_logged(command: list[str], stem: str):
    with (HERE / (stem + ".log")).open("w") as output:
        result = subprocess.run(command, cwd=ROOT, stdout=output,
                                stderr=subprocess.STDOUT, check=False)
    (HERE / (stem + ".exit")).write_text(str(result.returncode) + "\n")
    if result.returncode:
        raise SystemExit(f"Failed {stem}: see {HERE / (stem + '.log')}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--run", action="store_true")
    args = parser.parse_args()
    sources = closure()
    if args.run:
        production = sorted({str(path.relative_to(ROOT).with_suffix("")).replace("/", ".")
            for own in sources if own.parts[0:len(ROOT.parts)] == ROOT.parts
            and own.relative_to(ROOT).parts[0] == "research"
            for path in local_imports(own)
            if path.relative_to(ROOT).parts[0] == "MaxCaterpillar"})
        run_logged(["scripts/lean_lock.sh", "lake", "build", *production], "project")
        for path in sources:
            if path.relative_to(ROOT).parts[0] != "research":
                continue
            rel = path.relative_to(ROOT)
            artifact = ROOT / ".lake/build/lib" / rel.with_suffix(".olean")
            artifact.parent.mkdir(parents=True, exist_ok=True)
            stem = path.stem.lower() if path.parent == HERE else "dependency_" + path.stem.lower()
            run_logged(["python3", "research/sN/overnight_20261103/lean_pool.py",
                        "lake", "env", "lean", "-o", str(artifact), str(rel)], stem)
    reports = {}
    logs = {}
    for name in ("model", "section", "bounds", "check"):
        log_path = HERE / (name + ".log")
        assert (HERE / (name + ".exit")).read_text().strip() == "0", name
        log = log_path.read_text()
        assert "error:" not in log, name
        found = {decl: [x.strip() for x in axioms.split(",") if x.strip()]
                 for decl, axioms in re.findall(
                     r"'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.S)}
        assert found and all(set(xs) <= ALLOWED for xs in found.values()), name
        reports.update(found)
        logs[str(log_path.relative_to(ROOT))] = sha(log_path)
    checker = ROOT / "research/sN/jensen_bound/star_obstruction/star_obstruction_receipt.py"
    parsed = ast.parse(checker.read_text())
    node = next(n for n in parsed.body
                if isinstance(n, ast.FunctionDef) and n.name == "strip_comments")
    namespace = {}
    exec(compile(ast.Module(body=[node], type_ignores=[]), str(checker), "exec"), namespace)
    forbidden = re.compile(r"\b(sorry|admit|native_decide|sorryAx)\b|\bLean\.ofReduceBool\b|"
                           r"^\s*(?:private\s+)?axiom\s+", re.M)
    for path in sources:
        assert not forbidden.search(namespace["strip_comments"](path.read_text())), str(path)
    controls = [HERE / "README.md", Path(__file__).resolve(), checker,
                ROOT / "lean-toolchain", ROOT / "lakefile.lean", ROOT / "lake-manifest.json",
                ROOT / "scripts/lean_lock.sh", ROOT / "research/sN/overnight_20261103/lean_pool.py"]
    data = {
        "status": "PASS",
        "state": "isolated research Lean contracts; frozen public roots unchanged",
        "scope": "Exact nine-array coordinate quotient; MAX transport; same-size deletion dominance; transported quadratic and conditional bounds.",
        "limits": ["No improvement over optimal support-transversal size.",
                   "The growing-matching obstruction is still an explicit hypothesis.",
                   "No unconditional exponential conclusion."],
        "axiom_reports": reports,
        "source_sha256": {str(path.relative_to(ROOT)): sha(path) for path in sorted(sources)},
        "control_sha256": {str(path.relative_to(ROOT)): sha(path) for path in controls},
        "logs_sha256": logs,
        "source_count": len(sources),
        "full_rebuild_performed_this_run": args.run,
        "reproduce": "python3 research/sN/overnight_20261103/portfolio/coordinate_quotient/recheck.py --run",
    }
    (HERE / "receipt.json").write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "source_count": len(sources),
                      "axiom_reports": len(reports)}))


if __name__ == "__main__":
    main()
