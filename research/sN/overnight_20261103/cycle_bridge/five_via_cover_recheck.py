#!/usr/bin/env python3
"""Reproduce the separate star-only H(5,2) leaf and bind its full closure."""
from pathlib import Path
import argparse
import ast
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
NEW = "research.sN.overnight_20261103.cycle_bridge.FiveViaCover"
OLD = "MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.FiveInstance"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def closure(root):
    seen = {}
    todo = [root]
    while todo:
        module = todo.pop()
        path = ROOT / (module.replace(".", "/") + ".lean")
        if not path.exists() or module in seen:
            continue
        seen[module] = path
        for line in path.read_text().splitlines():
            if line.strip().startswith("import "):
                todo.extend(line.strip()[7:].split())
    return seen


def run(stem, command):
    with (HERE / (stem + ".log")).open("w") as stream:
        code = subprocess.run(command, cwd=ROOT, stdout=stream,
                              stderr=subprocess.STDOUT, check=False).returncode
    (HERE / (stem + ".exit")).write_text(str(code) + "\n")
    if code:
        raise SystemExit(f"{stem} failed ({code}); inspect its log")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--run", action="store_true")
    args = parser.parse_args()
    core_path = HERE / "receipt.json"
    core = json.loads(core_path.read_text())
    assert core["status"] == "PASS", "run the cycle-bridge core gate first"
    for relative, digest in core["source_files"].items():
        assert sha(ROOT / relative) == digest, ("core source drift", relative)
    for relative, digest in core["logs"].items():
        assert sha(ROOT / relative) == digest, ("core log drift", relative)
    if args.run:
        run("five_via_cover_imports", ["scripts/lean_lock.sh", "lake", "build",
            "MaxCaterpillar.Frontier.StarCertificate.StarObstruction",
            "MaxCaterpillar.Frontier.RandomRestriction.BraidModelInteraction",
            "MaxCaterpillar.Frontier.StarCertificate.SmallMatchingGraphStarFormula"])
        artifact = ROOT / ".lake/build/lib" / HERE.relative_to(ROOT) / "FiveViaCover.olean"
        artifact.parent.mkdir(parents=True, exist_ok=True)
        run("five_via_cover", ["scripts/lean_lock.sh", "lake", "env", "lean", "-j1",
            "-o", str(artifact), str(HERE / "FiveViaCover.lean")])
        run("five_via_cover_check", ["scripts/lean_lock.sh", "lake", "env", "lean", "-j1",
            str(HERE / "FiveViaCoverCheck.lean")])

    reports = {}
    logs = {}
    for stem in ["five_via_cover_imports", "five_via_cover", "five_via_cover_check"]:
        assert (HERE / (stem + ".exit")).read_text().strip() == "0", stem
        log = (HERE / (stem + ".log")).read_text()
        assert "error:" not in log, stem
        logs[stem] = {"exit": 0, "sha256": sha(HERE / (stem + ".log"))}
        if stem != "five_via_cover_imports":
            found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.S)
            assert found, stem
            for name, values in found:
                axioms = sorted(v.strip() for v in values.split(",") if v.strip())
                assert set(axioms) <= ALLOWED, (name, axioms)
                reports[name] = axioms
    assert len(reports) == 6, reports

    new = closure(NEW)
    old = closure(OLD)
    check = closure(NEW + "Check")
    assert not any("Triangle" in name for name in new)
    scanner = ROOT / "research/sN/jensen_bound/star_obstruction/star_obstruction_receipt.py"
    node = next(n for n in ast.parse(scanner.read_text()).body
                if isinstance(n, ast.FunctionDef) and n.name == "strip_comments")
    namespace = {}
    exec(compile(ast.Module(body=[node], type_ignores=[]), str(scanner), "exec"), namespace)
    forbidden = re.compile(r"\b(sorry|admit|native_decide|sorryAx)\b|\bLean\.ofReduceBool\b|(?m:^\s*(?:private\s+)?axiom\s+)")
    for path in check.values():
        assert not forbidden.search(namespace["strip_comments"](path.read_text())), path
    added = sorted(set(new) - set(old))
    removed = sorted(set(old) - set(new))
    controls = [Path(__file__).resolve(), HERE / "FiveViaCover.md", scanner, core_path,
                ROOT / "lean-toolchain", ROOT / "lake-manifest.json", ROOT / "scripts/lean_lock.sh"]
    receipt = {
        "status": "PASS",
        "scope": "Research-only exact actual H(5,2), using the closed all-real star certificate and generic cycle deletion; no triangle import or theorem dependency.",
        "limits": "No stronger numerical lower bound. The expansion may increase width. Core research imports are rebuilt by the separate cycle-bridge gate; this gate rebuilds production star/model imports and the two new leaves.",
        "reproduce": "python3 research/sN/overnight_20261103/cycle_bridge/five_via_cover_recheck.py --run",
        "axiom_audits": reports,
        "core_receipt_validated": True,
        "logs": logs,
        "source_sha256": {str(p.relative_to(ROOT)): sha(p) for p in sorted(check.values())},
        "control_sha256": {str(p.relative_to(ROOT)): sha(p) for p in controls},
        "comparison": {
            "old_project_module_count": len(old), "new_project_module_count": len(new),
            "old_source_bytes": sum(p.stat().st_size for p in old.values()),
            "new_source_bytes": sum(p.stat().st_size for p in new.values()),
            "new_triangle_modules": [],
            "added": {m: new[m].stat().st_size for m in added},
            "removed": {m: old[m].stat().st_size for m in removed},
            "added_bytes": sum(new[m].stat().st_size for m in added),
            "removed_bytes": sum(old[m].stat().st_size for m in removed)},
        "controls": ["Expanded actual cover-one counterexample input", "Expanded actual two-edge disjoint matching", "Nonempty one-edge cover", "Empty-cover boundary"],
    }
    output = HERE / "five_via_cover_receipt.json"
    output.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "sources": len(check), "axiom_audits": len(reports),
                      "triangle_modules": 0, "receipt": str(output.relative_to(ROOT))}))


if __name__ == "__main__":
    main()
