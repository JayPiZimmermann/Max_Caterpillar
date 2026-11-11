#!/usr/bin/env python3
"""Replay the five-neuron invisible shallow function and exact-type consumer.

This is a contact-data counterexample, not a MAX5 network construction or
a width lower bound.  Rebuilds the exact repository-local import closure
through its ordinary Lake target before compiling the two new leaves.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[5]
HERE = Path(__file__).resolve().parent
REL = HERE.relative_to(ROOT)
POOL = Path("research/sN/overnight_20261103/lean_pool.py")
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(name, args):
    log = HERE / (name + ".log")
    with log.open("w") as out:
        result = subprocess.run(["python3", str(POOL), *args], cwd=ROOT,
                                stdout=out, stderr=subprocess.STDOUT, check=False)
    (HERE / (name + ".exit")).write_text(str(result.returncode) + "\n")
    if result.returncode:
        raise SystemExit(f"Lean failed: {log}")
    text = log.read_text()
    if "error:" in text:
        raise SystemExit(f"Error text in {log}")
    audits = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text, re.S)
    for declaration, raw in audits:
        axioms = {x.strip() for x in raw.split(",") if x.strip()}
        if not axioms <= ALLOWED:
            raise SystemExit(f"Unexpected axioms for {declaration}: {axioms}")
    return {declaration: sorted({x.strip() for x in raw.split(",") if x.strip()})
            for declaration, raw in audits}


def main():
    producer = REL / "InvisibleShallow.lean"
    consumer = REL / "InvisibleShallowCheck.lean"
    spec = importlib.util.spec_from_file_location("source_checks", ROOT / "scripts/verify.py")
    checks = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checks)
    seen, external = set(), set()
    stack = [producer, consumer]
    while stack:
        path = stack.pop()
        if path in seen:
            continue
        seen.add(path)
        source = checks.uncomment((ROOT / path).read_text())
        if re.search(r"\b(sorry|sorryAx|admit|axiom|native_decide|unsafe)\b|Lean\.ofReduceBool", source):
            raise SystemExit(f"Forbidden source construct: {path}")
        for line in source.splitlines():
            if line.startswith("import "):
                for module in line.split()[1:]:
                    local = Path(module.replace(".", "/") + ".lean")
                    if (ROOT / local).is_file():
                        stack.append(local)
                    else:
                        external.add(module)
    artifact = ROOT / ".lake/build/lib" / REL / "InvisibleShallow.olean"
    artifact.parent.mkdir(parents=True, exist_ok=True)
    run("invisible_dependency", ["lake", "build", "MaxCaterpillar.Frontier.Basic"])
    audits = run("invisible_artifact", ["lake", "env", "lean", "-o", str(artifact), str(producer)])
    audits.update(run("invisible_check", ["lake", "env", "lean", str(consumer)]))
    if len(audits) != 13:
        raise SystemExit(f"Expected thirteen axiom audits, got {len(audits)}")
    paths = seen | {REL / Path(__file__).name, ROOT.joinpath("scripts/verify.py").relative_to(ROOT),
                   REL / "INVISIBLE_LEAN.md", Path("lean-toolchain"), Path("lake-manifest.json"),
                   Path("lakefile.lean"), POOL}
    for stem in ("invisible_dependency", "invisible_artifact", "invisible_check"):
        paths |= {REL / (stem + ".log"), REL / (stem + ".exit")}
    receipt = {
        "status": "LEAN_VERIFIED_TARGETED_DIRTY_TREE_RECEIPT",
        "scope": "All-real five-neuron shallow counterexample to reconstruction from contact data; no network-width claim",
        "type_consumer": str(consumer),
        "axiom_audits": audits,
        "repository_lean_import_closure": [str(p) for p in sorted(seen)],
        "external_imports_bound_by_lake_manifest": sorted(external),
        "files": {str(path): digest(ROOT / path) for path in sorted(paths)},
    }
    (HERE / "invisible_receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"PASS: {len(paths)} hashes; {len(seen)} local Lean sources; {len(audits)} standard-axiom audits")


if __name__ == "__main__":
    main()
