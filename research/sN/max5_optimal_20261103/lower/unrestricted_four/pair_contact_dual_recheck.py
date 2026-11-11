#!/usr/bin/env python3
"""Rebuild the finite pair-contact dual leaf and literal-type consumer.

This checks the stated finite-vector theorem.  It does not formalize a
network reduction or prove a MAX5 width endpoint.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[5]
HERE = Path(__file__).resolve().parent
REL = HERE.relative_to(ROOT)
POOL = ROOT / "research/sN/overnight_20261103/lean_pool.py"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(name, args):
    log = HERE / (name + ".log")
    with log.open("w") as out:
        result = subprocess.run(
            ["python3", str(POOL), "lake", "env", "lean", *args],
            cwd=ROOT, stdout=out, stderr=subprocess.STDOUT, check=False)
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
    producer = REL / "PairContactDual.lean"
    consumer = REL / "PairContactDualCheck.lean"
    for path in (producer, consumer):
        source = (ROOT / path).read_text()
        if re.search(r"\b(sorry|sorryAx|admit|axiom|native_decide|unsafe)\b|Lean\.ofReduceBool", source):
            raise SystemExit(f"Forbidden source construct: {path}")
    artifact = ROOT / ".lake/build/lib" / REL / "PairContactDual.olean"
    artifact.parent.mkdir(parents=True, exist_ok=True)
    audits = run("pair_contact_dual_artifact", ["-o", str(artifact), str(producer)])
    audits.update(run("pair_contact_dual_check", [str(consumer)]))
    if len(audits) != 5:
        raise SystemExit(f"Expected five declared axiom audits, got {len(audits)}")
    paths = [producer, consumer, REL / Path(__file__).name,
             REL / "PAIR_CONTACT_DUAL.md", Path("lean-toolchain"),
             Path("lake-manifest.json"), Path("lakefile.lean"),
             POOL.relative_to(ROOT)]
    for stem in ("pair_contact_dual_artifact", "pair_contact_dual_check"):
        paths += [REL / (stem + ".log"), REL / (stem + ".exit")]
    receipt = {
        "status": "PASS",
        "scope": "Exact finite real-vector classification; no network-width claim",
        "type_consumer": str(consumer),
        "axiom_audits": audits,
        "repository_lean_import_closure": [str(producer), str(consumer)],
        "external_dependencies": "Mathlib and Lake packages bound by lake-manifest.json and lean-toolchain",
        "files": {str(path): digest(ROOT / path) for path in sorted(paths)},
    }
    (HERE / "pair_contact_dual_receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"PASS: {len(paths)} source/control/evidence hashes; {len(audits)} standard-axiom audits")


if __name__ == "__main__":
    main()
