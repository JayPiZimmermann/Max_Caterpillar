#!/usr/bin/env python3
"""Source-bound feeding-only structural and normalized-counting refinement gate."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
MODULE = "MaxCaterpillar.Frontier.RandomRestriction.FeedingCounting"
DRIVER = "verification/h2/FeedingCoreCheck.lean"
PREFIX = "MaxCaterpillar.Frontier.RandomRestriction.FeedingCore."
HEADLINES = [PREFIX + n for n in [
    "core_inner", "core_edgeWeight", "absorb_eval", "absorb_normalized",
    "absorb_auxiliary_edgeWeight", "exists_original_matching_of_feeding_braid",
    "structural_witness_of_generic_embedding_feeding", "model_counting_feeding_on_tail"]]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def code_only(text):
    result = []
    i, depth, quoted = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i): depth += 1; i += 2
            elif text.startswith("-/", i): depth -= 1; i += 2
            else: i += 1
        elif quoted:
            if text[i] == "\\": i += 2
            elif text[i] == '"': quoted = False; i += 1
            else: i += 1
        elif text.startswith("/-", i): depth = 1; i += 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        elif text[i] == '"': quoted = True; i += 1
        else: result.append(text[i]); i += 1
    return "".join(result)

def closure():
    result = {}
    def visit(path):
        rel = str(path.relative_to(ROOT))
        if rel in result: return
        result[rel] = sha(path)
        for line in code_only(path.read_text()).splitlines():
            if line.startswith("import "):
                for name in line.split()[1:]:
                    dependency = ROOT / (name.replace(".", "/") + ".lean")
                    if dependency.is_file(): visit(dependency)
    visit(ROOT / DRIVER)
    visit(ROOT / (MODULE.replace(".", "/") + ".lean"))
    return result

before = closure()
checks = [("feeding_core_build", ["lake", "build", MODULE]),
          ("feeding_core_exact", ["lake", "env", "lean", "-j1", DRIVER])]


if "--run" in sys.argv:
    for name, args in checks:
        with (HERE / (name + ".log")).open("w") as output:
            process = subprocess.run([str(ROOT / "scripts/lean_lock.sh"), *args],
                                     cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
        (HERE / (name + ".exit")).write_text(str(process.returncode) + "\n")
        if process.returncode: raise SystemExit(f"FAILED {name}")
logs = {}
for name, _ in checks:
    assert (HERE / (name + ".exit")).read_text().strip() == "0", name
    logs[str((HERE / (name + ".log")).relative_to(ROOT))] = sha(HERE / (name + ".log"))
text = (HERE / "feeding_core_exact.log").read_text()
axioms = {}
for declaration in HEADLINES:
    match = re.search("'" + re.escape(declaration) + r"' depends on axioms: \[([^]]*)\]", text, re.S)
    assert match, declaration
    dependencies = sorted(x.strip() for x in match[1].split(",") if x.strip())
    assert set(dependencies) <= {"propext", "Classical.choice", "Quot.sound"}, (declaration, dependencies)
    axioms[declaration] = dependencies
for path in before:
    code = code_only((ROOT / path).read_text())
    assert not re.search(r"\b(?:sorry|admit|native_decide|Lean\.ofReduceBool)\b|^\s*(?:axiom|unsafe)\b", code, re.M), path
after = closure()
assert before == after, "Source changed during verification"
after[str(Path(__file__).resolve().relative_to(ROOT))] = sha(Path(__file__).resolve())
after["lean-toolchain"] = sha(ROOT / "lean-toolchain")
receipt = {
    "status": "PASS", "module": MODULE, "driver": DRIVER,
    "source_files": after, "source_count": len(after), "logs": logs,
    "headline_axioms": axioms, "forbidden_construct_scan": "PASS",
    "scope": "Research helper refinement for primitive NormalizedNetwork arrays with arbitrary linear/first-output skips. Feeding core preserves every original inner function and aggregate braid graph; tagged output-term absorption preserves full evaluation and normalization. Actual MAX5 obstruction and generic-point witness require small support only for feeding rows, return original Fin h2, and discharge the finite certificate. Normalized counting charges only core supports and retains the explicit half-model nonbraid-count budget.",
    "remaining_obligations": "These helper obligations are complete. The final affine-skip feeding-width theorem is independently verified by affine_feeding_recheck.py; this receipt audits the structural and counting helpers.",
    "exact_contracts": "The checker expands Feeding to existence of a nonzero W entry and expands the cutoff counting prerequisite, so neither output-only row support restrictions nor probability/counting estimates are hidden.",
    "reproduce": "python3 research/sN/jensen_bound/feeding_core_recheck.py --run",
    "toolchain_sha256": sha(ROOT / "lean-toolchain")}
path = HERE / "feeding_core_receipt.json"
path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
print(f"PASS {len(after)} source/toolchain hashes, {len(axioms)} standard-only axiom audits: {path.relative_to(ROOT)}")
