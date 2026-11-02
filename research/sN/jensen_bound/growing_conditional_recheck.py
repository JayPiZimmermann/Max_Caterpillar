#!/usr/bin/env python3
"""Source-bound actual growing-matching transfer gate, conditional only on structural H."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
MODULE = "MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.ConditionalBound"
DRIVER = "verification/h2/GrowingConditionalBoundCheck.lean"
PREFIX = "MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching."
HEADLINES = [PREFIX + n for n in [
    "shortRankEvent_fraction_le", "actual_event_cover", "finite_union_fraction_bound",
    "conditional_finite_transfer", "localMatchingObstruction_five_two"]]

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
checks = [("growing_conditional_build", ["lake", "build", MODULE]),
          ("growing_conditional_exact", ["lake", "env", "lean", "-j1", DRIVER])]
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
text = (HERE / "growing_conditional_exact.log").read_text()
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
    "scope": "Actual translation-normalized homogeneous real skip Network(m+k,h1,h2), exact MAX on every real input. Finite inequality(T) holds conditional ONLY on LocalMatchingObstruction(k,q), q>0, k>0 and numeric cutoff conditions m>=2,K>=4,K<m,m+k>=4. A common actual gap scale and all three bad-event and original-neuron probability estimates are DERIVED, not assumed.",
    "conditional_status": "H(k,q) is an explicit actual finite-network obstruction with no counting/probability premise. The exact driver expands it. H(5,2) is independently proved; the growing-q hierarchy remains unproved. This receipt does NOT establish an unconditional exponential network lower bound.",
    "bound": "1-8K/m-M*(k)_3/(m+k)_3-L/(m+k)_4*[K^2*(1+k/m)/(1-K/m)+(k)_2*K/2] <= h2*(k)_(2q)/(m+k)_(2q)*(c^q)^(-1)*exp(c*k*(m+k-1)), c=7K/[24m(m-1)]. M counts ALL first supports>=3, L sums their falling fourth moments, including output-only rows.",
    "nonvacuity": "Independent checker verifies the proved H(5,2) instance and constructs an actual normalized MAX10 network at admissible k=5,m=5,K=4 from the separate caterpillar theorem. This does not assert that this particular lower-side expression is positive.",
    "proof_route": "Actual generic localization gives an original surviving neuron with a selected q-matching under H; literal support-good complement implies actual cleanliness; the actual clean-rank event is bounded by the correlated selected-tail mean; exact q!-preserving graph selection and exponential-series suppression give the per-neuron envelope. Explicit actual B1/B2/B3 fractions and a finite union yield(T).",
    "reproduce": "python3 research/sN/jensen_bound/growing_conditional_recheck.py --run",
    "toolchain_sha256": sha(ROOT / "lean-toolchain")}
path = HERE / "growing_conditional_receipt.json"
path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
print(f"PASS {len(after)} source/toolchain hashes, {len(axioms)} standard-only axiom audits: {path.relative_to(ROOT)}")
