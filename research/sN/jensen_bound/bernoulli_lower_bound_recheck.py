#!/usr/bin/env python3
"""Source-bound actual normalized Bernoulli conditional sqrt theorem verification."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
MODULE = "MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli.LowerBound"
DRIVER = "verification/h2/BernoulliLowerBoundCheck.lean"
PREFIX = "MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching."
HEADLINES = [PREFIX + n for n in [
    "Bernoulli.actual_raw_event_cover", "Bernoulli.conditional_union_bound",
    "Bernoulli.finite_conditional_bound", "Bernoulli.conditional_sqrt_lower_bound",
    "localMatchingObstruction_five_two"]]

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
checks = [("bernoulli_lower_bound_module", ["lake", "build", MODULE]),
          ("bernoulli_lower_bound_exact", ["lake", "env", "lean", "-j1", DRIVER])]
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
text = (HERE / "bernoulli_lower_bound_exact.log").read_text()
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
    "scope": "Primitive actual NormalizedNetwork n h1 h2, arbitrary real weights and all homogeneous affine/first-output skips, exact MAX on every real input, translation-normalized. Actual ALL-first support statistics M and L satisfy M,L<=d^2*n^2, d>=1,n>=10^10*d^2. The only structural assumption is LocalMatchingObstruction at the literal q=floor((sqrt(n)/(1000d))/8), k0=4q+1. Final theorem has no generic scale, conditional probability, rarity-mass, event cover, rank or counting premise.",
    "conditional_status": "This is a conditional exp(c sqrt n) actual-network theorem. Growing structural H is OPEN and no joint witness of H at these literal large parameters is supplied. Known H(5,2) is an independent low-level control only. The result is not advertised as an unconditional exponential lower bound.",
    "bound": "(1/2)*exp(3*sqrt(n)/(8000*d))<=h2",
    "exact_contracts": "Independent checker expands H as an actual finite-network matching obstruction, exposes q/k0 literal floors, and expands M as the actual count of all first supports>=3 and L as the actual sum of falling fourth moments. These geometry bounds are not probability estimates; the raw-affine half-restriction wrapper discharges them separately.",
    "nonvacuity_controls": "ParameterBounds(10^10,1) is proved. The known H(5,2) and an actual normalized MAX10 construction are checked separately; neither is claimed to instantiate the open growing-H premise of the final sqrt theorem.",
    "proof_route": "Literal selected subsets with canonical keep/tail embeddings and true uniform variable-tail raw permutations; actual original-neuron witness under upward structural H; raw short-rank/family-good event cover; genuine downward Bernoulli conditional union; canonical support avoidance and floor cap, proved positive mass; actual conditional neuron envelope without rarity loss; derived support/cardinality tails; explicit scalar floors and exponential suppression.",
    "reproduce": "python3 research/sN/jensen_bound/bernoulli_lower_bound_recheck.py --run",
    "toolchain_sha256": sha(ROOT / "lean-toolchain")}
path = HERE / "bernoulli_lower_bound_receipt.json"
path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
print(f"PASS {len(after)} source/toolchain hashes, {len(axioms)} standard-only axiom audits: {path.relative_to(ROOT)}")
