#!/usr/bin/env python3
"""Source-bound ordinary-network width-tradeoff verification; --run rebuilds."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
MODULE = "MaxCaterpillar.Frontier.RandomRestriction.NetworkLowerBound"
DRIVER = "verification/h2/NetworkLowerBoundCheck.lean"
PREFIX = MODULE + "."
HEADLINES = [PREFIX + n for n in [
    "actual_neuron_event_cover", "model_counting_of_coefficients",
    "half_model_count_budget", "actual_network_tradeoff_of_coefficients",
    "second_width_tradeoff", "second_width_quadratic"]]

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
checks = [("network_lower_bound_build", ["lake", "build", MODULE]),
          ("network_lower_bound_exact", ["lake", "env", "lean", "-j1", DRIVER])]
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
text = (HERE / "network_lower_bound_exact.log").read_text()
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
    "scope": "Ordinary two-hidden-layer ReLU Network N h1 h2, arbitrary real parameters and arbitrary biases, exact maximum on every real input, N>=1040. No skip connections, normalized-model premise, parity assumption, support budget, probability estimate or finite-certificate premise in the public headline.",
    "bound": "h2 >= (1/400000000) min(N^2,N^4/h1)",
    "quadratic_corollary": "h1<=N^2 implies h2>=N^2/400000000",
    "nonvacuity": "Independent checker applies the headline at N=1040 to the separately proved ordinary caterpillar construction, retaining its exact first and second widths and all-real-input MAX identity.",
    "proof_route": "Actual arbitrary-parity half restriction, original-index moment and count budgets, actual common gap scale, closed five-variable coefficient certificate, actual original-neuron matching witness, three explicit bad events and actual per-neuron count, scalar cutoff optimization. Large h1 regime uses the independent actual linear width bound.",
    "reproduce": "python3 research/sN/jensen_bound/network_lower_bound_recheck.py --run",
    "toolchain_sha256": sha(ROOT / "lean-toolchain")}
path = HERE / "network_lower_bound_receipt.json"
path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
print(f"PASS {len(after)} source/toolchain hashes, {len(axioms)} standard-only axiom audits: {path.relative_to(ROOT)}")
