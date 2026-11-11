#!/usr/bin/env python3
"""Rebuild exact raw-network width/support tradeoffs and bind their sources."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
REL = HERE.relative_to(ROOT)
DRIVERS = [HERE / (s + ".lean") for s in
           ["WidthTradeoffCheck", "SharpTradeoffCheck", "WeightedTradeoffCheck"]]
PREFIX = "MaxCaterpillar.ExponentialPush.WidthTradeoff."
HEADLINES = [PREFIX + s for s in [
    "conditional_affine_width_tradeoff_explicit",
    "conditional_affine_feeding_tradeoff_explicit",
    "conditional_affine_sqrt_coefficient",
    "conditional_affine_feeding_sharp_explicit",
    "conditional_affine_feeding_sqrt_coefficient",
    "conditional_affine_support_tradeoff"]]
HEADLINES += [PREFIX + "Audit." + s for s in [
    "exact_total_width_contract", "exact_feeding_width_contract", "exact_rounding_budget",
    "exact_sharp_feeding_contract", "exact_sharp_rounding_budget", "exact_sqrt_coefficient_contract",
    "exact_weighted_support_contract", "exact_cost_at_small_support", "exact_clipped_cost_zero"]]
sys.path.insert(0, str(ROOT / "scripts"))
from verify import uncomment


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inventory():
    hashes, ordered, roots = {}, [], set()

    def visit(path):
        rel = str(path.relative_to(ROOT))
        if rel in hashes:
            return
        hashes[rel] = sha(path)
        for name in re.findall(r"^import\s+(\S+)", uncomment(path.read_text()), re.M):
            child = ROOT / (name.replace(".", "/") + ".lean")
            if child.is_file():
                if rel.startswith("research/") and name.startswith("MaxCaterpillar."):
                    roots.add(name)
                visit(child)
        if rel.startswith("research/") and path not in DRIVERS:
            ordered.append(path)

    for path in DRIVERS:
        visit(path)
    controls = [Path(__file__).resolve(), HERE / "README.md", HERE / "audit.md",
                ROOT / "lean-toolchain", ROOT / "lakefile.lean", ROOT / "lake-manifest.json",
                ROOT / "scripts/lean_lock.sh", ROOT / "scripts/verify.py"]
    for path in controls:
        hashes[str(path.relative_to(ROOT))] = sha(path)
    return hashes, ordered, sorted(roots)


before, leaves, roots = inventory()
checks = [("production_imports", ["lake", "build", *roots])]
for index, path in enumerate(leaves):
    rel = path.relative_to(ROOT)
    target = ROOT / ".lake/build/lib" / rel.with_suffix(".olean")
    target.parent.mkdir(parents=True, exist_ok=True)
    checks.append((f"leaf_{index:02d}_{path.stem}",
                   ["lake", "env", "lean", "-j1", "-o", str(target), str(rel)]))
checks += [(path.stem, ["lake", "env", "lean", "-j1", str(path.relative_to(ROOT))])
           for path in DRIVERS]
if "--run" in sys.argv:
    for name, args in checks:
        log = HERE / ("gate_" + name + ".log")
        with log.open("w") as output:
            process = subprocess.run([str(ROOT / "scripts/lean_lock.sh"), *args], cwd=ROOT,
                                     stdout=output, stderr=subprocess.STDOUT)
        (HERE / ("gate_" + name + ".exit")).write_text(str(process.returncode) + "\n")
        if process.returncode:
            raise SystemExit(f"FAILED {name}: see {log.relative_to(ROOT)}")

logs = {}
for name, _ in checks:
    assert (HERE / ("gate_" + name + ".exit")).read_text().strip() == "0", name
    path = HERE / ("gate_" + name + ".log")
    logs[str(path.relative_to(ROOT))] = sha(path)
output = "\n".join((HERE / ("gate_" + path.stem + ".log")).read_text() for path in DRIVERS)
axioms = {}
for name in HEADLINES:
    match = re.search("'" + re.escape(name) + r"' depends on axioms: \[([^]]*)\]", output, re.S)
    assert match, name
    dependencies = sorted(s.strip() for s in match[1].split(",") if s.strip())
    assert set(dependencies) <= {"propext", "Classical.choice", "Quot.sound"}, (name, dependencies)
    axioms[name] = dependencies
for rel in before:
    if rel.endswith(".lean"):
        code = uncomment((ROOT / rel).read_text())
        assert not re.search(r"\b(?:sorry|admit|native_decide|Lean\.ofReduceBool)\b|^\s*(?:axiom|unsafe)\b",
                             code, re.M), rel
after, _, _ = inventory()
assert before == after, "A source or control changed during the gate"
receipt = {
    "status": "PASS", "evidence_level": "Exact isolated research Lean declarations; no production-root integration implied",
    "source_count": len(after), "source_files": after, "logs": logs,
    "headline_axioms": axioms, "forbidden_construct_scan": "PASS",
    "drivers": [str(p.relative_to(ROOT)) for p in DRIVERS],
    "scope": "Original nine-array affine-skip networks computing actual MAX_N at every real input. Arbitrary real covectors, weights, biases, and skips. The conclusion counts original h2; total first width need not be bounded.",
    "sharp_feeding_parameter": "n=floor(N/2), F=card{original j | exists original k, W[k,j]!=0}, d=1+Nat.sqrt(105*F/(16*n^2)), q=floor(sqrt(n)/(8000*d)). If n>=10^10*d^2 and H(4q+1,q), h2>=exp(3sqrt(n)/(8000d))/2.",
    "quadratic_coefficient": "F<=C*N^2 permits d=6*ceil(sqrt(C)), with denominator48000*ceil(sqrt(C)) in the exponent, rather than published160000*C. The required H premise is at the corresponding new q.",
    "weighted_scope": "Let w(r)=0 for r<=2,1 for r=3,and(r)_4 for r>=4. Charge original rows only when bias=0,coordinate sum=0,some original W coefficient nonzero,and r<=n. If sum w(r)/2^r<=d^2*n^2, the same conditional bound holds without any row-count cap.",
    "conditional_boundary": "Growing LocalMatchingObstruction H remains an explicit unproved premise. No unconditional exponential theorem or joint large-H/nonlinear-network witness is claimed.",
    "derived_bridges": "Faithful raw normalization, same-index generic half localization, exact original feeding lineage, sharp simultaneous support budgets, auxiliary empty-graph event elimination, support-dependent averaging, and removal of supports exceeding the selected arity.",
    "semantic_controls": "Independent handwritten raw-array contracts expand evaluators, original W-column cardinality, support filters, bias/sum/feeding/clipping gates, literal matching floors and constants. Integer zero-width, odd/even,perfect-square and small/large support boundary controls are checked.",
    "reproduce": f"python3 {REL}/recheck.py --run",
}
destination = HERE / "receipt.json"
destination.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
print(f"PASS {len(after)} source/control hashes, {len(axioms)} standard-only audits: {destination.relative_to(ROOT)}")
