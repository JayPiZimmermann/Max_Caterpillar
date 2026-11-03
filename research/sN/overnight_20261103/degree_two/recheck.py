#!/usr/bin/env python3
"""Rebuild the actual degree-two MAX lower bound and bind its exact scope."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
REL = HERE.relative_to(ROOT)
DRIVER = REL / "Check.lean"
LOGS = HERE / "logs"
LOGS.mkdir(exist_ok=True)
HEADLINES = [
    "MaxCaterpillar.Overnight.DegreeTwo.raw_width_binomial",
    "MaxCaterpillar.Overnight.DegreeTwo.raw_width_exponential",
    "MaxCaterpillar.Overnight.DegreeTwo.raw_width_exponential_real",
    "MaxCaterpillar.Overnight.DegreeTwo.Audit.raw_nine_array_bounds",
    "MaxCaterpillar.Overnight.DegreeTwo.Audit.four_input_nonvacuity",
    "MaxCaterpillar.ExponentialPush.DegreeTwo.exists_active_second_on_set",
    "MaxCaterpillar.Overnight.DegreeTwo.twoComponentSets_card_le",
    "MaxCaterpillar.ExponentialPush.DegreeTwo.Recession.model_computes_max",
    "MaxCaterpillar.Overnight.DegreeTwo.raw_width_binomial_sharp",
    "MaxCaterpillar.Overnight.DegreeTwo.raw_width_exponential_sharp_real",
    "MaxCaterpillar.Overnight.DegreeTwo.normalized_width_binomial_sharp_feeding",
    "MaxCaterpillar.Overnight.DegreeTwo.SharpAudit.raw_nine_array_sharp_bounds",
    "MaxCaterpillar.Overnight.DegreeTwo.SharpAudit.normalized_feeding_exact_type",
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def code_only(text):
    result, i, depth, quoted = [], 0, 0, False
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
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            quoted = True
            i += 1
        else:
            result.append(text[i])
            i += 1
    return "".join(result)


def inspect_closure():
    hashes, research_order, project_boundary = {}, [], set()

    def visit(path):
        rel = str(path.relative_to(ROOT))
        if rel in hashes:
            return
        hashes[rel] = sha(path)
        for line in code_only(path.read_text()).splitlines():
            if not line.startswith("import "):
                continue
            for name in line.split()[1:]:
                dep = ROOT / (name.replace(".", "/") + ".lean")
                if dep.is_file():
                    if rel.startswith("research/") and not name.startswith("research."):
                        project_boundary.add(name)
                    visit(dep)
        if rel.startswith("research/"):
            research_order.append(rel)

    visit(ROOT / DRIVER)
    for path in [Path(__file__).resolve(), HERE / "README.md", HERE / "AUDIT.md",
                 HERE / "SHARP_AUDIT.md",
                 ROOT / "lean-toolchain", ROOT / "lakefile.lean", ROOT / "lake-manifest.json",
                 ROOT / "scripts/lean_lock.sh"]:
        hashes[str(path.relative_to(ROOT))] = sha(path)
    return hashes, research_order, sorted(project_boundary)


before, order, boundary = inspect_closure()
checks = [("project_imports", ["lake", "build", *boundary])]
for number, rel in enumerate(order):
    source = Path(rel)
    artifact = ROOT / ".lake/build/lib" / source.with_suffix(".olean")
    artifact.parent.mkdir(parents=True, exist_ok=True)
    checks.append((f"{number:03d}_{source.stem}",
                   ["lake", "env", "lean", "-j1", "-o", str(artifact), rel]))

if "--run" in sys.argv:
    for name, args in checks:
        log = LOGS / ("gate_" + name + ".log")
        with log.open("w") as output:
            proc = subprocess.run([str(ROOT / "scripts/lean_lock.sh"), *args],
                                  cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
        (LOGS / ("gate_" + name + ".exit")).write_text(str(proc.returncode) + "\n")
        if proc.returncode:
            raise SystemExit(f"FAILED {name}; see {log.relative_to(ROOT)}")

logs = {}
for name, _ in checks:
    assert (LOGS / ("gate_" + name + ".exit")).read_text().strip() == "0", name
    log = LOGS / ("gate_" + name + ".log")
    logs[str(log.relative_to(ROOT))] = sha(log)

output = (LOGS / ("gate_" + checks[-1][0] + ".log")).read_text()
axioms = {}
for declaration in HEADLINES:
    found = re.search("'" + re.escape(declaration) + r"' depends on axioms: \[([^]]*)\]",
                      output, re.S)
    assert found, declaration
    deps = sorted(x.strip() for x in found[1].split(",") if x.strip())
    assert set(deps) <= {"propext", "Classical.choice", "Quot.sound"}, deps
    axioms[declaration] = deps

for rel in before:
    if rel.endswith(".lean"):
        code = code_only((ROOT / rel).read_text())
        assert not re.search(r"\b(?:sorry|admit|native_decide|Lean\.ofReduceBool)\b|^\s*(?:axiom|unsafe)\b",
                             code, re.M), rel

after, _, _ = inspect_closure()
assert before == after, "Source/control changed during verification"
receipt = {
    "status": "PASS",
    "evidence_level": "Research-only exact Lean declarations with reconstructed import closure; production roots unchanged",
    "driver": str(DRIVER),
    "source_files": after,
    "source_count": len(after),
    "research_modules_rebuilt": order,
    "project_imports_rebuilt": boundary,
    "logs": logs,
    "headline_axioms": axioms,
    "forbidden_construct_scan": "PASS",
    "scope": "Actual real nine-array affine-skip/bias MAX_N networks with every first covector zero-sum and support at most two, and every original summed signed interaction graph of maximum degree at most two. No first-hidden-width cap, sign condition, fixed graph ordering, genericity hypothesis, or matching conjecture is assumed. Sharp bound for every m>=3: 2*choose(N,m)<=h2*(2N+(m-1)N^2). For N>=6: h2>=4*2^N/[N^3(N+1)]. The earlier fourfold weaker bounds remain verified compatibility statements. A separate normalized theorem requires braid support only for feeding first rows, while retaining translation normalization for all rows.",
    "actual_model_bridges": "Recession preserves every original A,U,W,L,B,d array and both hidden indices. Outer normalization only masks entire second weight rows, preserving signed cancellations. Every selected set has a proved original nonzero-output neuron whose actual induced graph has at most two components, including selected isolates. Graph degree-two capacity is proved by Hamiltonian-path encoding and two-component counting, not assumed.",
    "nonvacuity": "Literal exact MAX4 network at widths (2,1), with graph exactly two disjoint edges and degree one. Concrete controls cover a proper three-input selected set and the whole four-input set with empty complement.",
    "limitations": "No degree-two MAX_N existence construction for N>=6 is established by this receipt. Existing general caterpillar constructions can have higher-degree branches. The lower bound is an implication for the stated graph class; it is not an unrestricted exponential bound or an assertion of tightness or all-arity feasibility.",
    "attribution": "Formalizes the mathematical route in research/sN/trees/overnight_degree_two.md using the new elementary finite-difference obstruction and faithful raw-array bridges.",
    "reproduce": f"python3 {REL}/recheck.py --run",
}
(HERE / "receipt.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
print(f"PASS {len(after)} source/control hashes, {len(order)} research modules, {len(axioms)} standard-only axiom audits")
