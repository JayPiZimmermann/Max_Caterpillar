#!/usr/bin/env python3
"""Check an ordinary-network extension of a frozen verified dependency proof."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / "lakefile.lean").is_file())
REL = HERE.relative_to(ROOT)
BASELINE = ROOT / "research/sN/overnight_20261103/constants/tradeoff_theta/min_receipt.json"
POOL = ROOT / "research/sN/overnight_20261103/lean_pool.py"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
PREFIX = "MaxCaterpillar.CleanQuadratic.Ordinary."
CLAIMS = [PREFIX + name for name in [
    "explicit_quadratic_ge_one", "explicit_quadratic",
    "exists_uniform_quadratic_constant", "exists_quadratic_constant_for_scale",
    "Check.exact_explicit_type", "Check.exact_exists_type",
    "Check.exact_fixed_scale_type", "Check.withDormantBias_eval",
    "Check.actual_biased_max_three",
]]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def code_only(text):
    out = []
    i = depth = 0
    quoted = False
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
            i = len(text) if end == -1 else end
        elif text[i] == '"':
            quoted = True
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def closure():
    files = {}
    def visit(path):
        rel = str(path.relative_to(ROOT))
        if rel in files:
            return
        files[rel] = sha(path)
        for line in code_only(path.read_text()).splitlines():
            if not line.startswith("import "):
                continue
            for module in line.split()[1:]:
                dep = ROOT / (module.replace(".", "/") + ".lean")
                if dep.is_file():
                    visit(dep)
    visit(HERE / "Check.lean")
    return files


baseline = json.loads(BASELINE.read_text())
assert baseline["status"] == "PASS"
baseline_sources = baseline["source_files"]
for rel, expected in baseline_sources.items():
    assert sha(ROOT / rel) == expected, "Baseline drift: " + rel
for rel, expected in baseline["logs"].items():
    assert sha(ROOT / rel) == expected, "Baseline log drift: " + rel

before = closure()
new_sources = {str(REL / "Bounds.lean"), str(REL / "Check.lean")}
for rel, digest in before.items():
    if rel not in new_sources:
        assert baseline_sources.get(rel) == digest, "Unverified dependency: " + rel
    assert not re.search(r"\b(?:sorry|admit|native_decide|Lean\.ofReduceBool)\b|^\s*(?:axiom|unsafe)\b",
                         code_only((ROOT / rel).read_text()), re.M), rel

if "--run" in sys.argv:
    for leaf in ["Bounds", "Check"]:
        output = ROOT / ".lake/build/lib" / REL / (leaf + ".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        cmd = [sys.executable, str(POOL), "lake", "env", "lean", "-j1", "-o",
               str(output.relative_to(ROOT)), str(REL / (leaf + ".lean"))]
        with (HERE / (leaf.lower() + ".log")).open("w") as log:
            result = subprocess.run(cmd, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
        (HERE / (leaf.lower() + ".exit")).write_text(str(result.returncode) + "\n")
        assert result.returncode == 0, leaf + " failed"

logs = {}
audit_text = ""
for leaf in ["bounds", "check"]:
    assert (HERE / (leaf + ".exit")).read_text().strip() == "0", leaf
    for extension in ["log", "exit"]:
        path = HERE / (leaf + "." + extension)
        logs[str(path.relative_to(ROOT))] = sha(path)
    audit_text += (HERE / (leaf + ".log")).read_text() + "\n"
assert not re.search(r"\berror:", audit_text)
axioms = {}
for name in CLAIMS:
    match = re.search("'" + re.escape(name) + r"' depends on axioms: \[([^]]*)\]", audit_text, re.S)
    assert match, "Missing axiom audit: " + name
    found = sorted(x.strip() for x in match[1].split(",") if x.strip())
    assert set(found) <= ALLOWED, (name, found)
    axioms[name] = found
assert closure() == before, "Sources changed during extension check"
for path in [Path(__file__).resolve(), HERE / "README.md", HERE / "SEMANTIC_AUDIT.md", BASELINE, POOL,
             ROOT / "lean-toolchain", ROOT / "lakefile.lean", ROOT / "lake-manifest.json"]:
    before[str(path.relative_to(ROOT))] = sha(path)
receipt = {
    "status": "PASS",
    "state": "Lean-verified isolated extension of a source-unchanged verified baseline",
    "source_files": before,
    "source_count": len(before),
    "logs": logs,
    "headline_axioms": axioms,
    "baseline_receipt": str(BASELINE.relative_to(ROOT)),
    "baseline_source_count": len(baseline_sources),
    "baseline_sources_and_logs": "All hashes match",
    "forbidden_construct_scan": "PASS",
    "scope": "Ordinary sequential two-hidden-layer ReLU networks, arbitrary real weights and all biases, no skip connections. For every N>=3 and C>0, h1<=C*N^2 implies h2>=N^2/(175000*max(1,C)); one absolute positive constant and fixed-C existential corollaries.",
    "controls": "Independent literal six-array contracts; actual MAX3 network at C=1 with a first-hidden bias equal to one.",
    "limits": "Existence is currently proved from the explicit bound, not by an independently simplified paper argument. New modules rebuilt; old closure reused after source and receipt validation. Not imported into a frozen production root.",
    "reproduce": "python3 " + str(REL / "recheck.py") + " --run",
}
(HERE / "receipt.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
print("PASS", len(before), "source/control hashes;", len(axioms), "standard-only axiom audits")
