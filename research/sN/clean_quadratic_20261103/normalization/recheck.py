#!/usr/bin/env python3
"""Check the exact anchor-localization declarations and bind their sources."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
LOGS = HERE / "logs"
LOGS.mkdir(exist_ok=True)
NAMESPACE = "MaxCaterpillar.CleanQuadratic.Normalization."
HEADLINES = [NAMESPACE + name for name in [
    "anchorLift_diag", "maximum_anchorLift", "lin_anchorLift",
    "sum_anchorRestrict", "anchorLocalize_computes_max",
    "anchorLocalize_normalized", "anchorLocalize_first_row",
    "exists_anchor_localized", "IndependentCheck.exact_step",
    "IndependentCheck.exact_sum", "IndependentCheck.exact_model",
    "IndependentCheck.canonical_base_control", "IndependentCheck.maxTwo_normalized",
    "IndependentCheck.maxTwo_exact", "IndependentCheck.maxTwo_restriction_realizable",
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
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            quoted = True
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def closure():
    files = {}
    research_order = []
    production_imports = set()

    def visit(path):
        relative = str(path.relative_to(ROOT))
        if relative in files:
            return
        files[relative] = sha(path)
        for line in code_only(path.read_text()).splitlines():
            if line.startswith("import "):
                for module in line.split()[1:]:
                    dep = ROOT / (module.replace(".", "/") + ".lean")
                    if dep.is_file():
                        if relative.startswith("research/") and module.startswith("MaxCaterpillar."):
                            production_imports.add(module)
                        visit(dep)
        if relative.startswith("research/"):
            research_order.append(relative)

    visit(HERE / "AnchorCheck.lean")
    return files, research_order, sorted(production_imports)


before, order, production = closure()
checks = [("project_imports", ["lake", "build", *production])]
for number, relative in enumerate(order):
    output = ROOT / ".lake/build/lib" / Path(relative).with_suffix(".olean")
    output.parent.mkdir(parents=True, exist_ok=True)
    checks.append((f"{number:02d}_{Path(relative).stem}",
        ["lake", "env", "lean", "-j1", "-o", str(output.relative_to(ROOT)), relative]))

if "--run" in sys.argv:
    for label, command in checks:
        with (LOGS / (label + ".log")).open("w") as log:
            run = subprocess.run([str(ROOT / "scripts/lean_lock.sh"), *command],
                cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
        (LOGS / (label + ".exit")).write_text(str(run.returncode) + "\n")
        if run.returncode:
            raise SystemExit("FAIL " + label)

logs = {}
combined = ""
for label, _ in checks:
    exit_path = LOGS / (label + ".exit")
    assert exit_path.read_text().strip() == "0", label
    log = LOGS / (label + ".log")
    logs[str(log.relative_to(ROOT))] = sha(log)
    logs[str(exit_path.relative_to(ROOT))] = sha(exit_path)
    combined += log.read_text() + "\n"

axioms = {}
for declaration in HEADLINES:
    matches = re.findall("'" + re.escape(declaration) +
        r"' depends on axioms: \[([^]]*)\]", combined, re.S)
    assert matches, declaration
    for match in matches:
        found = sorted(a.strip() for a in match.split(",") if a.strip())
        assert set(found) <= {"propext", "Classical.choice", "Quot.sound"}, (declaration, found)
        axioms[declaration] = found

for relative in before:
    assert not re.search(r"\b(?:sorry|admit|native_decide|Lean\.ofReduceBool)\b|^\s*(?:axiom|unsafe)\b",
        code_only((ROOT / relative).read_text()), re.M), relative
after, _, _ = closure()
assert before == after, "Source changed during verification"
for path in [Path(__file__).resolve(), HERE / "README.md", ROOT / "lean-toolchain",
             ROOT / "lakefile.lean", ROOT / "lake-manifest.json", ROOT / "scripts/lean_lock.sh"]:
    after[str(path.relative_to(ROOT))] = sha(path)

receipt = {
    "status": "PASS",
    "state": "Lean verified isolated research declarations; no production-facade import",
    "scope": "Exact same-index coordinate localization of normalized homogeneous MAX networks. The diagonal-preserving anchor lift eliminates the second diagonal normalization. Actual all-input MAX identity, coordinate-sum normalization, and whole-support first-row retention are derived; generic tied points are supplied internally.",
    "source_count": len(after),
    "source_files": after,
    "logs": logs,
    "headline_axioms": axioms,
    "forbidden_construct_scan": "PASS",
    "nonvacuity": "Independent literal expected types, the universal canonical tied point (selected coordinates zero, outside coordinates minus one), an exact normalized MAX2 network, and its actual one-coordinate localized MAX1 model.",
    "limits": "This receipt covers the anchor localization and its linear algebra, not the separate manuscript bias-limit proof, support averaging proof, ordinary linear bound, or the full quadratic lower bound.",
    "reproduce": "python3 " + str((HERE / "recheck.py").relative_to(ROOT)) + " --run",
}
(HERE / "receipt.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
print("PASS", len(after), "source/control hashes;", len(axioms), "standard-only axiom audits")
