#!/usr/bin/env python3
"""Rebuild and content-bind the raw-network original-neuron rank obstruction."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
REL = HERE.relative_to(ROOT)
LEAVES = ["DifferenceAlgebra", "ContrastSupport", "MaxTent", "MaxAnnihilator", "NoRidgeSum", "RankBridge", "ActualRank"]
DRIVER = REL / "ActualRankCheck.lean"
PREFIX = "MaxCaterpillar.ExponentialPush.Ridge."
HEADLINES = [
    PREFIX + "exists_active_original_second_highrank",
    PREFIX + "Check.raw_nine_array_highrank",
    "MaxCaterpillar.Frontier.maxThreeNet_eval",
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def code_only(text):
    result = []
    i, depth, quoted = 0, 0, False
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
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        elif text[i] == '"':
            quoted = True
            i += 1
        else:
            result.append(text[i])
            i += 1
    return "".join(result)


def closure():
    result = {}

    def visit(path):
        rel = str(path.relative_to(ROOT))
        if rel in result:
            return
        result[rel] = sha(path)
        for line in code_only(path.read_text()).splitlines():
            if line.startswith("import "):
                for name in line.split()[1:]:
                    dependency = ROOT / (name.replace(".", "/") + ".lean")
                    if dependency.is_file():
                        visit(dependency)

    visit(ROOT / DRIVER)
    for path in [Path(__file__).resolve(), ROOT / "lean-toolchain", ROOT / "lakefile.lean",
                 ROOT / "lake-manifest.json", ROOT / "scripts/lean_lock.sh"]:
        result[str(path.relative_to(ROOT))] = sha(path)
    return result


before = closure()
checks = [("project_imports", ["lake", "build", "MaxCaterpillar.Frontier.Basic",
                              "MaxCaterpillar.Frontier.StarCertificate.Anova",
                              "MaxCaterpillar.Frontier.RandomRestriction.AffineSkipExtension",
                              "MaxCaterpillar.Frontier.SecondWidthN",
                              "MaxCaterpillar.Frontier.Constructions"])]
for leaf in LEAVES:
    target = ROOT / ".lake/build/lib" / REL / (leaf + ".olean")
    target.parent.mkdir(parents=True, exist_ok=True)
    checks.append((leaf, ["lake", "env", "lean", "-j1", "-o", str(target),
                          str(REL / (leaf + ".lean"))]))
checks.append(("exact_type", ["lake", "env", "lean", "-j1", str(DRIVER)]))

if "--run" in sys.argv:
    for name, args in checks:
        log = HERE / ("actual_recheck_" + name + ".log")
        with log.open("w") as output:
            process = subprocess.run([str(ROOT / "scripts/lean_lock.sh"), *args],
                                     cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
        (HERE / ("actual_recheck_" + name + ".exit")).write_text(str(process.returncode) + "\n")
        if process.returncode:
            raise SystemExit(f"FAILED {name}; see {log.relative_to(ROOT)}")

logs = {}
for name, _ in checks:
    assert (HERE / ("actual_recheck_" + name + ".exit")).read_text().strip() == "0", name
    log = HERE / ("actual_recheck_" + name + ".log")
    logs[str(log.relative_to(ROOT))] = sha(log)

output = (HERE / "actual_recheck_exact_type.log").read_text()
axioms = {}
for declaration in HEADLINES:
    match = re.search("'" + re.escape(declaration) + r"' depends on axioms: \[([^]]*)\]",
                      output, re.S)
    assert match, declaration
    dependencies = sorted(x.strip() for x in match[1].split(",") if x.strip())
    assert set(dependencies) <= {"propext", "Classical.choice", "Quot.sound"}, dependencies
    axioms[declaration] = dependencies

for path in before:
    if not path.endswith(".lean"):
        continue
    code = code_only((ROOT / path).read_text())
    assert not re.search(r"\b(?:sorry|admit|native_decide|Lean\.ofReduceBool)\b|^\s*(?:axiom|unsafe)\b",
                         code, re.M), path

after = closure()
assert before == after, "Source/control changed during verification"
receipt = {
    "status": "PASS",
    "evidence_level": "Research-only exact Lean declarations; not a production-root integration",
    "driver": str(DRIVER),
    "source_files": after,
    "source_count": len(after),
    "logs": logs,
    "headline_axioms": axioms,
    "forbidden_construct_scan": "PASS",
    "scope": "For N>=3, every unrestricted real affine-skip/bias two-hidden-layer network computing actual MAX_N on every real input has an ORIGINAL second-neuron index k with nonzero output coefficient d_k and observation rank at least N-1. The observation is x -> (U_k dot x, (W_kj (A_j dot x))_j), so nonfeeding first rows vanish and no normalization or changed neuron indices are used.",
    "proof_route": "The common kernel of a rank<=N-2 linear observation contains a non-diagonal vector, by appending one coordinate and comparing dimensions. Such a vector is a period of the original biased neuron. First-hidden-layer output skips also have a non-diagonal period at N>=3; zero-output neurons are handled separately. The actual finite-sum maximum obstruction then gives a contradiction if every contributing original second neuron has rank<=N-2.",
    "boundary_controls": "The exact driver expands all nine primitive real arrays and the complete forward-pass formula. It also instantiates the theorem on the concrete exact MAX3 network maxThreeNet at widths (4,3), through the proved ofOrdinary affine-skip embedding.",
    "limitations": "This proves a per-neuron rank necessity, not a second-hidden-width bound or an exponential lower bound. It does not permit deleting arbitrary low-rank terms from a mixed representation. The range-rank observation is literal; a graph-component or sparse feeding-card corollary needs its separate bridge.",
    "reproduce": f"python3 {REL}/actual_rank_recheck.py --run",
}
destination = HERE / "actual_rank_receipt.json"
destination.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
print(f"PASS {len(after)} source/control hashes, {len(axioms)} standard-only axiom audits: {destination.relative_to(ROOT)}")
