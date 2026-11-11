#!/usr/bin/env python3
"""Rebuild and content-bind the exact maximum periodic-sum obstruction."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
REL = HERE.relative_to(ROOT)
LEAVES = ["DifferenceAlgebra", "ContrastSupport", "MaxTent", "MaxAnnihilator", "NoRidgeSum"]
DRIVER = REL / "NoRidgeSumCheck.lean"
PREFIX = "MaxCaterpillar.ExponentialPush.Ridge."
HEADLINES = [PREFIX + name for name in [
    "contrastBounded_periodic_eq_zero", "iterDiff_eq_zero_iff_of_contrastBounded",
    "maxCoordinateDifference_eq_tent", "iterDiff_maximum_ne_zero",
    "maximum_ne_affine_sum_of_exists_periods"]]


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
                              "MaxCaterpillar.Frontier.StarCertificate.Anova"])]
for leaf in LEAVES:
    target = ROOT / ".lake/build/lib" / REL / (leaf + ".olean")
    target.parent.mkdir(parents=True, exist_ok=True)
    checks.append((leaf, ["lake", "env", "lean", "-j1", "-o", str(target),
                          str(REL / (leaf + ".lean"))]))
checks.append(("exact_type", ["lake", "env", "lean", "-j1", str(DRIVER)]))

if "--run" in sys.argv:
    for name, args in checks:
        log = HERE / ("recheck_" + name + ".log")
        with log.open("w") as output:
            process = subprocess.run([str(ROOT / "scripts/lean_lock.sh"), *args],
                                     cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
        (HERE / ("recheck_" + name + ".exit")).write_text(str(process.returncode) + "\n")
        if process.returncode:
            raise SystemExit(f"FAILED {name}; see {log.relative_to(ROOT)}")

logs = {}
for name, _ in checks:
    assert (HERE / ("recheck_" + name + ".exit")).read_text().strip() == "0", name
    log = HERE / ("recheck_" + name + ".log")
    logs[str(log.relative_to(ROOT))] = sha(log)

output = (HERE / "recheck_exact_type.log").read_text()
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
    "scope": "For N>=2, actual MAX_N cannot equal an arbitrary additive affine function plus a finite sum of arbitrary real functions each having one period vector v with v_i != v_j for some i,j. No continuity, measurability, diagonal invariance, or invariance under all real multiples is assumed for the summands.",
    "core_identity": "The alternating coordinate-subset difference of MAX_N is (-1)^(N-1) max(0,1-max_i x_i+min_i x_i), nonzero at zero and supported where every absolute coordinate contrast is less than one.",
    "proof_route": "Finite differences commute and annihilate each periodic summand; two extra non-diagonal differences annihilate the affine remainder. The maximum-to-tent identity transfers this annihilation to a nonzero function with bounded coordinate-contrast support. Each non-diagonal difference is injective on that support class by an Archimedean periodicity argument.",
    "boundary_controls": "Exact driver derives NeZero N from N>=2, checks satisfiable single-summand hypotheses, shows MAX1 is affine, and constructs MAX3 minus one coordinate as a diagonal-periodic summand plus that affine coordinate. These controls show why the arity and non-diagonal restrictions matter.",
    "limitations": "This is not a second-hidden-width bound and does not establish a growing structural obstruction or exponential lower bound. The full-rank network corollary requires a separate linear-algebra and actual-model bridge. Low-rank terms cannot simply be deleted from a mixed representation.",
    "reproduce": f"python3 {REL}/recheck.py --run",
}
destination = HERE / "no_ridge_sum_receipt.json"
destination.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
print(f"PASS {len(after)} source/control hashes, {len(axioms)} standard-only axiom audits: {destination.relative_to(ROOT)}")
