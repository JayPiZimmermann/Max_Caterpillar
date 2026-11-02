#!/usr/bin/env python3
"""Source-bound larger-cutoff quadratic total-width verification."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
MODULE = "MaxCaterpillar.Frontier.RandomRestriction.QuadraticCutoff"
DRIVER = "verification/h2/QuadraticCutoffCheck.lean"
PREFIX = "MaxCaterpillar.Frontier.RandomRestriction.QuadraticCutoff."
HEADLINES = [PREFIX + n for n in [
    "coverage", "envelope_le", "model_bound", "normalized_quadratic", "affine_quadratic"]] + [
    "MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.localMatchingObstruction_five_two",
    "MaxCaterpillar.Frontier.RandomRestriction.NormalizedTotalHalf.exists_model"]

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
checks = [("quadratic_cutoff_build", ["lake", "build", MODULE]),
          ("quadratic_cutoff_exact", ["lake", "env", "lean", "-j1", DRIVER])]


if "--run" in sys.argv:
    for name, args in checks:
        with (HERE / (name + ".log")).open("w") as output:
            runner = ([sys.executable, str(ROOT / "research/sN/zulip_three/lean_small_pool.py")]
                      if "--pool" in sys.argv else [str(ROOT / "scripts/lean_lock.sh")])
            process = subprocess.run([*runner, *args],
                                     cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
        (HERE / (name + ".exit")).write_text(str(process.returncode) + "\n")
        if process.returncode: raise SystemExit(f"FAILED {name}")
logs = {}
for name, _ in checks:
    assert (HERE / (name + ".exit")).read_text().strip() == "0", name
    logs[str((HERE / (name + ".log")).relative_to(ROOT))] = sha(HERE / (name + ".log"))
text = (HERE / "quadratic_cutoff_exact.log").read_text()
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
for control in ["lakefile.lean", "lake-manifest.json", "scripts/lean_lock.sh", "research/sN/zulip_three/lean_small_pool.py"]:
    after[control] = sha(ROOT / control)
receipt = {
    "status": "PASS", "module": MODULE, "driver": DRIVER,
    "source_files": after, "source_count": len(after), "logs": logs,
    "headline_axioms": axioms, "forbidden_construct_scan": "PASS",
    "scope": "The complete nine-array/scalar affine-skip model: arbitrary real weights, all first/second/output biases, input-to-second, first-to-output, and input-to-output skips. Exact MAX_N on every real input, N>=3, total first hidden width h1<=N^2. No structural H, moment, support, rank, count, genericity, or probability premise in the headline.",
    "bound": "h2 >= N^2/10000000",
    "comparison": "Four times the constant of FeedingSharp's quadratic feeding-width corollary, but this theorem bounds TOTAL first width rather than only feeding width. Forty times the original constant1/400000000. No exponent or tightness claim.",
    "nonvacuity": "Independent driver applies the theorem to actual caterpillar networks at N=3 and N=50001, on both sides of the small-dimension linear branch, proving their actual total first widths <=N^2 without evaluating huge Catalan second widths.",
    "proof_route": "Faithful arbitrary affine-skip normalization; actual simultaneous all-row half restriction with unchanged hidden indices; known closed H(5,2) applied to the fully proved finite growing-matching transfer; literal K=floor(m/25); actual coverage >=1/2 and exact envelope <=1600/K^2; larger-cutoff scalar assembly; skip-safe free_neurons linear bound for N<=50000.",
    "reproduce": "python3 research/sN/jensen_bound/quadratic_cutoff_recheck.py --run",
    "toolchain_sha256": sha(ROOT / "lean-toolchain")}
path = HERE / "quadratic_cutoff_receipt.json"
path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
print(f"PASS {len(after)} source/toolchain hashes, {len(axioms)} standard-only axiom audits: {path.relative_to(ROOT)}")
