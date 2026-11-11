#!/usr/bin/env python3
"""Source-bound fully affine original-feeding-width tradeoff verification."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
MODULE = "MaxCaterpillar.Frontier.RandomRestriction.FeedingTransfer"
DRIVER = "verification/h2/AffineFeedingTradeoffCheck.lean"
PREFIX = "MaxCaterpillar.Frontier.RandomRestriction.FeedingCore."
HEADLINES = [PREFIX + n for n in [
    "absorb_eval", "exists_original_matching_of_feeding_braid",
    "structural_witness_of_generic_embedding_feeding", "model_counting_feeding_on_tail",
    "feedingCard_pos", "exists_feeding_half_model", "normalized_feeding_tradeoff",
    "normalized_feedingCard_le_original", "affine_feeding_tradeoff", "affine_feeding_quadratic"]]

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
checks = [("affine_feeding_build", ["lake", "build", MODULE]),
          ("affine_feeding_exact", ["lake", "env", "lean", "-j1", DRIVER])]


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
text = (HERE / "affine_feeding_exact.log").read_text()
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
    "scope": "The complete nine-array/scalar affine-skip model: arbitrary first and second biases, arbitrary input-to-second affine skips, first-to-output and input-to-output skips, output bias; exact MAX_N on every real input, N>=1040. Denominator is the ORIGINAL number h1prime of columns of the original W matrix with some nonzero entry. No total-first-width cap, normalized model, moment/support budget, coefficient certificate, genericity or probability/counting premise in the final theorem.",
    "bound": "h2 >= min(N^2,N^4/h1prime)/400000000",
    "quadratic_corollary": "h1prime<=N^2 implies h2>=N^2/400000000, with arbitrarily many additional output-only first neurons.",
    "nonvacuity": "Independent driver applies the stronger quadratic feeding theorem at N=1040 to the actual caterpillar construction embedded into the affine skip model, proves its actual feeding count <= firstWidth(1040) <= 1040^2, and retains its exact real-input MAX identity. Affine normalization's separate expanded-type gate also supplies nonzero-biased-skip and nonlinear MAX3 witnesses.",
    "proof_route": "Faithful affine-skip normalization with original indices and feeding lineage; actual five-variable obstruction with only feeding support restrictions via tagged empty-graph output-term absorption; original-neuron probability counted on the feeding-masked core; half averaging only over the feeding subtype; simultaneous actual moment/count/regularized budgets; original feeding-card monotonicity; closed scalar optimizer. Large feeding width uses the existing skip-safe free_neurons linear bound.",
    "reproduce": "python3 research/sN/jensen_bound/affine_feeding_recheck.py --run",
    "toolchain_sha256": sha(ROOT / "lean-toolchain")}
path = HERE / "affine_feeding_receipt.json"
path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
print(f"PASS {len(after)} source/toolchain hashes, {len(axioms)} standard-only axiom audits: {path.relative_to(ROOT)}")
