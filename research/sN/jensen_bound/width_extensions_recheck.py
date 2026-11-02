#!/usr/bin/env python3
"""Source-bound feeding-width and full affine-skip extension gate; --run rebuilds."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
MODULE = "MaxCaterpillar.Frontier.RandomRestriction.AffineSkipExtension"
DRIVER = "verification/h2/WidthExtensionsCheck.lean"
BASE = "MaxCaterpillar.Frontier.RandomRestriction."
HEADLINES = [BASE + n for n in [
    "FeedingWidthExtension.prune_eval", "FeedingWidthExtension.second_width_tradeoff_feeding",
    "FeedingWidthExtension.second_width_quadratic_feeding", "AffineSkipExtension.encode_eval",
    "AffineSkipExtension.second_width_tradeoff_affine_skips",
    "AffineSkipExtension.second_width_tradeoff_affine_skips_unshifted"]]

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
checks = [
    ("feeding_width_extension", ["lake", "build", "MaxCaterpillar.Frontier.RandomRestriction.FeedingWidthExtension"]),
    ("affine_skip_extension", ["lake", "build", MODULE]),
    ("width_extensions_exact", ["lake", "env", "lean", "-j1", DRIVER])]


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
text = (HERE / "width_extensions_exact.log").read_text()
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
    "scope": "Two distinct extensions, N>=1040 and exact MAX on all real inputs: ordinary arbitrary-bias networks charged only their first-to-second feeding neurons; fully affine skip networks charged their total first width. The latter allows arbitrary first and second biases, arbitrary input-to-second affine skips, first-to-output and input-to-output skips, and output bias. No normalized-model, support, certificate or counting premise.",
    "bound": "Ordinary: h2 >= min(N^2,N^4/feedingCount)/400000000. Affine skips: h2 >= min(N^2,N^4/h1)/1600000000. Sharper shifted skip bound also checked: h2+2 >= min(N^2,N^4/(h1+2N))/400000000.",
    "quadratic_corollary": "Ordinary feedingCount<=N^2 implies h2>=N^2/400000000; unrestricted nonfeeding first neurons are irrelevant and are literally pruned.",
    "nonvacuity": "Independent checker embeds the actual N=1040 ordinary caterpillar construction into the affine skip model, proves its all-real exactness, and applies the unshifted skip theorem. The contract also expands all nine primitive affine-skip parameter arrays/scalars and the feeding-neuron subtype cardinality.",
    "proof_route": "Feeding extension literally prunes ordinary first neurons with zero W2 column, preserving every original bias and h2. Affine-skip extension exactly encodes arbitrary skips into an ordinary network of widths (h1+2N,h2+2), then applies the frozen closed theorem. Existing ordinary first/second width bounds absorb both shifts at factor-four constant cost.",
    "reproduce": "python3 research/sN/jensen_bound/width_extensions_recheck.py --run",
    "toolchain_sha256": sha(ROOT / "lean-toolchain")}
path = HERE / "width_extensions_receipt.json"
path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
print(f"PASS {len(after)} source/toolchain hashes, {len(axioms)} standard-only axiom audits: {path.relative_to(ROOT)}")
