#!/usr/bin/env python3
"""Content-bound diagnostic audit for the SupportBounds leaf and exact-type driver."""
import hashlib
import json
import pathlib
import re
import runpy

HERE = pathlib.Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / "lakefile.lean").exists())
BASE = "MaxCaterpillar/Frontier/RandomRestriction/GrowingMatching/Bernoulli/"
NAMESPACE = "MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli."
uncomment = runpy.run_path(str(ROOT / "scripts/verify.py"))["uncomment"]
source = uncomment((ROOT / (BASE + "SupportBounds.lean")).read_text())
assert not re.search(r"\b(sorry|admit|axiom|native_decide)\b", source)
claims = [NAMESPACE + name for name in re.findall(r"\btheorem\s+(\w+)", source)]
assert len(claims) == 5, claims
for name in ["support_bounds", "support_bounds_check"]:
    assert (HERE / (name + ".exit")).read_text().strip() == "0", name
output = (HERE / "support_bounds_check.log").read_text()
assert not re.search(r"\b(sorryAx|Lean.ofReduceBool|error:)\b", output)
allowed = {"propext", "Classical.choice", "Quot.sound"}
audits = []
for name in claims:
    match = re.search("'" + re.escape(name) + r"' depends on axioms:\s*\[([^]]*)\]", output, re.S)
    assert match, name
    axioms = sorted(a.strip() for a in match.group(1).split(",") if a.strip())
    assert set(axioms) <= allowed, (name, axioms)
    assert "@" + name.rsplit(".", 1)[1] + " :" in output
    audits.append({"declaration": name, "axioms": axioms})
paths = [BASE + name + ".lean" for name in ["Weight", "Association", "Support", "Mgf", "Tails", "SupportBounds"]]
paths += ["lake-manifest.json", "lean-toolchain"]
paths += [str((HERE / f).relative_to(ROOT)) for f in ["SupportBoundsCheck.lean", "support_bounds_check.log", "support_bounds_audit.py"]]
receipt = {
    "evidence": "Diagnostic working-tree receipt. Five exact expected types are checked by SupportBoundsCheck.lean; no public-root integration or clean committed closure claimed.",
    "producer": "flock /tmp/max_caterpillar_count65_small_lean_1.lock: lake env lean -o <SupportBounds.olean> <SupportBounds.lean>, then lake env lean <SupportBoundsCheck.lean>; python3 <this support_bounds_audit.py>",
    "claims": audits,
    "source_sha256": {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in paths},
}
(HERE / "support_bounds_receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
print("SupportBounds exact-type, axiom, and source audit passed for five declarations.")
