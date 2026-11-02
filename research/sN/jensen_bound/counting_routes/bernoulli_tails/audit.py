#!/usr/bin/env python3
"""Audit the scoped exact-type driver after the three dependency-ordered compiles."""
import hashlib
import json
import pathlib
import re
import runpy

HERE = pathlib.Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / "lakefile.lean").exists())
BASE = "MaxCaterpillar/Frontier/RandomRestriction/GrowingMatching/Bernoulli/"
NAMESPACE = "MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Bernoulli."
MODULES = [BASE + "Mgf.lean", BASE + "Tails.lean"]
uncomment = runpy.run_path(str(ROOT / "scripts/verify.py"))["uncomment"]
claims = []
for filename in MODULES:
    source = uncomment((ROOT / filename).read_text())
    assert not re.search(r"\b(sorry|admit|axiom|native_decide)\b", source), filename
    claims.extend(NAMESPACE + name for name in re.findall(r"\btheorem\s+(\w+)", source))
assert len(claims) == 9, claims
for name in ["mgf", "tails", "check"]:
    assert (HERE / (name + ".exit")).read_text().strip() == "0", name
output = (HERE / "check.log").read_text()
assert not re.search(r"\b(sorryAx|Lean.ofReduceBool|error:)\b", output)
allowed = {"propext", "Classical.choice", "Quot.sound"}
audits = []
for name in claims:
    match = re.search("'" + re.escape(name) + r"' depends on axioms:\s*\[([^]]*)\]", output, re.S)
    assert match, name
    axioms = sorted(a.strip() for a in match.group(1).split(",") if a.strip())
    assert set(axioms) <= allowed, (name, axioms)
    assert "@" + name.rsplit(".", 1)[1] + " :" in output or name.rsplit(".", 1)[1] + " :" in output
    audits.append({"declaration": name, "axioms": axioms})
paths = MODULES + [BASE + "Weight.lean", "lake-manifest.json", "lean-toolchain"]
paths += [str((HERE / f).relative_to(ROOT)) for f in ["Check.lean", "check.log", "audit.py"]]
receipt = {
    "evidence": "Diagnostic working-tree receipt; exact expected types are checked by Check.lean. No public-root integration or clean committed closure claimed.",
    "producer": "flock /tmp/max_caterpillar_count65_small_lean_1.lock: lake env lean -o <module.olean> <Mgf.lean>, then <Tails.lean>, then lake env lean <Check.lean>; python3 <this audit.py>",
    "claims": audits,
    "source_sha256": {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in paths},
}
(HERE / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
print("Scoped exact-type, axiom, and source audit passed for nine declarations.")
