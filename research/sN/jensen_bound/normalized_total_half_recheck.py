#!/usr/bin/env python3
"""Rebuild and bind the normalized total-width half-restriction contract."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
MODULE = "MaxCaterpillar.Frontier.RandomRestriction.NormalizedTotalHalf"
DRIVER = "verification/h2/NormalizedTotalHalfCheck.lean"
DECLARATION = MODULE + ".exists_model"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def closure():
    found = {}

    def visit(path):
        name = str(path.relative_to(ROOT))
        if name in found:
            return
        found[name] = sha(path)
        for line in path.read_text().splitlines():
            if line.startswith("import "):
                for module in line.split()[1:]:
                    dependency = ROOT / (module.replace(".", "/") + ".lean")
                    if dependency.is_file():
                        visit(dependency)

    visit(ROOT / DRIVER)
    for control in ["lean-toolchain", "lakefile.lean", "lake-manifest.json",
                    "scripts/lean_lock.sh", "research/sN/zulip_three/lean_small_pool.py",
                    str(Path(__file__).resolve().relative_to(ROOT))]:
        found[control] = sha(ROOT / control)
    return found


before = closure()
commands = [
    ("normalized_total_half_build", ["lake", "build", MODULE]),
    ("normalized_total_half_exact", ["lake", "env", "lean", "-j1", DRIVER]),
]
runner = ([sys.executable, str(ROOT / "research/sN/zulip_three/lean_small_pool.py")]
          if "--pool" in sys.argv else [str(ROOT / "scripts/lean_lock.sh")])
if "--run" in sys.argv:
    for name, args in commands:
        with (HERE / (name + ".log")).open("w") as output:
            result = subprocess.run([*runner, *args], cwd=ROOT,
                                    stdout=output, stderr=subprocess.STDOUT)
        (HERE / (name + ".exit")).write_text(str(result.returncode) + "\n")
        if result.returncode:
            raise SystemExit(f"FAILED {name}")

logs = {}
for name, _ in commands:
    assert (HERE / (name + ".exit")).read_text().strip() == "0", name
    logs[str((HERE / (name + ".log")).relative_to(ROOT))] = sha(HERE / (name + ".log"))
output = (HERE / "normalized_total_half_exact.log").read_text()
match = re.search("'" + re.escape(DECLARATION) + r"' depends on axioms: \[([^]]*)\]", output, re.S)
assert match, DECLARATION
axioms = sorted(part.strip() for part in match[1].split(",") if part.strip())
assert set(axioms) <= {"propext", "Classical.choice", "Quot.sound"}, axioms
assert before == closure(), "Source changed during verification"
receipt = {
    "status": "PASS", "module": MODULE, "driver": DRIVER,
    "source_files": before, "source_count": len(before), "logs": logs,
    "axioms": {DECLARATION: axioms},
    "scope": "Actual normalized all-real-input MAX network, arbitrary affine homogeneous skips, positive selected arity n with 2n<=N; same original first and second index types; one selected set and actual normalized restricted MAX_n model obey 4*fourthMoment<=81*h1 and 4*nonBraidCount<=h1, counting ALL first rows.",
    "nonvacuity": "Independent checker applies the theorem to the actual normalized caterpillar MAX4 construction and obtains an exact MAX2 model with both budgets and unchanged hidden index types.",
    "commands": [args for _, args in commands],
    "reproduce": "python3 research/sN/jensen_bound/normalized_total_half_recheck.py --run",
}
(HERE / "normalized_total_half_receipt.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
print(f"PASS {len(before)} current source/control hashes; exact type, witness, standard axioms")
