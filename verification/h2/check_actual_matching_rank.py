#!/usr/bin/env python3
"""Fresh actual nonlinear-neuron conditional rank bridge and nonzero-edge witness."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

root = Path(__file__).resolve().parents[2]
os.chdir(root)
base = Path("MaxCaterpillar/Frontier/RandomRestriction")
sources = [base / name for name in ["ActualMatchingRow.lean", "ActualMatchingFlip.lean",
           "ActualMatchingCleanFlip.lean", "ActualMatchingRank.lean"]]
check = Path("verification/h2/ActualMatchingRankCheck.lean")
checks = [check, Path("verification/h2/ActualCleanSanityCheck.lean")]
out = Path("research/sN/jensen_bound")
allowed = {"propext", "Classical.choice", "Quot.sound"}
expected = {"MaxCaterpillar.Frontier.RandomRestriction." + name for name in [
    "actualMatchingRow_zero_iff", "actualMatchingRow_swap", "actualMatchingRow_fiber_flip",
    "actualClean_fiber_survival_fraction_le"]}
expected |= {"ActualMatchingRankCheck." + name for name in ["oneEdge_normalized", "oneEdge_weight"]}
expected |= {"ActualCleanSanityCheck.cancellation_example_not_clean"}

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def mirror_branch(original, overlay, branch):
    overlay.mkdir(parents=True, exist_ok=True)
    excluded = {p.stem + suffix for p in sources for suffix in [".olean", ".ilean"]}
    if original.is_dir():
        for child in original.iterdir():
            if branch and child.name == branch[0]:
                continue
            if not branch and child.name in excluded:
                continue
            (overlay / child.name).symlink_to(child.resolve(),
                                            target_is_directory=child.is_dir())
    if branch:
        mirror_branch(original / branch[0], overlay / branch[0], branch[1:])

receipt = {
    "sources": [{"path": str(p), "sha256": digest(p),
                 "role": "owned source"}
                for p in sources],
    "check": str(check), "check_sha256": digest(check),
    "producer": str(Path(__file__).resolve().relative_to(root)),
    "producer_sha256": digest(Path(__file__)), "integrated": False, "steps": []}
# Bind every project-source import, including separately verified frozen dependencies.
closure = {}
def visit(path):
    path = Path(path)
    if str(path) in closure:
        return
    closure[str(path)] = digest(path)
    for line in re.findall(r"^import ([^\n]+)", path.read_text(), re.M):
        for name in line.split():
            if name.startswith("MaxCaterpillar."):
                visit(Path(name.replace(".","/")+".lean"))
for source in sources+checks:
    visit(source)
receipt["project_source_closure"] = closure
receipt["freshly_rebuilt"] = [str(p) for p in sources]
receipt["independent_checks"] = {str(p):digest(p) for p in checks}
base_search = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"],
                                      text=True).strip()
lean = subprocess.check_output(["lake", "env", "which", "lean"], text=True).strip()
with tempfile.TemporaryDirectory(prefix="max_caterpillar_actual_matching_rank_") as directory:
    overlay = Path(directory)
    mirror_branch(root / ".lake/build/lib", overlay, base.parts)
    env = dict(os.environ, LEAN_PATH=str(overlay) + ":" + base_search)
    commands = [(p.stem, [lean, "-j1", "-o", str(overlay / p.with_suffix(".olean")), str(p)])
                for p in sources]
    commands.extend((p.stem, [lean, "-j1", str(p)]) for p in checks)
    for name, command in commands:
        log = out / ("actual_matching_rank_" + name + ".log")
        with log.open("w") as handle:
            result = subprocess.run(command, env=env, stdout=handle,
                                    stderr=subprocess.STDOUT)
        text = log.read_text()
        print(text, end="", flush=True)
        axioms = {declaration: [a.strip() for a in body.split(",") if a.strip()]
                  for declaration, body in re.findall(
                      r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)}
        receipt["steps"].append({"name": name, "command": command,
                                 "exit_code": result.returncode, "axioms": axioms,
                                 "log": str(log), "log_sha256": digest(log)})
        (out / ("actual_matching_rank_" + name + ".exit")).write_text(str(result.returncode) + "\n")
        if result.returncode:
            break
receipt["sources_unchanged"] = all(digest(Path(p["path"])) == p["sha256"]
                                    for p in receipt["sources"])
receipt["check_unchanged"] = digest(check) == receipt["check_sha256"]
receipt["allowed_axioms"] = sorted(allowed)
printed = set().union(*(set(step["axioms"]) for step in receipt["steps"]))
receipt["axiom_audit_passed"] = (
    expected <= printed and all(set(axioms) <= allowed
        for step in receipt["steps"] for axioms in step["axioms"].values()))
receipt["closure_unchanged"] = all(digest(Path(p))==h for p,h in closure.items())
receipt["owned_lexical_passed"] = all(not re.search(r"\b(?:sorry|admit|native_decide|axiom)\b", p.read_text()) for p in sources+checks)
receipt["checks_unchanged"] = all(digest(Path(p))==h for p,h in receipt["independent_checks"].items())
receipt["success"] = (receipt["closure_unchanged"] and receipt["checks_unchanged"] and receipt["owned_lexical_passed"] and len(receipt["steps"]) == len(sources)+len(checks) and
                      all(s["exit_code"] == 0 for s in receipt["steps"]) and
                      receipt["sources_unchanged"] and receipt["check_unchanged"] and
                      receipt["axiom_audit_passed"])
(out / "actual_matching_rank_receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
raise SystemExit(0 if receipt["success"] else 1)
