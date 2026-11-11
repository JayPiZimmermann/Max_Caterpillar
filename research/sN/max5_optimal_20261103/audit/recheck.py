"""Replay the MAX5 frontier's finite controls without editing frozen receipts.

This does not formalize the written mathematical model bridges.  It records
that distinction and pins the exact source artifacts used by this audit.
"""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    replay = HERE / "replay"
    replay.mkdir(exist_ok=True)
    sources = [
        "research/sN/frontierN/overnight_general_check.py",
        "research/sN/frontierN/overnight_general_flags.json",
        "research/sN/frontierN/overnight_general_six_check.py",
        "research/sN/frontierN/overnight_general_six_supports.json",
        "research/sN/frontierN/overnight_general_six_pairpeeling.json",
        "research/sN/frontierN/overnight_general_six_global.json",
    ]
    for name in sources:
        path = ROOT / name
        shutil.copyfile(path, replay / path.name)
        assert sha(path) == sha(replay / path.name)

    runs = []
    for name in ("overnight_general_check.py", "overnight_general_six_check.py"):
        with (replay / (name + ".log")).open("w") as log:
            run = subprocess.run([sys.executable, str(replay / name)],
                                 cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
        assert run.returncode == 0, name
        result = json.loads((replay / name.replace(".py", ".json")).read_text())
        runs.append({"name": name, "exit_code": run.returncode, "result": result})

    checker = ROOT / "research/sN/frontier5/max5_certificate_checker.py"
    constructions = [
        ("9_11", "research/sN/frontier5/max5_nine_c5_atoms_o2_r1.network.json"),
        ("10_6", "research/sN/best5/netB_10_6.json"),
    ]
    upper_runs = []
    for tag, name in constructions:
        output = HERE / ("upper_" + tag + ".json")
        with (HERE / ("upper_" + tag + ".log")).open("w") as log:
            run = subprocess.run([sys.executable, str(checker), str(ROOT / name),
                                  "--output", str(output)], cwd=ROOT,
                                 stdout=log, stderr=subprocess.STDOUT)
        assert run.returncode == 0, tag
        result = json.loads(output.read_text())
        assert result["status"] == "PASS"
        upper_runs.append({"network": name, "exit_code": run.returncode,
                           "result": result})
        sources.append(name)

    sources += [
        "research/sN/frontier5/max5_certificate_checker.py",
        "research/sN/frontierN/causal_intervention_certifier.py",
        "research/sN/frontierN/overnight_general.md",
        "research/sN/frontierN/overnight_general_six.md",
        "research/sN/frontierN/overnight_general_antipodal.lean",
        "research/sN/frontierN/overnight_general_antipodal.md",
        "research/sN/best5/overnight_fixed_natural8_rectangle.md",
        "research/sN/frontier5/construction_frontier.md",
        "research/sN/frontier5/max5_oct31_complete3_theorem.md",
        "research/sN/frontier5/max5_oct31_fiber_summary.md",
        "notes/max5_exact/README.md",
        "notes/max5_exact/first9_mixed.md",
        "notes/max5_exact/first9_nonroot.md",
        "notes/max5_exact/three_shared.md",
        "notes/max5_exact/four_shared.md",
        "notes/max5_exact/first9_c5_lower.md",
        "notes/max5_exact/root7_k4.md",
        "notes/max5_exact/width5_carriers.md",
    ]
    result = {
        "status": "PASS_FINITE_FRONTIER_CONTROLS",
        "scope": "Fresh exact finite classification replays and all-input rational upper constructions; written model bridges are not newly Lean checked.",
        "first_width_minimum": 9,
        "second_width_intervals": {"h1=9": [4, 11], "h1>=10": [4, 6]},
        "classification_replays": runs,
        "upper_replays": upper_runs,
        "sources": {name: sha(ROOT / name) for name in sources},
        "checker_sha256": sha(Path(__file__)),
    }
    (HERE / "recheck.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "source_count": len(sources),
                      "upper_pairs": [[r["result"]["h1"], r["result"]["h2"]]
                                      for r in upper_runs]}, indent=2))


if __name__ == "__main__":
    main()
