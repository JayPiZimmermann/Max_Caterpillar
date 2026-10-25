#!/usr/bin/env python3
"""Fresh isolated replay of the endpoint Q2 rational-relation certificate.

This rebuilds the exact residue dictionaries and ignores all saved DFS memos.
It is a replay of reviewed producers, not an independently implemented CAS.
"""
import gzip
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import time

HERE = Path(__file__).absolute().parent
ROOT = HERE.parents[2]
PYTHON = ROOT / "research/sN/dfs/h5-growth/venv/bin/python"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    started = time.monotonic()
    sources = [
        "overnight_uniform_q9_inventory.json",
        "overnight_uniform_endpoint_q2.json",
        "overnight_uniform_endpoint_q2_residue.py",
        "overnight_uniform_endpoint_q2_dfs.py",
        "overnight_uniform_endpoint_q2_coordinate.py",
        "overnight_uniform_endpoint_q2_constant.py",
    ]
    receipt = {"source_sha256": {name: digest(HERE / name) for name in sources},
               "checks": [], "scope": "Fresh producer replay without saved memo; mathematical bridges require the accompanying independent written review."}
    with tempfile.TemporaryDirectory(prefix="root-endpoint-q2-") as temp:
        work = Path(temp)
        for name in sources:
            shutil.copy2(HERE / name, work / name)
        for k in (2, 3, 4):
            for stage in ("residue", "dfs"):
                command = [str(PYTHON), str(work / f"overnight_uniform_endpoint_q2_{stage}.py"), str(k)]
                result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=180)
                logname = f"overnight_root_endpoint_q2_{stage}_{k}.log"
                (HERE / logname).write_text(result.stdout + result.stderr)
                assert result.returncode == 0, logname
                data = json.loads((work / f"overnight_uniform_endpoint_q2_{stage}_{k}.json").read_text())
                if stage == "residue":
                    cache = f"overnight_uniform_endpoint_q2_residue_{k}.fractions.json.gz"
                    with gzip.open(work / cache, "rt") as f:
                        actual = json.load(f)
                    with gzip.open(HERE / cache, "rt") as f:
                        expected = json.load(f)
                    assert actual == expected, cache
                    detail = {"records": len(actual["records"]), "exact_cache_matches": True}
                else:
                    assert data["zero"] is True
                    assert data["calls_this_phase"] > 0
                    detail = {"zero": True, "fresh_nodes": data["calls_this_phase"]}
                receipt["checks"].append({"cut_size": k, "stage": stage, **detail})
                print(json.dumps(receipt["checks"][-1]), flush=True)
        result = subprocess.run([str(PYTHON), str(work / "overnight_uniform_endpoint_q2_constant.py")],
                                cwd=ROOT, capture_output=True, text=True, timeout=60)
        (HERE / "overnight_root_endpoint_q2_constant.log").write_text(result.stdout + result.stderr)
        assert result.returncode == 0
        data = json.loads((work / "overnight_uniform_endpoint_q2_constant.json").read_text())
        assert data["zero"] is True and data["constant"] == "0"
        receipt["coordinate_constant"] = data
    assert all(digest(HERE / name) == value for name, value in receipt["source_sha256"].items())
    receipt.update(status="PASS", seconds=time.monotonic() - started)
    Path(__file__).with_suffix(".json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "seconds": receipt["seconds"]}), flush=True)


if __name__ == "__main__":
    main()
