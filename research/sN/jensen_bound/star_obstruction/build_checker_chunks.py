#!/usr/bin/env python3
"""Build generated checker chunks sequentially, releasing the lock each time.

Every chunk has an individual durable log/exit marker. Stop at the first
failure or declared wall-time limit; successful prior chunks are reusable.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "checker_chunks_generation.json"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--per-chunk-timeout", type=int, default=120)
    parser.add_argument("--max-wall-seconds", type=int, default=7200)
    parser.add_argument("--start", type=int, default=0)
    parser.add_argument("--limit", type=int)
    parser.add_argument("--stride", type=int, default=1)
    parser.add_argument("--lane", choices=("canonical", "priority"), default="canonical")
    parser.add_argument("--run-id", default="default")
    parser.add_argument("--no-assembly", action="store_true")
    parser.add_argument("--stop-before", type=int)
    parser.add_argument("--resume-status", type=Path, action="append", default=[])
    args = parser.parse_args()
    manifest = json.loads(MANIFEST.read_text())
    paths = [p for p in manifest["outputs"] if Path(p).stem.startswith("Chunk")]
    paths.sort()
    chosen = paths[args.start::args.stride]
    if args.stop_before is not None:
        chosen = [p for p in chosen if int(Path(p).stem.removeprefix("Chunk")) < args.stop_before]
    if args.limit is not None:
        chosen = chosen[:args.limit]
    started = time.monotonic()
    status = {"manifest_sha256": hashlib.sha256(MANIFEST.read_bytes()).hexdigest(),
              "per_chunk_timeout": args.per_chunk_timeout,
              "max_wall_seconds": args.max_wall_seconds, "completed": [], "status": "running"}
    status["lane"] = args.lane
    status["run_id"] = args.run_id
    status["reused"] = []
    prior = {}
    for source in args.resume_status:
        data = json.loads(source.read_text())
        if data["manifest_sha256"] != status["manifest_sha256"]:
            raise SystemExit("Resume status belongs to a different generated manifest: " + str(source))
        for record in data["completed"] + data.get("reused", []):
            if record["exit"] == 0:
                prior[record["module"]] = {**record, "resumed_from": str(source)}
    status_path = HERE / f"checker_chunks_build_status_{args.run_id}.json"
    lock = ([str(ROOT / "scripts/lean_lock.sh")] if args.lane == "canonical" else
            ["flock", "/tmp/max_caterpillar_zulip_three_lean.lock"])
    for index, path in enumerate(chosen):
        if time.monotonic() - started > args.max_wall_seconds:
            status["status"] = "wall_limit"
            status_path.write_text(json.dumps(status, indent=2) + "\n")
            raise SystemExit(124)
        actual = hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
        if actual != manifest["outputs"][path]:
            raise SystemExit(f"Changed generated source: {path}")
        stem = Path(path).stem
        module = path[:-5].replace("/", ".")
        if module in prior:
            artifact = ROOT / ".lake/build/lib" / path.replace(".lean", ".olean")
            if not artifact.is_file():
                raise SystemExit("Missing previously checked artifact: " + str(artifact))
            status["reused"].append(prior[module])
            status_path.write_text(json.dumps(status, indent=2) + "\n")
            continue
        log = HERE / "checker_chunk_logs" / (stem + ".log")
        log.parent.mkdir(exist_ok=True)
        command = lock + ["timeout", str(args.per_chunk_timeout) + "s",
                   "/usr/bin/time", "-f", "elapsed=%e rss_kib=%M", "lake", "build", module]
        before = time.monotonic()
        with log.open("w") as output:
            result = subprocess.run(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
        log.with_suffix(".exit").write_text(str(result.returncode) + "\n")
        record = {"module": module, "exit": result.returncode,
                  "elapsed_including_lock_seconds": round(time.monotonic() - before, 3),
                  "log": str(log.relative_to(ROOT))}
        status["completed"].append(record)
        status["elapsed_seconds"] = round(time.monotonic() - started, 3)
        status_path.write_text(json.dumps(status, indent=2) + "\n")
        print(json.dumps(record), flush=True)
        if result.returncode:
            status["status"] = "failed"
            status_path.write_text(json.dumps(status, indent=2) + "\n")
            raise SystemExit(result.returncode)
    if not args.no_assembly and args.limit is None and args.stride == 1 and manifest["full_tree_assembly_emitted"]:
        log = HERE / "checker_full_assembly_build.log"
        module = "MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.Full"
        with log.open("w") as output:
            result = subprocess.run([str(ROOT / "scripts/lean_lock.sh"), "timeout", "300s",
                                     "/usr/bin/time", "-f", "elapsed=%e rss_kib=%M", "lake", "build", module],
                                    cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
        log.with_suffix(".exit").write_text(str(result.returncode) + "\n")
        status["assembly_exit"] = result.returncode
        if result.returncode:
            status["status"] = "assembly_failed"
            status_path.write_text(json.dumps(status, indent=2) + "\n")
            raise SystemExit(result.returncode)
    status["status"] = "complete"
    status_path.write_text(json.dumps(status, indent=2) + "\n")


if __name__ == "__main__":
    main()
