#!/usr/bin/env python3
"""Read-only receipt/hash checks, with optional Lean replay into .lake only."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--replay", action="store_true")
    args = parser.parse_args()
    manifest = json.loads((HERE / "manifest.json").read_text())
    for section in ("files", "existing_dependencies"):
        for name, expected in manifest[section].items():
            actual = digest(ROOT / name)
            if actual != expected:
                raise SystemExit("Hash mismatch: " + name)
    commands = []
    for name in manifest["receipts"]:
        receipt = json.loads((ROOT / name).read_text())
        for command in receipt["commands"]:
            if command not in commands:
                commands.append(command)
    seen_axioms = {}
    if args.replay:
        pool = ROOT / "research/sN/overnight_20261103/lean_pool.py"
        for command in commands:
            wrapped = command if any("lean_pool.py" in x for x in command[:2]) else [
                sys.executable, str(pool), *command]
            result = subprocess.run(wrapped, cwd=ROOT,
                                    text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT)
            if result.returncode:
                print(result.stdout)
                raise SystemExit("Lean command failed: " + " ".join(command))
            for declaration, body in re.findall(
                    r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", result.stdout):
                axioms = {x.strip() for x in body.split(",") if x.strip()}
                if not axioms <= ALLOWED_AXIOMS:
                    raise SystemExit("Unapproved axioms: " + declaration)
                seen_axioms[declaration] = sorted(axioms)
        # The exact consumer files are compiled above; require the
        # intended public declarations to appear in their axiom output.
        for declaration in manifest["declarations"]:
            if declaration not in seen_axioms:
                raise SystemExit("Missing axiom print: " + declaration)
    print(json.dumps({"status": "PASS", "new_files": len(manifest["files"]),
                      "existing_dependencies": len(manifest["existing_dependencies"]),
                      "lean_replayed": args.replay,
                      "declaration_axioms": seen_axioms}, sort_keys=True))


if __name__ == "__main__":
    main()
