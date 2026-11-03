#!/usr/bin/env python3
"""Four bounded slots for short, owned overnight Lean diagnostics.

The first two lock names are shared with the existing two-slot pool. This
does not permit concurrent writers to the same artifact. Heavy sequential
closure builds continue to use scripts/lean_lock.sh.
"""
import fcntl
import subprocess
import sys
import time

LOCKS = [
    "/tmp/max_caterpillar_count65_small_lean.lock",
    "/tmp/max_caterpillar_count65_small_lean_2.lock",
    "/tmp/max_caterpillar_overnight_lean_3.lock",
    "/tmp/max_caterpillar_overnight_lean_4.lock",
]


def available_bytes():
    with open("/proc/meminfo", encoding="ascii") as handle:
        for line in handle:
            if line.startswith("MemAvailable:"):
                return int(line.split()[1]) * 1024
    return 0


def main():
    if len(sys.argv) < 2:
        raise SystemExit("usage: lean_pool.py COMMAND [ARG ...]")
    handles = [open(path, "a", encoding="ascii") for path in LOCKS]
    while True:
        for slot, handle in enumerate(handles):
            required = (0, 10, 14, 14)[slot] * 1024**3
            if available_bytes() < required:
                continue
            try:
                fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                continue
            try:
                result = subprocess.run(sys.argv[1:], check=False)
                return result.returncode
            finally:
                fcntl.flock(handle, fcntl.LOCK_UN)
        time.sleep(0.2)


if __name__ == "__main__":
    raise SystemExit(main())
