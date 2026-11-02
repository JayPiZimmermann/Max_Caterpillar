#!/usr/bin/env python3
"""Two bounded slots for short, task-owned Lean diagnostics.

Heavy builds use scripts/lean_lock.sh; the three-claim regularity workers use
one separate priority lane. Never use this pool to write someone else's .olean.
"""
import fcntl
import os
import subprocess
import sys
import time

paths = ['/tmp/max_caterpillar_count65_small_lean.lock',
         '/tmp/max_caterpillar_count65_small_lean_2.lock']
if len(sys.argv) < 2:
    raise SystemExit('usage: lean_small_pool.py COMMAND [ARG ...]')
handles = [open(p, 'a') for p in paths]

def available():
    with open('/proc/meminfo') as f:
        for row in f:
            if row.startswith('MemAvailable:'):
                return int(row.split()[1]) * 1024
    return 0

while True:
    for slot, handle in enumerate(handles):
        if slot and available() < 10 * 1024**3:
            continue
        try:
            fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            continue
        try:
            child = subprocess.run(sys.argv[1:])
            raise SystemExit(child.returncode)
        finally:
            fcntl.flock(handle, fcntl.LOCK_UN)
    time.sleep(0.2)
