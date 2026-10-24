#!/usr/bin/env python3
"""Bounded single-thread subprocess launcher with durable log/exit receipt."""
import argparse
import datetime
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time

HERE = Path(__file__).parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('tag')
    parser.add_argument('--seconds', type=int, default=1200)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    assert command and args.tag.replace('_', '').isalnum()
    seconds = min(args.seconds, 1200)
    env = os.environ.copy()
    for name in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS', 'NUMEXPR_NUM_THREADS', 'FLINT_NUM_THREADS'):
        env[name] = '1'

    def limits():
        resource.setrlimit(resource.RLIMIT_AS, (3 * 1024 ** 3, 3 * 1024 ** 3))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

    log = HERE / f'overnight_upper_{args.tag}.log'
    exit_path = HERE / f'overnight_upper_{args.tag}_exit.json'
    start = time.monotonic()
    record = dict(command=command, started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  timeout_seconds=seconds, address_space_limit_bytes=3 * 1024 ** 3,
                  threads=1, log=log.name)
    with log.open('w') as output:
        process = subprocess.Popen(command, stdout=output, stderr=subprocess.STDOUT, env=env,
                                   preexec_fn=limits, start_new_session=True)
        try:
            returncode = process.wait(timeout=seconds)
            record.update(returncode=returncode, timed_out=False)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
            record.update(returncode=None, timed_out=True)
    record['elapsed_seconds'] = time.monotonic() - start
    record['finished_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    exit_path.write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps(record, indent=2), flush=True)


if __name__ == '__main__':
    main()
