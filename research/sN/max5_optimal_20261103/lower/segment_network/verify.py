#!/usr/bin/env python3
"""Content-bound checks for the actual-array segment bridge; --replay reruns Lean."""
import argparse
import datetime
import hashlib
import importlib.util
import json
import pathlib
import re
import subprocess

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[4]
REL = HERE.relative_to(ROOT)
BASE = pathlib.Path('research/sN/max5_optimal_20261103/lower')
CLAIMS = [
    'MaxCaterpillar.Max5Optimal.SegmentNetwork.exceptional_row_balanced',
    'MaxCaterpillar.Max5Optimal.SegmentNetwork.no_three_coordinate_exception',
]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def lean_command(path):
    return ['lake', 'env', 'lean', '-o',
            str(pathlib.Path('.lake/build/lib') / path.with_suffix('.olean')), str(path)]


COMMANDS = [
    ('dependency', ['lake', 'build', 'MaxCaterpillar.Frontier.Basic']),
    ('triple_contact', lean_command(BASE / 'triple_contact/TripleContact.lean')),
    ('segment_scalar', lean_command(BASE / 'width4_geometry/SegmentScalar.lean')),
    ('segment_balance', lean_command(BASE / 'width4_geometry/SegmentBalance.lean')),
    ('build', lean_command(REL / 'SegmentNetwork.lean')),
    ('statements', ['lake', 'env', 'lean', str(REL / 'Statements.lean')]),
]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--replay', action='store_true')
    args = parser.parse_args()
    if args.replay:
        for name, command in COMMANDS:
            if '-o' in command:
                (ROOT / command[command.index('-o') + 1]).parent.mkdir(parents=True, exist_ok=True)
            run = subprocess.run(['python3', 'research/sN/overnight_20261103/lean_pool.py'] + command,
                                 cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT)
            (HERE / (name + '.log')).write_text(run.stdout)
            (HERE / (name + '.exit')).write_text(str(run.returncode) + '\n')
            if run.returncode:
                raise SystemExit(run.stdout)
    for name, _ in COMMANDS:
        assert (HERE / (name + '.exit')).read_text().strip() == '0', name
    output = (HERE / 'statements.log').read_text()
    claims = []
    for name in CLAIMS:
        match = re.search("'" + re.escape(name) + "' depends on axioms:\\s*\\[([^]]*)\\]", output, re.S)
        assert match, name
        axioms = sorted(x.strip() for x in match[1].split(',') if x.strip())
        assert set(axioms) <= ALLOWED, (name, axioms)
        claims.append({'declaration': name, 'axioms': axioms})
    spec = importlib.util.spec_from_file_location('source_checks', ROOT / 'scripts/verify.py')
    checks = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checks)
    seen, external = set(), set()
    stack = [HERE / 'SegmentNetwork.lean', HERE / 'Statements.lean']
    while stack:
        path = stack.pop()
        if path in seen:
            continue
        seen.add(path)
        code = checks.uncomment(path.read_text())
        assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', code), path
        for line in code.splitlines():
            if line.startswith('import '):
                for module in line.split()[1:]:
                    local = ROOT / (module.replace('.', '/') + '.lean')
                    if local.is_file():
                        stack.append(local)
                    else:
                        external.add(module)
    paths = seen | {ROOT / p for p in ['lean-toolchain', 'lakefile.lean', 'lake-manifest.json']}
    paths.add(HERE / 'verify.py')
    receipt = {
        'status': 'LEAN_VERIFIED_TARGETED_DIRTY_TREE_RECEIPT',
        'checked_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'scope': 'Actual homogeneous shallow-array segment bridge and support-three exclusion; not the full Max5 support classification.',
        'claims': claims,
        'commands': [command for _, command in COMMANDS],
        'local_lean_import_closure_count': len(seen),
        'sources': {str(p.relative_to(ROOT)): digest(p) for p in sorted(paths)},
        'external_imports_bound_by_lake_manifest': sorted(external),
        'logs': {name + '.log': digest(HERE / (name + '.log')) for name, _ in COMMANDS},
    }
    (HERE / 'receipt.json').write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'status': 'PASS', 'claims': len(claims), 'local_lean_files': len(seen)}))


if __name__ == '__main__':
    main()
