#!/usr/bin/env python3
"""Replay the arbitrary-pair bridge without changing earlier frozen receipts."""
import argparse
import datetime
import importlib.util
import json
import re
import subprocess
import verify as unit
import verify_general as general

HERE, ROOT, REL = unit.HERE, unit.ROOT, unit.REL
CLAIM = 'MaxCaterpillar.Max5Optimal.SegmentNetwork.balance_or_zero_pair_mass'
COMMANDS = [('pairs_' + name, command) for name, command in general.COMMANDS[:-1]] + [
    ('pairs_build', unit.lean_command(REL / 'SegmentNetworkPairs.lean')),
    ('pairs_statements', ['lake', 'env', 'lean', str(REL / 'PairStatements.lean')]),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--replay', action='store_true')
    args = parser.parse_args()
    if args.replay:
        for name, command in COMMANDS:
            if '-o' in command:
                (ROOT / command[command.index('-o') + 1]).parent.mkdir(parents=True, exist_ok=True)
            run = subprocess.run(['python3', 'research/sN/overnight_20261103/lean_pool.py'] + command,
                                 cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            (HERE / (name + '.log')).write_text(run.stdout)
            (HERE / (name + '.exit')).write_text(str(run.returncode) + '\n')
            if run.returncode:
                raise SystemExit(run.stdout)
    for name, _ in COMMANDS:
        assert (HERE / (name + '.exit')).read_text().strip() == '0', name
    output = (HERE / 'pairs_statements.log').read_text()
    match = re.search("'" + re.escape(CLAIM) + "' depends on axioms:\\s*\\[([^]]*)\\]", output, re.S)
    assert match, CLAIM
    axioms = sorted(x.strip() for x in match[1].split(',') if x.strip())
    assert set(axioms) <= unit.ALLOWED, axioms
    spec = importlib.util.spec_from_file_location('source_checks', ROOT / 'scripts/verify.py')
    checks = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checks)
    seen, external = set(), set()
    stack = [HERE / 'SegmentNetworkPairs.lean', HERE / 'PairStatements.lean']
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
                    if local.is_file(): stack.append(local)
                    else: external.add(module)
    paths = seen | {ROOT / p for p in ['lean-toolchain', 'lakefile.lean', 'lake-manifest.json']}
    paths |= {HERE / 'verify.py', HERE / 'verify_general.py', HERE / 'verify_pairs.py'}
    result = {
        'status': 'LEAN_VERIFIED_TARGETED_DIRTY_TREE_RECEIPT',
        'checked_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'scope': 'Actual homogeneous shallow arrays; guarded segment condition for every distinct pair of Max5 contact labels; not a full support classification.',
        'claims': [{'declaration': CLAIM, 'axioms': axioms}],
        'commands': [command for _, command in COMMANDS],
        'local_lean_import_closure_count': len(seen),
        'sources': {str(p.relative_to(ROOT)): unit.digest(p) for p in sorted(paths)},
        'external_imports_bound_by_lake_manifest': sorted(external),
        'logs': {name + '.log': unit.digest(HERE / (name + '.log')) for name, _ in COMMANDS},
    }
    (HERE / 'pairs_receipt.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'status': 'PASS', 'claims': 1, 'local_lean_files': len(seen)}))


if __name__ == '__main__':
    main()
