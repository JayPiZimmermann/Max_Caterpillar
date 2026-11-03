#!/usr/bin/env python3
"""Replay the nonzero-curvature bridge without changing the frozen unit receipt."""
import argparse
import datetime
import importlib.util
import json
import re
import subprocess
import verify as unit

HERE, ROOT, REL = unit.HERE, unit.ROOT, unit.REL
CLAIMS = [
    'MaxCaterpillar.Max5Optimal.SegmentNetwork.exceptional_row_balanced_of_nonzero_mass',
    'MaxCaterpillar.Max5Optimal.SegmentNetwork.balance_or_zero_midpoint_mass',
]
COMMANDS = [('general_' + name if name != 'build' else 'general_unit', command)
            for name, command in unit.COMMANDS[:-1]] + [
    ('general_build', unit.lean_command(REL / 'SegmentNetworkGeneral.lean')),
    ('general_statements', ['lake', 'env', 'lean', str(REL / 'GeneralStatements.lean')]),
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
    output = (HERE / 'general_statements.log').read_text()
    claims = []
    for name in CLAIMS:
        match = re.search("'" + re.escape(name) + "' depends on axioms:\\s*\\[([^]]*)\\]", output, re.S)
        assert match, name
        axioms = sorted(x.strip() for x in match[1].split(',') if x.strip())
        assert set(axioms) <= unit.ALLOWED, (name, axioms)
        claims.append({'declaration': name, 'axioms': axioms})
    spec = importlib.util.spec_from_file_location('source_checks', ROOT / 'scripts/verify.py')
    checks = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checks)
    seen, external = set(), set()
    stack = [HERE / 'SegmentNetworkGeneral.lean', HERE / 'GeneralStatements.lean']
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
    paths |= {HERE / 'verify.py', HERE / 'verify_general.py'}
    result = {
        'status': 'LEAN_VERIFIED_TARGETED_DIRTY_TREE_RECEIPT',
        'checked_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'scope': 'Actual homogeneous shallow arrays, arbitrary nonzero signed midpoint masses, and guarded zero-mass clause; not a full Max5 support classification.',
        'claims': claims,
        'commands': [command for _, command in COMMANDS],
        'local_lean_import_closure_count': len(seen),
        'sources': {str(p.relative_to(ROOT)): unit.digest(p) for p in sorted(paths)},
        'external_imports_bound_by_lake_manifest': sorted(external),
        'logs': {name + '.log': unit.digest(HERE / (name + '.log')) for name, _ in COMMANDS},
    }
    (HERE / 'general_receipt.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'status': 'PASS', 'claims': len(claims), 'local_lean_files': len(seen)}))


if __name__ == '__main__':
    main()
