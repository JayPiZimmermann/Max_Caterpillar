#!/usr/bin/env python3
"""Check the bounded triple-contact artifact; --replay reruns its Lean commands."""
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
NAMES = [
    'MaxCaterpillar.Max5Optimal.TripleContact.exists_zero_core_at_top_tie',
    'MaxCaterpillar.Max5Optimal.TripleContact.max5_pair_contact',
    'MaxCaterpillar.Max5Optimal.TripleContact.max5_weighted_pair_contact',
]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
COMMANDS = [
    ('dependency', ['lake', 'build', 'MaxCaterpillar.Frontier.Basic']),
    ('build', ['lake', 'env', 'lean', '-o',
               str(pathlib.Path('.lake/build/lib') / REL / 'TripleContact.olean'),
               str(REL / 'TripleContact.lean')]),
    ('statements', ['lake', 'env', 'lean', str(REL / 'Statements.lean')]),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--replay', action='store_true')
    args = parser.parse_args()
    if args.replay:
        (ROOT / '.lake/build/lib' / REL).mkdir(parents=True, exist_ok=True)
        for name, command in COMMANDS:
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
    for name in NAMES:
        match = re.search("'" + re.escape(name) + "' depends on axioms:\\s*\\[([^]]*)\\]", output, re.S)
        assert match, name
        axioms = sorted(x.strip() for x in match[1].split(',') if x.strip())
        assert set(axioms) <= ALLOWED, (name, axioms)
        claims.append({'declaration': name, 'axioms': axioms, 'status': 'EXACT_TYPE_AND_AXIOMS_CHECKED'})
    spec = importlib.util.spec_from_file_location('source_checks', ROOT / 'scripts/verify.py')
    checks = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checks)
    seen = set()
    stack = [HERE / 'TripleContact.lean', HERE / 'Statements.lean']
    external_imports = set()
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
                        external_imports.add(module)
    source_paths = seen | {ROOT / x for x in ['lean-toolchain', 'lakefile.lean', 'lake-manifest.json']}
    source_paths.add(HERE / 'verify.py')
    sources = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
               for p in sorted(source_paths)}
    receipt = {
        'status': 'LEAN_VERIFIED_TARGETED_DIRTY_TREE_RECEIPT',
        'checked_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'scope': 'Target module and exact-type consumer; not an integrated or public full-project gate.',
        'commands': [cmd for _, cmd in COMMANDS],
        'claims': claims,
        'local_lean_import_closure_count': len(seen),
        'source_files': sources,
        'external_imports_bound_by_lake_manifest': sorted(external_imports),
        'logs': {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                 for p in [HERE / 'build.log', HERE / 'dependency.log', HERE / 'statements.log']},
    }
    (HERE / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print('PASS: 3 exact theorem types; permitted axioms; ' + str(len(seen)) + ' local Lean source files.')


if __name__ == '__main__':
    main()
