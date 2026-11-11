"""Produce and independently replay the one-shared-contact SMT refutations.

This audits arithmetic unsatisfiability only, not the network-to-model bridge.
The normalization expands Z3 cardinality syntax and removes neutral unary
operators. Both transformations preserve the formula exactly.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import itertools
import json
import re
import subprocess
import sys
import tempfile
import time
import zipfile

HERE = Path(__file__).resolve().parent
BEST = HERE.parent / 'best5'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def parse(raw):
    stack = []
    roots = []
    for token in re.findall(r'\(|\)|[^\s()]+', re.sub(r';[^\n]*', '', raw)):
        if token == '(':
            stack.append([])
        elif token == ')':
            row = stack.pop()
            (stack[-1] if stack else roots).append(row)
        else:
            assert stack
            stack[-1].append(token)
    assert not stack
    return roots


def render(node):
    return '(' + ' '.join(map(render, node)) + ')' if isinstance(node, list) else node


def normalize(raw):
    counts = {'neutral_unary': 0, 'at_least': 0}

    def visit(node):
        if not isinstance(node, list):
            return node
        node = [visit(x) for x in node]
        if len(node) == 2 and isinstance(node[0], str) and node[0] in ('+', '*', 'and', 'or'):
            counts['neutral_unary'] += 1
            return node[1]
        if node and isinstance(node[0], list) and node[0][:2] == ['_', 'at-least']:
            assert len(node[0]) == 3
            k = int(node[0][2])
            args = node[1:]
            assert 0 <= k <= len(args)
            counts['at_least'] += 1
            if k == 0:
                return 'true'
            clauses = [['and', *subset] for subset in itertools.combinations(args, k)]
            return ['or', *clauses]
        if node and isinstance(node[0], list) and node[0][:2] == ['_', 'pbeq']:
            threshold, *weights = node[0][2:]
            assert len(weights) == len(node) - 1
            counts['pbeq'] = counts.get('pbeq', 0) + 1
            summands = [['*', w, ['ite', arg, '1', '0']]
                        for w, arg in zip(weights, node[1:])]
            return ['=', ['+', *summands], threshold]
        return node

    trees = [visit(node) for node in parse(raw)]
    trees = [node for node in trees if node[:1] != ['set-logic']]
    return '(set-logic ALL)\n' + '\n'.join(render(node) for node in trees) + '\n', counts


def normalization_control():
    # Independent truth table of each possible cardinality threshold at arity 5.
    for k in range(6):
        for bits in itertools.product([False, True], repeat=5):
            expanded = any(all(bits[j] for j in subset)
                           for subset in itertools.combinations(range(5), k))
            assert expanded == (sum(bits) >= k)


def produce(source, budget):
    sys.path.insert(0, '/tmp/max5_first11_cvc5')
    import cvc5
    normalization_control()
    raw = source.read_text()
    normalized, counts = normalize(raw)
    stem = source.with_name(source.stem + '_audit')
    normalized_path = stem.with_suffix('.smt2')
    normalized_path.write_text(normalized)
    solver = cvc5.Solver()
    for k, v in [('produce-proofs', 'true'), ('check-proofs', 'true'),
                 ('proof-format-mode', 'cpc'), ('tlimit-per', str(budget * 1000))]:
        solver.setOption(k, v)
    parser = cvc5.InputParser(solver)
    parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, normalized, str(normalized_path))
    sm = parser.getSymbolManager()
    while True:
        cmd = parser.nextCommand()
        if cmd.isNull():
            break
        if not str(cmd).startswith('(check-sat'):
            cmd.invoke(solver, sm)
    start = time.monotonic()
    print('PARSED', source.name, len(solver.getAssertions()), flush=True)
    result = solver.checkSat()
    version = solver.getVersion()
    if isinstance(version, bytes):
        version = version.decode()
    out = dict(status=str(result), seconds=time.monotonic()-start, budget=budget,
               original_source=source.name, original_source_sha256=sha(source),
               normalized_source=normalized_path.name,
               normalized_source_sha256=sha(normalized_path), normalization=counts,
               cvc5_version=version, assertions=len(solver.getAssertions()),
               audit_script_sha256=sha(__file__))
    print('RESULT', str(result), out['seconds'], flush=True)
    if result.isUnsat():
        proofs = solver.getProof()
        parts = [solver.proofToString(p) for p in proofs]
        text = '\n'.join(p.decode() if isinstance(p, bytes) else p for p in parts) + '\n'
        proof = stem.with_suffix('.proof.cpc')
        proof.write_text(text)
        out.update(proof=proof.name, proof_sha256=sha(proof),
                   proof_bytes=proof.stat().st_size, proof_roots=len(proofs),
                   trust_rule_present=':rule trust' in text)
    elif result.isUnknown():
        out['unknown_explanation'] = str(result.getUnknownExplanation())
    stem.with_suffix('.cvc5.json').write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps(out), flush=True)


def replay(source, budget):
    stem = source.with_name(source.stem + '_audit')
    receipt = json.loads(stem.with_suffix('.cvc5.json').read_text())
    assert receipt['status'] == 'unsat'
    assert receipt['proof_roots'] == 1 and not receipt['trust_rule_present']
    assert sha(source) == receipt['original_source_sha256']
    normalized, counts = normalize(source.read_text())
    assert counts == receipt['normalization']
    normalized_path = HERE / receipt['normalized_source']
    assert normalized_path.read_text() == normalized
    assert sha(normalized_path) == receipt['normalized_source_sha256']
    proof_path = HERE / receipt['proof']
    assert sha(proof_path) == receipt['proof_sha256']
    proof = proof_path.read_text().strip()
    assert ':rule trust' not in proof and proof.startswith('(') and proof.endswith(')')
    dep_path = BEST / 'overnight_root_complete_ethos_manifest.json'
    dependency = json.loads(dep_path.read_text())
    spec = importlib.util.spec_from_file_location('ethos_support', BEST / 'overnight_root_complete_ethos_verify.py')
    support = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(support)
    cache = Path(tempfile.gettempdir()) / 'max_caterpillar_ethos_025'
    cache.mkdir(exist_ok=True)
    archive = cache / 'ethos.zip'
    support.fetch(archive, dependency['checker_url'], dependency['checker_archive_sha256'])
    checker = cache / 'ethos'
    if not checker.exists():
        with zipfile.ZipFile(archive) as zipped:
            names = [n for n in zipped.namelist() if Path(n).name == 'ethos']
            assert len(names) == 1
            data = zipped.read(names[0])
            assert hashlib.sha256(data).hexdigest() == dependency['checker_binary_sha256']
            checker.write_bytes(data)
            checker.chmod(0o755)
    support.read_checked(checker, dependency['checker_binary_sha256'])
    for row in dependency['signatures']:
        support.fetch(cache / 'cpc' / row['path'], row['url'], row['sha256'])
    with tempfile.TemporaryDirectory(prefix='max5_one_shared_ethos_') as tmp:
        pr = Path(tmp) / 'proof.cpc'
        pr.write_text(proof[1:-1] + '\n')
        cmd = [str(checker), '--include=' + str(cache / 'cpc/Cpc.eo'),
               '--reference=' + str(normalized_path), '--require-proof-of-false', str(pr)]
        start = time.monotonic()
        result = subprocess.run(cmd, text=True, capture_output=True, timeout=budget)
        duration = time.monotonic() - start
        stem.with_suffix('.ethos.log').write_text(result.stdout + result.stderr)
        assert result.returncode == 0 and result.stdout.strip() == 'correct', (result.returncode, result.stdout, result.stderr)
    out = dict(status='INDEPENDENT_ETHOS_PASS', seconds=duration,
               original_source=source.name, original_source_sha256=sha(source),
               normalized_source_sha256=sha(normalized_path), proof_sha256=sha(proof_path),
               checker_binary_sha256=dependency['checker_binary_sha256'],
               dependency_manifest_sha256=sha(dep_path), audit_script_sha256=sha(__file__))
    stem.with_suffix('.ethos.json').write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps(out), flush=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('mode', choices=['produce', 'replay'])
    ap.add_argument('source', type=Path)
    ap.add_argument('--budget', type=int, default=120)
    a = ap.parse_args()
    (produce if a.mode == 'produce' else replay)(a.source.resolve(), a.budget)


if __name__ == '__main__':
    main()
