"""Independent scope/encoding audit of the six same-label necessary models.

This script neither solves the formulas nor certifies global MAX5 equality.
The mathematical coverage argument is recorded in AUDIT.md.
"""
from pathlib import Path
import hashlib
import json
import re
import sys

HERE = Path(__file__).resolve().parent
TASK = HERE.parent
ROOT = TASK.parents[4]
OLD = ROOT / 'research/sN/frontier5'
sys.path.insert(0, '/tmp/max5_first11_z3')
import z3

EXPECTED_MODEL = 'e9ea5d767546ea8f5fb06a661ff962d7cb4034f5eea0a370353f45364d66072e'
EXPECTED_INDICES = [275, 277, 280, 307, 353, 355]
EXPECTED_EXTRA = [
    ['012','013','013','014'], ['012','013','0134','014'],
    ['012','013','014','034'], ['0123','013','014','014'],
    ['013','013','014','014'], ['013','013','014','024'],
]

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    model = OLD/'max5_exact_three_shared_local.py'
    cover = OLD/'max5_three_shared_one_each_cover.json'
    assert sha(model) == EXPECTED_MODEL
    records = json.loads(cover.read_text())['kinds']['three_roots']['records']
    chosen = [(i, rec) for i, rec in enumerate(records)
              if rec['status'] == 'REMAINS'
              and sum(len(s) == 2 for s in rec['supports']) == 3]
    assert [i for i, _ in chosen] == EXPECTED_INDICES
    results = []
    for (index, rec), expected_extra in zip(chosen, EXPECTED_EXTRA):
        roots = sorted(s for s in rec['supports'] if len(s) == 2)
        assert roots == [[0,2],[1,2],[3,4]]
        extra = sorted(''.join(map(str,s)) for s in rec['supports'] if len(s)>2)
        assert extra == expected_extra
        zero_counts = [sum(i not in s for s in rec['supports']) for i in (2,3,4)]
        nonroot_zero_counts = [sum(i not in s and len(s)>2 for s in rec['supports'])
                               for i in (2,3,4)]
        assert min(zero_counts) >= 4 and min(nonroot_zero_counts) >= 1
        assert all(len(s) <= 4 for s in rec['supports'])
        source = TASK/f'case{index}.smt2'
        meta = json.loads(source.with_suffix('.metadata.json').read_text())
        assert meta['index'] == index and meta['supports'] == rec['supports']
        assert meta['source_sha256'] == sha(source)
        assert meta['model_sha256'] == sha(model)
        assert meta['cover_sha256'] == sha(cover)
        assert meta['producer_sha256'] == sha(TASK/'run.py')
        assert meta['kind'] == 'one_each_same' and meta['mode'] == 'general'
        assert meta['samples'] == 'boolean' and meta['shared_germs']
        assert meta['rigid'] and meta['wall'] and meta['coefficient_gauge']
        formula = z3.parse_smt2_string(source.read_text())
        seen=set(); variables=set(); integer_divisions=[]; quantifiers=[]
        def visit(term):
            key=term.get_id()
            if key in seen: return
            seen.add(key)
            if z3.is_quantifier(term): quantifiers.append(str(term))
            if z3.is_app(term):
                if term.decl().kind() == z3.Z3_OP_IDIV:
                    integer_divisions.append(str(term))
                if term.decl().kind() == z3.Z3_OP_UNINTERPRETED and term.num_args()==0:
                    variables.add(str(term))
            for child in term.children(): visit(child)
        for term in formula: visit(term)
        assert not integer_divisions and not quantifiers
        assert all(re.fullmatch(r'(orient[0-2]|active[01]|[ghr][0-6]|e[0-4]|a[3-6]_[0-4])',v)
                   for v in variables)
        results.append(dict(index=index, source=source.name,
            source_sha256=sha(source), metadata_sha256=sha(source.with_suffix('.metadata.json')),
            supports=rec['supports'], singular_counts=zero_counts,
            nonroot_singular_counts=nonroot_zero_counts, assertions=len(formula),
            expression_nodes=len(seen), integer_divisions=0, quantifiers=0,
            variables=sorted(variables)))
    out=dict(status='SIX_CASE_SCOPE_AND_ENCODING_AUDIT_PASS_NOT_UNSAT',
        scope='Exactly the six surviving support classes with three physical root rows in the same-label one-each three-shared-contact sector.',
        source_model_sha256=sha(model), support_cover_sha256=sha(cover),
        runner_sha256=sha(TASK/'run.py'), audit_sha256=sha(__file__), cases=results)
    (HERE/'receipt.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(dict(status=out['status'], cases=len(results), indices=EXPECTED_INDICES)))

if __name__=='__main__': main()
