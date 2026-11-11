"""Audit exactly six elementary singleton-triple clauses for case 277.

No arithmetic satisfiability claim is made by this checker.
"""
from itertools import combinations
from pathlib import Path
import hashlib
import json

from check_row_gauge import keys, z3

HERE=Path(__file__).resolve().parent
TASK=HERE.parent
ROOT=TASK.parents[4]
OLD=ROOT/'research/sN/frontier5'

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def main():
    source=TASK/'case277_single.smt2'
    previous=TASK/'case277.smt2'
    meta_path=source.with_suffix('.metadata.json')
    meta=json.loads(meta_path.read_text())
    previous_meta=json.loads(previous.with_suffix('.metadata.json').read_text())
    cover=OLD/'max5_three_shared_one_each_cover.json'
    rec=json.loads(cover.read_text())['kinds']['three_roots']['records'][277]
    assert meta['source_sha256']==sha(source)
    assert previous_meta['source_sha256']==sha(previous)
    assert meta['producer_sha256']==sha(TASK/'emit_singleton.py')
    assert meta['model_sha256']==sha(OLD/'max5_exact_three_shared_local.py')
    assert meta['cover_sha256']==sha(cover)
    for field in ('index','kind','mode','samples','shared_germs','wall','rigid',
                  'mandatory_roots','supports','coefficient_gauge'):
        assert meta[field]==previous_meta[field]
    assert meta['supports']==rec['supports']
    roots=[tuple(e) for e in meta['mandatory_roots']]
    extra=sorted(tuple(s) for s in rec['supports'])
    for edge in roots:extra.remove(edge)
    supports=roots+extra
    found=[]
    for triple in combinations(range(5),3):
        singular=[j for j,s in enumerate(supports) if set(s)<=set(triple)]
        if len(singular)==1 and len(supports[singular[0]])==3:
            found.append(dict(triple=list(triple),row=singular[0]))
    assert found==[dict(triple=[0,1,3],row=4),dict(triple=[0,1,4],row=6)]
    assert meta['singleton_rows']==found
    expected=[]
    for row in found:
        j=row['row'];g=z3.Real(f'g{j}');h=z3.Real(f'h{j}')
        expected.extend([g!=0,h!=0,z3.Or(g==h,g==-h)])
    old=z3.parse_smt2_string(previous.read_text())
    new=z3.parse_smt2_string(source.read_text())
    a,b=keys(old),keys(new)
    assert not a-b and b-a==keys(expected) and len(b-a)==6
    seen=set();bad=[]
    def visit(term):
        key=term.get_id()
        if key in seen:return
        seen.add(key)
        if z3.is_quantifier(term):bad.append('quantifier')
        if z3.is_app(term) and term.decl().kind()==z3.Z3_OP_IDIV:bad.append('integer division')
        for ch in term.children():visit(ch)
    for term in new:visit(term)
    assert not bad
    geometry=[ROOT/'notes/max5_exact/allfive_shared_rank.md',
              ROOT/'notes/max5_exact/shared_rank_audit.md']
    receipt=dict(status='CASE277_SIX_SINGLETON_CLAUSES_AUDIT_PASS_NOT_UNSAT',
        scope='Exactly the elementary singleton-rootless-top-triple constraints for case277; no global width or arithmetic refutation claim.',
        previous_source_sha256=sha(previous),source_sha256=sha(source),
        metadata_sha256=sha(meta_path),producer_sha256=sha(TASK/'emit_singleton.py'),
        model_sha256=meta['model_sha256'],cover_sha256=sha(cover),
        old_assertions=len(old),new_assertions=len(new),added_assertions=6,
        removed_assertions=0,singletons=found,integer_division_nodes=0,
        geometry_sources={str(p.relative_to(ROOT)):sha(p) for p in geometry},
        canonicalizer_sha256=sha(HERE/'check_row_gauge.py'),audit_sha256=sha(__file__))
    (HERE/'singleton_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(dict(status=receipt['status'],singletons=found)))

if __name__=='__main__':main()
