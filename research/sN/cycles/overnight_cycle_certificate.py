#!/usr/bin/env python3
"""Replay the compact canonical-cycle obstruction, without expanded orbit caches.

The default checks coverage, all independent DP evaluation rows, the scalar
rank gap, and the integrity of the archived symbolic proof. --prove additionally
rebuilds and proves every rational identity from scratch, without resuming any
archived step. Neither mode needs the 99 MB expanded family or native matrices.
"""
import argparse
from fractions import Fraction as Q
from pathlib import Path
import hashlib,json,math,time

import overnight_cycle_symmetric_exact as E
import overnight_upper_weighted_paths as W
from overnight_upper_cycle_minor import rank

HERE=Path(__file__).resolve().parent
TREES=HERE.parent/'trees'
BASE=HERE/'overnight_cycle_symmetric_7'


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def check(prove=False,budget=1800):
    started=time.monotonic()
    inventory=json.loads(BASE.with_suffix('.inventory.json').read_text())
    proposal=json.loads(BASE.with_suffix('.path_kernels.json').read_text())
    archived=json.loads(BASE.with_suffix('.exact.json').read_text())
    minor_path=TREES/'overnight_upper_cycle_minor_7.json'
    minor=json.loads(minor_path.read_text())
    assert minor['inventory_sha256']==sha(BASE.with_suffix('.inventory.json'))
    assert minor['dp_producer_sha256']==sha(Path(W.__file__))
    assert minor['original_matrix_sha256']==archived['matrix_sha256']
    assert archived['status']=='EXACT_ENDPOINT_SHIFTED_PATH_OBSTRUCTION'
    assert sorted(item['index'] for item in archived['passed'])==list(range(12))
    for name,expected in archived['hashes'].items():
        matches=[p for p in (HERE/name,TREES/name,TREES/'all_tree_dfs'/name) if p.is_file()]
        assert len(matches)==1 and sha(matches[0])==expected,(name,'archived source mismatch')

    reps=inventory['representatives'];ids=proposal['path_columns']
    assert ids==[j for j,(key,atoms) in enumerate(reps) if len(key[1])==5]
    assert len(ids)==138 and minor['prime']==W.P==1000000007
    signatures=W.family(7,'unit1');lookup={s:i for i,s in enumerate(signatures)}
    assert len(signatures)==138
    dag=W.Compiler(7).compile(signatures);mapping=[];seen=set()
    for original in ids:
        (head,edges),atoms=reps[original]
        assert edges==[[i,i+1] for i in range(1,6)] and head[0]==-1 and sum(head)==0
        signature=tuple((sum(head[i:])-1,1) for i in range(2,7))
        canonical=W.canonical(signature)
        auto=2 if signature==tuple((1-h-w,w) for h,w in signature[::-1]) else 1
        assert canonical not in seen;seen.add(canonical)
        mapping.append(dict(original_column=original,dp_column=lookup[canonical],
                            signature=canonical,automorphisms=auto))
    assert seen==set(signatures)
    assert json.loads(json.dumps(mapping))==minor['column_mapping']

    rows=[]
    assert len(minor['points'])==len(minor['modular_rows'])==127
    for point,expected in zip(minor['points'],minor['modular_rows']):
        assert len(point)==7 and sum(point)==0
        values=dag.evaluate(point,W.P)
        row=[values[m['dp_column']]*pow(m['automorphisms'],-1,W.P)%W.P for m in mapping]
        row.append(pow(math.prod(point)%W.P,-1,W.P))
        assert row==expected
        rows.append(row)
    ranks=[rank([row[:-1] for row in rows],W.P),rank(rows,W.P)]
    assert ranks==[126,127]

    free=proposal['kernel_free_columns'];vectors=proposal['kernel_vectors']
    assert len(free)==len(vectors)==12 and len(set(free))==12
    for f,vector in zip(free,vectors):
        v={j:Q(c) for j,c in vector}
        assert len(v)==len(vector) and set(v)<=set(ids) and v[f]==1
        assert all(v.get(g,Q(0))==0 for g in free if g!=f)
        for row in rows:
            assert sum(row[ids.index(j)]*(c.numerator%W.P)*pow(c.denominator%W.P,-1,W.P)
                       for j,c in v.items())%W.P==0
    print('COMPACT_COVERAGE_AND_MINOR_PASS',ranks,flush=True)

    symbolic=[]
    if prove:
        for i,vector in enumerate(vectors):
            began=time.monotonic();expression=E.expression(reps,vector)
            remaining=budget-(time.monotonic()-started)
            assert remaining>0,'fresh proof budget exhausted'
            receipt=E.prove(expression,remaining)
            receipt.update(index=i,seconds=time.monotonic()-began)
            symbolic.append(receipt)
            print('FRESH_KERNEL_PASS',i,'OF',len(vectors),flush=True)
    result=dict(status='FRESH_COMPACT_CYCLE_SYMBOLIC_PROOF_PASS' if prove else
                'COMPACT_CYCLE_STRUCTURE_MINOR_AND_ARCHIVE_INTEGRITY_PASS',
                n=7,path_orbits=138,independent_modular_ranks=ranks,
                exact_independent_kernel_vectors=12,symbolic_proof_replayed=prove,
                fresh_symbolic_receipts=symbolic,seconds=time.monotonic()-started,
                checker_sha256=sha(Path(__file__)),minor_sha256=sha(minor_path),
                archived_symbolic_proof_sha256=sha(BASE.with_suffix('.exact.json')))
    return result


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--prove',action='store_true')
    parser.add_argument('--budget',type=float,default=1800);parser.add_argument('--output',type=Path)
    args=parser.parse_args();result=check(args.prove,args.budget)
    if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)
