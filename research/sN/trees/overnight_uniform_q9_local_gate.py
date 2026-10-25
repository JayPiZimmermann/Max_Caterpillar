"""Exact local six-term rational identity gate for the proposed Q_* score.

Every relation is valid before symmetrizing. Two rooted child subtrees of
frequencies x,y are rewired, using f_e(q)=1/[q(q+e*a)]. All other factors
are unchanged. This avoids promoting a finite evaluation relation to proof.
"""
from pathlib import Path
from fractions import Fraction
import itertools,json,time
from overnight_uniform_pruning_candidate_target import score

HERE=Path(__file__).parent

def rewires(U,r,v,w):
    rest=[tuple(e)for e in U['edges']if set(e)not in({r,v},{r,w})]
    # epsilon + is child -> parent. Star +- minus star -+.
    specs=[(1,[(v,r),(r,w)]),(-1,[(r,v),(w,r)]),
           (-1,[(w,r),(v,w)]),(1,[(v,r),(w,v)]),
           (1,[(r,w),(w,v)]),(-1,[(r,v),(v,w)])]
    return [(c,{'root':U['root'],'edges':rest+E})for c,E in specs]

def main():
    before=time.monotonic();D=json.loads((HERE/'overnight_uniform_q9_inventory.json').read_text());tested=0
    # Test the measured twelve-term relation's representatives first.
    A=json.loads((HERE/'overnight_uniform_q9_full_gate_2112.json').read_text())['all_pm_with_stars_and_target']['smallest_violated_sampled_relation'];order=list(map(int,A))+[j for j in range(len(D['units']))if str(j)not in A]
    for j in order:
        U=D['units'][j];U={'root':U['root'],'edges':list(map(tuple,U['edges']))};T={v:[]for v in range(1,9)}
        for a,b in U['edges']:T[a].append(b);T[b].append(a)
        parent={U['root']:None};todo=[U['root']]
        for r in todo:
            for v in T[r]:
                if v!=parent[r]:parent[v]=r;todo.append(v)
        for r in todo:
            for v,w in itertools.combinations([v for v in T[r]if v!=parent[r]],2):
                terms=rewires(U,r,v,w);values=[score(u)for c,u in terms];pairing=sum(c*q for(c,u),q in zip(terms,values));tested+=1
                if pairing:
                    out={'status':'EXACT_LOCAL_IDENTITY_Q_SCORE_COUNTEREXAMPLE','source_raw_column':j,'junction':r,'children':[v,w],'terms':[dict(coefficient=c,unit=u,score=str(q))for(c,u),q in zip(terms,values)],'score_pairing':str(pairing),'tested_local_identities':tested,'seconds':time.monotonic()-before,'scope':'The displayed local six-term identity is a rational identity for arbitrary a,x,y; only its algebraic independent checker remains to be run.'};Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2),flush=True);return
    out={'status':'NO_LOCAL_SCORE_OBSTRUCTION','identities':tested,'seconds':time.monotonic()-before};Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(out,flush=True)

if __name__=='__main__':main()
