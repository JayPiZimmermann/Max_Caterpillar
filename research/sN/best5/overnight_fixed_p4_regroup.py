"""Exact necessary curvature gate for collapsing subsets of the12-term upper.

A single signed ReLU of any W7 form, modulo a W7 remainder, has at most
one interior hyperplane on each braid cone, with one global curvature sign.
This gate imposes no coefficient dictionary on the prospective replacement.
Passing a subset is not a construction or a full feasibility statement.
"""
from fractions import Fraction as Q
from itertools import permutations
from pathlib import Path
import json,hashlib,time
HERE=Path(__file__).resolve().parent


def main():
    start=time.monotonic();path=HERE/'overnight_fixed_cross_net9_14_simple.json';net=json.loads(path.read_text());A=[[Q(x)for x in r]for r in net['first_layer'][:7]];W=[[Q(x)for x in r[:7]]for r in net['second_layer'][2:]];D=list(map(Q,net['output'][2:]));cones=[]
    for p in permutations(range(5)):
        rank={v:i for i,v in enumerate(p)};active=[]
        for row in A:
            i=next(i for i,x in enumerate(row)if x>0);j=next(i for i,x in enumerate(row)if x<0);active.append(row if rank[i]<rank[j]else[Q(0)]*5)
        curv={}
        for k,(d,w)in enumerate(zip(D,W)):
            g=tuple(sum(w[j]*active[j][i]for j in range(7))for i in range(5));partial=[sum(g[p[j]]for j in range(t))for t in range(1,5)]
            if min(partial)<0<max(partial):
                scale=next(x for x in g if x);normal=tuple(x/scale for x in g);curv.setdefault(normal,[Q(0)]*12)[k]=d*abs(scale)
        cones.append((p,curv))
    candidates=[];first_failure={};counts={'multi_hyperplane':0,'mixed_curvature_signs':0,'passes':0}
    for mask in range(1,1<<12):
        size=mask.bit_count()
        if not 2<=size<12:continue
        sign=0;failure=None
        for p,curv in cones:
            values=[sum(c for k,c in enumerate(cs)if mask>>k&1)for cs in curv.values()];values=[v for v in values if v]
            if len(values)>1:failure='multi_hyperplane';break
            if values:
                s=1 if values[0]>0 else-1
                if sign and sign!=s:failure='mixed_curvature_signs';break
                sign=s
        if failure:counts[failure]+=1;first_failure[mask]={'reason':failure,'cone':p}
        else:counts['passes']+=1;candidates.append({'indices':[k for k in range(12)if mask>>k&1],'curvature_sign':sign})
    out={'status':'EXACT_CONTINUOUS_SINGLE_RELU_REGROUP_NECESSARY_GATE','counts':counts,'candidates':candidates,'seconds':time.monotonic()-start,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'network_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'scope':'Only replacing a subset of the existing12 fixed weighted units by one arbitrary W7 ReLU modulo W7. Passing candidates are not globally feasible; no general five-unit obstruction.'};(HERE/'overnight_fixed_p4_regroup.json').write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='candidates'},sort_keys=True),flush=True);print('candidate sizes', {n:sum(len(x['indices'])==n for x in candidates)for n in range(2,12)},flush=True)
if __name__=='__main__':main()
