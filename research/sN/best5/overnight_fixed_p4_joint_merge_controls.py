"""Independent structural controls for pair and2:1 merge incidences.

Direct rational geometry of both known networks; no Z3 or encoder import.
"""
from fractions import Fraction as Q
from collections import Counter,defaultdict
from itertools import permutations
from pathlib import Path
import json,time,hashlib
HERE=Path(__file__).resolve().parent


def check(name):
    n=json.loads((HERE/name).read_text());A=[list(map(Q,r))for r in n['first_layer'][:-2]];W=[list(map(Q,r[:-2]))for r in n['second_layer'][2:]];D=list(map(Q,n['output'][2:]));R=list(map(Q,n['second_layer'][0][:-2]));ref=next(i for i,v in enumerate(n['first_layer'][-2])if Q(v));cells={}
    for p in permutations(range(5)):
        rank={v:i for i,v in enumerate(p)};act=[row if rank[next(i for i,v in enumerate(row)if v>0)]<rank[next(i for i,v in enumerate(row)if v<0)]else[Q(0)]*5 for row in A];key=tuple(any(row)for row in act);cell=cells.setdefault(key,{'active':act,'sets':set(),'tops':set()});cell['sets'].update(tuple(sorted(p[:t]))for t in range(1,5));cell['tops'].add(p[0])
    pairs=triples=target_groups=0
    for cell in cells.values():
        act=cell['active'];tops=sorted(cell['tops']);assert len(tops)<=2;normal=tuple(Q(i==tops[0])-Q(i==tops[1])for i in range(5))if len(tops)==2 else None;linear=[sum(w*r[i]for w,r in zip(R,act))for i in range(5)];groups=defaultdict(lambda:[Counter(),Counter()])
        for w,d in zip(W,D):
            g=tuple(abs(d)*sum(w[j]*act[j][i]for j in range(len(A)))for i in range(5));s=1 if d>0 else-1;vals=[sum(g[j]for j in S)for S in cell['sets']]
            if min(vals)>=0:linear=[x+s*y for x,y in zip(linear,g)]
            elif max(vals)<=0:pass
            else:
                sc=next(v for v in g if v);nm=tuple(v/sc for v in g);groups[nm][int(s<0)][abs(sc)]+=1
                if sc<0:linear=[x+s*y for x,y in zip(linear,g)]
        if normal is not None:
            p,n=groups.pop(normal);assert sum(v*c for v,c in p.items())-sum(v*c for v,c in n.items())==1;target_groups+=1
        for p,n in groups.values():
            common=p&n;p-=common;n-=common;pairs+=sum(common.values())
            while p or n:
                hit=False
                for small,big in((p,n),(n,p)):
                    for a,count in list(small.items()):
                        if count>=2 and big[2*a]>0:small[a]-=2;big[2*a]-=1;small+=Counter();big+=Counter();triples+=1;hit=True;break
                    if hit:break
                assert hit,(p,n)
        assert linear==[Q(i==tops[-1])-Q(i==ref)for i in range(5)]
    return{'network':name,'cells':len(cells),'target_wall_groups':target_groups,'spurious_pair_cancellations':pairs,'spurious_two_to_one_merges':triples,'network_sha256':hashlib.sha256((HERE/name).read_bytes()).hexdigest()}


def main():
    start=time.monotonic();result={'status':'INDEPENDENT_EXACT_INCIDENCE_CONTROLS_PASS','controls':[check('netB_10_6.json'),check('overnight_fixed_cross_net9_14_simple.json')],'seconds':time.monotonic()-start,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};(HERE/'overnight_fixed_p4_joint_merge_controls.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print(json.dumps(result,sort_keys=True),flush=True)
if __name__=='__main__':main()
