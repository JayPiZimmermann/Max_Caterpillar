"""Exact positive control of locality equations using the certified network."""
import hashlib
import itertools
import json
from fractions import Fraction as Q
from pathlib import Path
from overnight_fixed_bowtie_k3 import FLATS,problem
from overnight_fixed_bowtie_ray import ray_problem


def main():
    net=json.loads(Path("netB_10_6.json").read_text())
    aa=[[Q(c) for c in row] for row in net["first_layer"]]
    ww=[[Q(c) for c in row] for row in net["second_layer"]]
    dd=[Q(c) for c in net["output"]]
    sets=[frozenset(c) for n in range(1,6) for c in itertools.combinations(range(5),n)]
    rel=[S for S in sets if len(S) in (3,4)];idx={S:i for i,S in enumerate(rel)}
    def val(k,S):return sum(w*max(sum(a[i] for i in S),0) for w,a in zip(ww[k],aa))
    zs=[sum(1<<idx[S] for S in rel if val(k,S)==0) for k in range(2,6)]
    ds=[1 if dd[k]>0 else -1 for k in range(2,6)]
    checked=0
    for U in sets:
        if len(U)<3:continue
        outs=[o for o in range(5) if o not in U] if len(U)==3 else [None]
        for o in outs:
            total=Q(0)
            for k in range(2,6):
                if val(k,U)!=0 or (o is not None and val(k,U|{o})!=0):continue
                total+=dd[k]*sum((-1)**(len(U)-len(S))*max(val(k,S),0) for S in sets if S<=U)
            assert total==(-1)**(len(U)+1)
            checked+=1
    # Independent exact recovery of flat coordinates in the eight-feature
    # parameterization, then substitution in the compressed equations.
    coords=[]
    for k,z in zip(range(2,6),zs):
        b=[[Q(c) for c in row] for row in FLATS[z]["basis"]]
        target=[abs(dd[k])*c for c in ww[k][:8]]
        cc=[]
        for j,row in enumerate(b):
            col=next(p for p in range(8) if row[p]==1 and all(i==j or bb[p]==0 for i,bb in enumerate(b)))
            cc.append(target[col])
        assert all(sum(cc[j]*b[j][i] for j in range(len(b)))==target[i] for i in range(8))
        coords+=cc
    p=problem(zs,ds);assert p is not None
    n,offsets,rows=p;assert n==len(coords)
    for expr,rhs in rows:
        assert sum(c*abs(sum(a*b for a,b in zip(f,coords))) for f,c in expr.items())==rhs
    strengthened=ray_problem(zs,ds);assert strengthened is not None
    for expr,rhs in strengthened[2]:
        assert sum(c*abs(sum(a*b for a,b in zip(f,coords))) for f,c in expr.items())==rhs
    result={"status":"EXACT_K4_POSITIVE_CONTROL_PASS","direct_equations":checked,
            "compressed_equations":len(rows),"flats":zs,"signs":ds,
            "ray_strengthened_equations":len(strengthened[2]),
            "network_sha256":hashlib.sha256(Path("netB_10_6.json").read_bytes()).hexdigest(),
            "scope":"instrument positive control; global construction was already independently certified"}
    Path("overnight_fixed_controls.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps(result,sort_keys=True),flush=True)


if __name__=="__main__":main()
