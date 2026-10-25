#!/usr/bin/env python3
"""Complete-family local residue gate for the smallest Baxter class bridge.

Every original forest/head state is included. The only budget filter is
which target poles are tested; it never removes source columns at a pole.
"""
from collections import defaultdict,Counter
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import hashlib,json,random,time
from flint import nmod_mat
import overnight_upper_baxter_forest_states as family
import overnight_upper_baxter_apex_geometry as geom
import overnight_upper_baxter_union as old
from overnight_upper_baxter_union_exact import expression,unit
from overnight_upper_baxter_apex_probe import atom_term
from rational_identity import term,subst,Verifier
HERE=Path(__file__).parent

def residue(key,c,pole):
    num,power,den=key
    if pole not in dict(den):return None
    assert dict(den)[pole]==1
    j=next(i for i,v in enumerate(pole[:-1]) if v)
    section=tuple(-Q(v,pole[j]) for v in pole[:j]+pole[j+1:])
    return term(c/Q(pole[j]),subst(num,j,section),power,
                [(subst(f,j,section),m) for f,m in den if f!=pole])

def main():
    start=time.monotonic();n=5;data=json.loads((HERE/'overnight_upper_baxter_union.json').read_text())
    graph=tuple(sorted(set(map(tuple,data['union_graph']))|{(0,i) for i in range(1,n)}))
    target=defaultdict(Q)
    for u,c in data['target']:
        key,d=expression(n,unit(u));target[key]+=c*d
    catalog={};heads=nonzero=forests=0
    for B in combinations(graph,3):
        if geom.components(n,B) is None:continue
        forests+=1
        for h in family.head_family(n,graph,B):
            heads+=1;atom=family.forest_atom(n,B,h)
            if atom is None:continue
            nonzero+=1;key,c=atom_term(n,atom);catalog.setdefault(key,(c,h,B))
    incidence=defaultdict(list)
    for key in catalog:
        for pole,m in key[2]:
            assert m==1
            incidence[pole].append(key)
    target_poles={p for k in target for p,m in k[2]};records=[];rng=random.Random(25102567)
    result=dict(status='RUNNING_COMPLETE_FAMILY_RESIDUE_GATE',n=n,graph=graph,
        normalized_head_descriptions=heads,nonzero_descriptions=nonzero,forests=forests,
        distinct_kernels=len(catalog),all_poles=len(incidence),target_poles=len(target_poles),records=records,
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        scope='All original five-state forest/head kernels are included at every tested pole. A local residue gap refutes the fixed-apex, fixed-twin-graph class bridge; passing tested poles does not prove a global identity.')
    dest=HERE/'overnight_upper_hopf_residue.json'
    for pole in sorted(target_poles,key=lambda p:len(incidence[p])):
        rhs=defaultdict(Q)
        for k,c in target.items():
            r=residue(k,c,pole)
            if r is not None:rhs[r[0]]+=r[1]
        rhs={k:c for k,c in rhs.items() if c}
        if Verifier(30).check(rhs):
            records.append(dict(pole=pole,status='TARGET_RESIDUE_EXACTLY_ZERO'));continue
        source={}
        for k in incidence[pole]:
            r=residue(k,Q(1),pole)
            if r is not None:source.setdefault(r[0],(k,r[1]))
        keys=sorted(source)
        if len(keys)>500:
            records.append(dict(pole=pole,status='PREDECLARED_COLUMN_BUDGET_SKIP',columns=len(keys)));continue
        points=[];rows=[]
        while len(rows)<len(keys)+16:
            point=tuple(rng.randrange(1,10000) for _ in range(3))
            try:
                row=[family.eval_term(k,Q(1),point) for k in keys]
                v=sum(family.eval_term(k,c,point) for k,c in rhs.items())%family.PRIME
            except ZeroDivisionError:continue
            points.append(point);rows.append(row+[v])
        rr,rank=nmod_mat(rows,family.PRIME).rref()
        pivots=[next(j for j in range(len(keys)+1) if rr[i,j]) for i in range(rank)]
        gap=len(keys) in pivots
        record=dict(pole=pole,incident_full_kernels=len(incidence[pole]),residue_columns=len(keys),
            ranks=[rank-int(gap),rank],status='MODULAR_LOCAL_RESIDUE_GAP' if gap else 'LOCAL_RESIDUE_INCLUSION_DIAGNOSTIC')
        if gap:
            kernels=[]
            for f in sorted(set(range(len(keys)))-set(pivots)):
                cs={f:Q(1)}
                for i,j in enumerate(pivots[:-1]):
                    c=old.reconstruct(int(-rr[i,f]),family.PRIME);assert c is not None
                    if c:cs[j]=c
                V=Verifier(60);assert V.check({keys[j]:c for j,c in cs.items()})
                kernels.append([[j,str(c)] for j,c in cs.items()])
            record.update(status='EXACT_COMPLETE_FAMILY_LOCAL_RESIDUE_OBSTRUCTION',points=points,
                prime=family.PRIME,kernels=kernels,
                residue_sources=[dict(full_key=source[k][0],residue_key=k) for k in keys],
                target_residue=[[k,str(c)] for k,c in rhs.items()])
        records.append(record);result['seconds']=time.monotonic()-start
        dest.write_text(json.dumps(result,indent=2)+'\n')
        print('HOPF RESIDUE',pole,'INCIDENT',len(incidence[pole]),'COLS',len(keys),'RANKS',record['ranks'],record['status'],
              'SECONDS',result['seconds'],flush=True)
        if gap:
            result['status']='EXACT_FULL_FIXED_GRAPH_BAXTER_CLASS_BRIDGE_OBSTRUCTION';break
    else:result['status']='COMPLETE_BOUNDED_LOCAL_RESIDUE_GATE_NO_OBSTRUCTION_FOUND'
    result['seconds']=time.monotonic()-start
    dest.write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],'SECONDS',result['seconds'],flush=True)

if __name__=='__main__':main()
