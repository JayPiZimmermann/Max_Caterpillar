"""Exact full-S9 control using induced subtrees and zero-cone flag indices.

No9! polytope sweep: all126 retained subsets are exhausted, and the only
five potentially nonzero cases have identical cube projections.
"""
from pathlib import Path
from fractions import Fraction as Q
from collections import Counter
import itertools,json,math,time
HERE=Path(__file__).parent
E=[(2,1),(3,2),(4,3),(5,1),(6,1),(7,1),(8,1)]

def flag_value(vertices,directions,j):
    if not directions:
        v=[x[j]for x in vertices];return max(v)-min(v)
    values=[sum(a*b for a,b in zip(x,directions[0]))for x in vertices]
    hi=tuple(x for x,v in zip(vertices,values)if v==max(values));lo=tuple(x for x,v in zip(vertices,values)if v==min(values))
    return flag_value(hi,directions[1:],j)-flag_value(lo,directions[1:],j)

def main():
    start=time.monotonic();flags=json.loads((HERE/'dfs_review_flag_certificate.log').read_text())['flags'];eta=Q(0);indices=[]
    for f in flags:
        directions=f['directions']+[[int(i==f['final_coordinate'])for i in range(5)]];v=0
        for signs in itertools.product((-1,1),repeat=4):
            belongs=True
            for coordinate in range(4):
                first=next(sign*(u[coordinate]-u[4])for sign,u in zip(signs,directions)if u[coordinate]!=u[4])
                if first>0:belongs=False;break
            if belongs:v+=math.prod(signs)
        eta+=Q(f['weight'])*v;indices.append(v)
    assert eta==-1
    graph={i:set()for i in range(1,9)}
    for a,b in E:graph[a].add(b);graph[b].add(a)
    classes=Counter();paths=[]
    for retained in itertools.combinations(range(9),5):
        if 0 not in retained:classes['apex_removed']+=1;continue
        I=set(retained)-{0};todo=[min(I)];seen=set(todo)
        for a in todo:
            for b in graph[a]&I:
                if b not in seen:seen.add(b);todo.append(b)
        if seen!=I:classes['disconnected_retained_tree']+=1;continue
        assert 1 in I
        edges=[(a,b)for a,b in E if a in I and b in I];assert len(edges)==3
        matching=any(len(set(e+f))==4 for e,f in itertools.combinations(edges,2))
        if not matching:
            assert max(len(graph[a]&I)for a in I)==3;classes['retained_star']+=1;continue
        deleted=set(range(1,9))-I;assert all(len(graph[a])==1 for a in deleted)
        assert I=={1,2,3}|(I&{4,5,6,7,8})and len(I&{4,5,6,7,8})==1
        assert all(int(a==1)+sum(u==a for u,v in edges)==1 for a in I)
        classes['retained_path']+=1;paths.append(sorted(I))
    assert dict(classes)=={'retained_path':5,'retained_star':10,'disconnected_retained_tree':55,'apex_removed':56}
    def core_value(star=False,simplex=False):
        if simplex:vertices=tuple(tuple(int(i==j)for i in range(5))for j in range(5))
        else:
            edges=[(2,1),(3,1),(4,1)]if star else[(2,1),(3,2),(4,3)];vertices={(0,)*5}
            for bits in itertools.product((0,1),repeat=3):
                x=[-1,1,0,0,0]
                for b,(i,j)in zip(bits,edges):
                    if b:x[i]+=1;x[j]-=1
                vertices.add(tuple(x))
            vertices=tuple(vertices)
        total=Q(0)
        for p in itertools.permutations(range(5)):
            V=tuple(tuple(v[i]for i in p)for v in vertices)
            for f in flags:total+=Q(f['weight'])*flag_value(V,f['directions'],f['final_coordinate'])
        return total
    path=core_value();star=core_value(star=True);maximum=core_value(simplex=True);assert(path,star,maximum)==(60,0,120)
    full_graft=classes['retained_path']*math.factorial(5)*math.factorial(4)*eta*path;full_max=math.factorial(9)*eta*maximum;assert full_graft==-864000 and full_max==-43545600
    out={'status':'EXACT_FULL_S9_FLAG_LIFT_COUNTEREXAMPLE','grafted_tree':{'apex':0,'root':1,'edges':E},'retained_subset_classes':dict(classes),'retained_paths':paths,'orthant_flag_indices':indices,'weighted_transfer_coefficient':str(eta),'base_separator_values':{'path':str(path),'star':str(star),'maximum':str(maximum)},'unaveraged_full_S9_graft_value':str(full_graft),'unaveraged_full_S9_maximum_value':str(full_max),'scope':'Exact full-label symmetrization of the actual filtration-dropping six-flag lift, followed by the certified five-label separator. This fixed lift fails on a canonical tree of matching number2. It does not exclude other complete-flag/tensor assemblies.','seconds':time.monotonic()-start};Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2),flush=True)

if __name__=='__main__':main()
