"""Independent exact symbolic refutation of the leading pair-infinity separator.

Only two star descriptions and the proposed coefficients are read. No pruning
formula, hook count, rooted cuts, producer evaluator, or finite grid is used.
Normalized heads and direct Laurent degrees for all120 S5 assignments instead.
"""
from pathlib import Path
import hashlib,itertools,json,time
import sympy as S

HERE=Path(__file__).parent

def symbolic_limit(unit,r,s):
    vertices=range(1,5);edges=[tuple(sorted(e)) for e in unit['edges']];adj={v:set() for v in vertices}
    for u,v in edges:adj[u].add(v);adj[v].add(u)
    assert sorted(map(len,adj.values()))==[1,1,1,3]
    head=[-1,0,0,0,0];head[unit['root']]+=1
    for u,v in unit['edges']:
        if u>v:head[u]+=1;head[v]-=1
    factors=[]
    for u,v in edges:
        C={u};todo=[u]
        while todo:
            x=todo.pop()
            for y in adj[x]:
                if {x,y}=={u,v}:continue
                if y not in C:C.add(y);todo.append(y)
        factors.append((C,sum(head[i] for i in C)))
    base=[S.Integer(0),-1-r-s,S.Integer(1),r,s];slope=[1,-1,0,0,0];terms=[]
    for p in itertools.permutations(range(5)):
        b=[base[i] for i in p];d=[slope[i] for i in p];deg_num=int(d[0]!=0);num=-d[0] if d[0] else -b[0];deg_den=0;den=1
        for C,h in factors:
            q0=sum(b[i] for i in C);q1=sum(d[i] for i in C)
            for offset in [h,h+1]:
                c=q0+offset*b[0];t=q1+offset*d[0]
                if t:deg_den+=1;den*=t
                else:assert c!=0;den*=c
        assert deg_num-deg_den<=-2
        if deg_num-deg_den==-2:terms.append(num/den)
    return S.factor(S.cancel(sum(terms)))

def main():
    start=time.monotonic();source=HERE/'overnight_uniform_pruning_gate.json';raw=source.read_bytes();data=json.loads(raw);r,s=S.symbols('r s');weights=[S.Rational(c) for c in data['target_combination']];indices=[i for i,w in enumerate(weights) if w];assert indices==[0,1]
    curves={i:symbolic_limit(data['units'][i],r,s) for i in indices};target=-1/(r*s)
    assert S.cancel(sum(weights[i]*curves[i] for i in indices)-target)==0
    result={'status':'INDEPENDENT_EXACT_PAIR_INFINITY_OBSTRUCTION_PASS','curves':{str(i):str(v) for i,v in curves.items()},'identity':'L(F_star0)/72 - L(F_star1)/48 = -1/(r*s)','seconds':time.monotonic()-start,'source_sha256':hashlib.sha256(raw).hexdigest(),'scope':'The entire leading pair-at-infinity map loses separation already at5 labels; not a counterexample to the full tree lower bound.'}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':main()
