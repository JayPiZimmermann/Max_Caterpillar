"""Independent normalized-head check of the two-star paired-residue obstruction.

No producer/family imports. Positive-endpoint cuts, explicit pole-order formulas,
and symbolic rational identities replace rooted-away cuts and series convolution.
"""
from pathlib import Path
import itertools,json,time,hashlib
import sympy as S

def factors(unit):
    edges=[tuple(sorted(e)) for e in unit['edges']];assert len(edges)==3 and len(set(edges))==3
    adj={i:set() for i in range(1,5)}
    for u,v in edges:adj[u].add(v);adj[v].add(u)
    assert sorted(map(len,adj.values()))==[1,1,1,3]
    head=[-1,0,0,0,0];head[unit['root']]+=1
    for pos,neg in unit['edges']:
        if pos>neg:head[neg]-=1;head[pos]+=1
    out=[]
    for u,v in edges:
        reached={u};todo=[u]
        while todo:
            x=todo.pop()
            for y in adj[x]:
                if (x==u and y==v) or (x==v and y==u):continue
                if y not in reached:reached.add(y);todo.append(y)
        out.append((reached,sum(head[i] for i in reached)))
    return out

def main():
    start=time.monotonic();path=Path(__file__).with_name('overnight_uniform_pair_residue.json');raw=path.read_bytes();data=json.loads(raw)
    z=S.Symbol('z');base=[S.Integer(0),S.Integer(1),S.Integer(-1),z,-z];normal=[4,-1,-1,-1,-1];checked=[]
    for index in [0,1]:
        fac=factors(data['representatives'][index]);terms=[]
        for perm in itertools.permutations(range(5)):
            b=[base[i] for i in perm];d=[normal[i] for i in perm];nonzero=[];zero=[]
            for C,h in fac:
                q0=sum(b[i] for i in C);q1=sum(d[i] for i in C)
                for offset in [h,h+1]:
                    c=q0+offset*b[0];t=q1+offset*d[0]
                    if c==0:assert t!=0;zero.append(t)
                    else:nonzero.append((c,t))
            assert len(zero)<=2
            if not zero:continue
            den=S.prod(zero)*S.prod(c for c,t in nonzero)
            numerator=-b[0]
            if len(zero)==2:numerator=-d[0]+b[0]*sum(t/c for c,t in nonzero)
            terms.append(numerator/den)
        curve=S.cancel(sum(terms));assert S.cancel(curve-S.sympify(data['curves'][index]))==0;checked.append(curve)
    target=S.Rational(1,4)/z**2
    assert S.cancel(checked[0]/90+checked[1]/120-target)==0
    result={'status':'INDEPENDENT_EXACT_PAIRED_RESIDUE_OBSTRUCTION_PASS','curves':list(map(str,checked)),
        'identity':'R0/90 + R1/120 = 1/(4*z^2)','source_sha256':hashlib.sha256(raw).hexdigest(),
        'seconds':time.monotonic()-start,'scope':'All linear functionals of this fixed-normal first paired-residue curve fail already on two canonical stars; not a failure of general separation.'}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__':main()
