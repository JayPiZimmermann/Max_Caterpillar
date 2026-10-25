"""Exact direct Vandermonde-square test on the actual sheared N5 kernels.

L(R)=Delta(partial_x)^2 R(-sum x,x1,x2,x3,x4) at x=(1,1,1,1).
This is an actual linear functional, including every apex placement. Compute
derivatives by exact polynomial moments of inverse linear denominators.
"""
from pathlib import Path
import itertools,json,math,sys,time
sys.path.append(str(Path('research/sN/dfs/h5-growth/venv/lib/python3.12/site-packages')))
from flint import fmpq,fmpq_mpoly_ctx

HERE=Path(__file__).parent
STARS=[{'root':1,'edges':[(2,1),(3,2),(4,2)]}]

def functional(factors,b=None):
    k=len(factors);ctx=fmpq_mpoly_ctx.get(tuple('t'+str(i)for i in range(k)));t=ctx.gens();L=[sum(factors[j][i]*t[j]for j in range(k))for i in range(4)];diff=[(i,j,L[j]-L[i])for i in range(4)for j in range(i+1,4)]
    if any(not d for i,j,d in diff):return fmpq(0),0
    P=ctx.constant(1)
    for i,j,d in diff:P*=d*d
    if b is not None:
        Pb=ctx.constant(0)
        for i,j,d in diff:
            if b[j]!=b[i]:Pb+=2*(b[j]-b[i])*(P/d)
        P=sum(b)*P-Pb
    rates=[sum(v)for v in factors];assert all(rates);out=fmpq(0)
    for powers,c in P.to_dict().items():
        val=c
        for z,r in zip(powers,rates):val*=fmpq(math.factorial(z),r**(z+1))
        out+=val
    return out,len(P)

def factors_rooted(unit,om):
    adj=[set()for _ in range(5)]
    for u,v in unit['edges']:adj[u].add(v);adj[v].add(u)
    root=unit['root'];parent={root:None};todo=[root]
    for u in todo:
        for v in adj[u]:
            if v!=parent[u]:parent[v]=u;todo.append(v)
    a=om[0];E=set(unit['edges']);out=[]
    for v in todo[1:]:
        C={v};queue=[v]
        for w in queue:
            for z in adj[w]:
                if z!=parent[w]:C.add(z);queue.append(z)
        q=tuple(sum(om[w][i]for w in C)for i in range(4));eps=1 if(v,parent[v])in E else -1;out.extend([q,tuple(q[i]+eps*a[i]for i in range(4))])
    return out,tuple(-z for z in a)

def factors_normalized(unit,om):
    h=[-1,0,0,0,0];h[unit['root']]+=1;adj=[set()for _ in range(5)]
    for u,v in unit['edges']:
        adj[u].add(v);adj[v].add(u)
        if u>v:h[u]+=1;h[v]-=1
    a=om[0];out=[]
    for u,v in map(sorted,unit['edges']):
        C={u};todo=[u]
        for w in todo:
            for z in adj[w]:
                if {w,z}=={u,v}:continue
                if z not in C:C.add(z);todo.append(z)
        q=tuple(sum(om[w][i]for w in C)for i in range(4));H=sum(h[w]for w in C)
        out.extend(tuple(q[i]+j*a[i]for i in range(4))for j in(H,H+1))
    return out,tuple(-z for z in a)

def main():
    start=time.monotonic();base=[(-1,-1,-1,-1)]+[tuple(int(i==j)for i in range(4))for j in range(4)];target,nt=functional(base);assert target==-864;records=[]
    print('target',target,flush=True)
    for U in STARS:
        values=[];counts=[]
        for negative in range(5):
            om=[None]*5;om[negative]=base[0]
            for i,v in enumerate(x for x in range(5)if x!=negative):om[v]=base[i+1]
            F,b=factors_rooted(U,om);value,count=functional(F,b);F2,b2=factors_normalized(U,om);other,_=functional(F2,b2);assert value==other;values.append(value);counts.append(count)
        full=24*sum(values);records.append({'unit':U,'apex_placement_values':list(map(str,values)),'full_S5_value':str(full),'moment_monomials':counts,'normalized_head_control':True});print('star',U,'value',full,flush=True)
    assert target and any(fmpq(r['full_S5_value'])for r in records)
    out={'status':'EXACT_ACTUAL_VANDERMONDE_SQUARE_REFUTATION','arity':5,'operator':'Delta(partial)^2 on R(-sum x,x), at x=(1,1,1,1)','target_value':str(target),'target_moment_monomials':nt,'stars':records,'scope':'The operator is well-defined on kernels analytic at this point, including the target and this star in every apex placement. It does not annihilate this matching-deficient star, so any extension to the full rational space still fails. This refutes the naive doubled Vandermonde bridge on the tree kernels themselves, not every operator on the sheared product.','seconds':time.monotonic()-start};Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print('seconds',out['seconds'],flush=True)
if __name__=='__main__':main()
