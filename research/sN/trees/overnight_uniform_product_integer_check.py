"""Independent exact refutation of the whole N5 leading periodized curve.

Enumerate integer frequency points and all permutations directly, using
normalized heads. Do not import the producer's cut endpoint classification.
Check the resulting rational identity over Q(r,s), not at sampled normals.
"""
from pathlib import Path
from collections import Counter
from fractions import Fraction as Q
import itertools,json,math,sys,time
sys.path.append(str(Path('research/sN/dfs/h5-growth/venv/lib/python3.12/site-packages')))
from flint import fmpq,fmpq_mpoly_ctx

def normalized_factors():
    U={'root':1,'edges':[(2,1),(3,2),(4,2)]};h=[-1,1,0,0,0];adj=[set()for _ in range(5)]
    for u,v in U['edges']:
        adj[u].add(v);adj[v].add(u)
        if u>v:h[u]+=1;h[v]-=1
    out=[]
    for u,v in map(sorted,U['edges']):
        C={u};todo=[u]
        for x in todo:
            for y in adj[x]:
                if {x,y}=={u,v}:continue
                if y not in C:C.add(y);todo.append(y)
        H=sum(h[x]for x in C)
        for j in(H,H+1):out.append(tuple(int(v in C)+j*int(v==0)for v in range(5)))
    return U,out

def main():
    start=time.monotonic();U,F=normalized_factors();norm=[(0,0,0),(1,0,0),(0,1,0),(0,0,1),(-1,-1,-1)];prepared=[]
    for p in itertools.permutations(range(5)):
        factors=[]
        for f in F:
            ff=[0]*5
            for i,c in enumerate(f):ff[p[i]]+=c
            factors.append((tuple(ff),tuple(sum(ff[v]*norm[v][i]for v in range(5))for i in range(3))))
        prepared.append((p[0],norm[p[0]],factors))
    terms=Counter();critical=0;lattice=0;max_coordinate=0
    def add(c,num,den):
        if num is not None:
            g=math.gcd(*num);assert g
            if next(x for x in num if x)<0:g=-g
            num=tuple(x//g for x in num);c*=g
        ds=[]
        for f in den:
            g=math.gcd(*f);assert g
            if next(x for x in f if x)<0:g=-g
            ds.append(tuple(x//g for x in f));c/=g
        terms[(num,tuple(sorted(ds)))]+=c
    for ks in itertools.product(range(-4,5),repeat=3):
        last=-1-sum(ks)
        if not -4<=last<=4:continue
        w=(1,)+ks+(last,);lattice+=1;sgn=-1 if (w[1]+w[2])%2 else 1
        for apex,pa,fs in prepared:
            a=w[apex];zero=[];nonzero=1
            for f,fn in fs:
                val=sum(x*y for x,y in zip(f,w))
                if val:nonzero*=val
                else:zero.append(fn)
            order=len(zero)-(a==0);assert order<=3
            if order!=3:continue
            critical+=1;max_coordinate=max(max_coordinate,max(map(abs,w)))
            if a:add(Q(-sgn*a,nonzero),None,zero)
            else:add(Q(sgn,nonzero),tuple(-x for x in pa),zero)
    terms={k:v for k,v in terms.items()if v};assert critical==720;assert max_coordinate<=3
    # Subtract12 times the maximum coefficient 2(p1+p2)/product p_i.
    terms[((1,1,0),((1,0,0),(0,1,0),(0,0,1),(-1,-1,-1)))]=terms.get(((1,1,0),((1,0,0),(0,1,0),(0,0,1),(-1,-1,-1))),Q(0))-24
    union=Counter()
    for num,den in terms:union|=Counter(den)
    ctx=fmpq_mpoly_ctx.get(('r','s'));r,s=ctx.gens();lin=lambda f:ctx.constant(f[0])+f[1]*r+f[2]*s;P={f:lin(f)for f in union};D=ctx.constant(1)
    for f,k in union.items():D*=P[f]**k
    numerator=ctx.constant(0)
    for (num,den),c in terms.items():
        term=D
        for f in den:term=term/P[f]
        numerator+=fmpq(c.numerator,c.denominator)*term*(lin(num)if num is not None else 1)
    assert numerator.is_zero()
    out={'status':'INDEPENDENT_EXACT_LEADING_PERIODIZED_STAR_OBSTRUCTION','unit':U,'lattice_box':[-4,4],'lattice_points':lattice,'label_permutations':120,'critical_states':critical,'maximum_absolute_integer_coordinate':max_coordinate,'identity':'Leading_B,p(F_star)=12 Leading_B,p(R_max)','normal_parameters':'p=(1,r,s,-1-r-s)','normal_subset':[1,2],'common_denominator_degree':int(D.total_degree()),'all_normal_identity':True,'scope':'The entire leading normal coefficient already contains the maximum in the span of one oriented star. Any linear postprocessing of this leading curve therefore fails. The convergence and finite-state completeness argument is recorded in the periodization note.','seconds':time.monotonic()-start};Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
