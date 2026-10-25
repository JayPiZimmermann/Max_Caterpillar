"""Exact N5 star gate for the leading twisted-periodization pole.

Keep omega_0=1, put omega_i=k_i+t*p_i, sum k_i=-1 and sum p_i=0.
Weight by (-1)^(k_1+k_2), and extract t^-3. The finite state formula
includes every apex placement. No numerical lattice truncation is used.
"""
from pathlib import Path
from collections import Counter
from fractions import Fraction as Q
import itertools,json,math,sys,time
import sympy as S
sys.path.append(str(Path('research/sN/dfs/h5-growth/venv/lib/python3.12/site-packages')))
from flint import fmpq,fmpq_mat
from dfs_review_fourier import family
HERE=Path(__file__).parent

def tree_data(U):
    adj={v:[]for v in range(1,5)}
    for u,v in U['edges']:adj[u].append(v);adj[v].append(u)
    root=U['root'];par={root:None};todo=[root]
    for v in todo:
        for w in adj[v]:
            if w!=par[v]:par[w]=v;todo.append(w)
    children={v:[w for w in adj[v]if par.get(w)==v]for v in adj};verts=todo[1:];E=set(map(tuple,U['edges']));eps=[1 if(v,par[v])in E else -1 for v in verts];cuts=[]
    for v in verts:
        C={v};queue=[v]
        for w in queue:C.update(children[w]);queue.extend(children[w])
        cuts.append(C)
    return root,par,children,verts,eps,cuts

def compiled(U):
    root,par,children,verts,eps,cuts=tree_data(U);terms=Counter();raw=0
    pbase=[(0,0,0),(1,0,0),(0,1,0),(0,0,1),(-1,-1,-1)]
    def add(weight,num,den):
        nonlocal raw
        raw+=1
        if num is not None:
            g=math.gcd(*num)
            if not g:return
            if next(v for v in num if v)<0:g=-g
            num=tuple(v//g for v in num);weight*=g
        ds=[]
        for f in den:
            g=math.gcd(*f);assert g
            if next(v for v in f if v)<0:g=-g
            ds.append(tuple(v//g for v in f));weight/=g
        terms[(num,tuple(sorted(ds)))]+=weight
    for perm in itertools.permutations(range(5)):
        v0=perm.index(0);pn=[pbase[perm[v]]for v in range(5)];pa=pn[0];qs=[tuple(sum(pn[v][i]for v in C)for i in range(3))for C in cuts]
        def reconstruct(a,q):
            w=[0]*5;w[0]=a;edgeq={v:q[i]for i,v in enumerate(verts)}
            for v in range(1,5):w[v]=(edgeq[v]if v!=root else -a)-sum(edgeq[c]for c in children[v])
            return w
        def character(w):return -1 if sum(w[v]for v in range(5)if perm[v]in(1,2))%2 else 1
        for a in(-1,1):
            for delta in itertools.product((0,1),repeat=3):
                q=[-d*e*a for d,e in zip(delta,eps)];w=reconstruct(a,q)
                if w[v0]!=1:continue
                den=[tuple(qs[j][i]+delta[j]*eps[j]*pa[i]for i in range(3))for j in range(3)]
                weight=Q(character(w)*(-1)**(1+sum(delta))*math.prod(eps));add(weight,None,den)
        if v0:
            for j,v in enumerate(verts):
                if v0==v:c=1
                elif v0==par[v]:c=-1
                else:continue
                q=[0]*3;q[j]=c;w=reconstruct(0,q);assert w[v0]==1
                den=[]
                for k in range(3):
                    if k!=j:den.extend([qs[k],tuple(qs[k][i]+eps[k]*pa[i]for i in range(3))])
                add(Q(character(w)),tuple(-z for z in pa),den)
    return {k:v for k,v in terms.items()if v},raw

def evaluate(terms,point):
    total=Q(0)
    for (num,den),c in terms.items():
        numer=1 if num is None else sum(x*y for x,y in zip(num,point));div=math.prod(sum(x*y for x,y in zip(f,point))for f in den)
        if not div:raise ValueError('normal pole')
        total+=c*Q(numer,div)
    return total

def main():
    start=time.monotonic();units=family(5,'nopath');compiled_units=[compiled(u)for u in units];print('compiled',len(units),'raw',[r for t,r in compiled_units],'terms',[len(t)for t,r in compiled_units],flush=True);points=[];rows=[]
    for x,y in itertools.product(range(2,13),range(2,13)):
        p=(1,x,y)
        try:row=[evaluate(t,p)for t,r in compiled_units]
        except ValueError:continue
        pp=(1,x,y,-1-x-y);target=Q(2*(pp[0]+pp[1]),math.prod(pp));points.append(p);rows.append(row+[target])
        if len(rows)>=40:break
    A=fmpq_mat([[fmpq(str(v))for v in row]for row in rows]);R,rank=A.rref();B=fmpq_mat([[fmpq(str(v))for v in row[:-1]]for row in rows]);_,bad_rank=B.rref();out={'status':'EXACT_N5_LEADING_TWISTED_PERIODIZATION_GATE','units':units,'points':points,'rows':[[str(x)for x in row]for row in rows],'ranks':[bad_rank,rank],'terms':[[{'weight':str(v),'numerator':num,'denominators':den}for(num,den),v in t.items()]for t,r in compiled_units],'raw_states':[r for t,r in compiled_units]}
    M=S.Matrix(rows).applyfunc(S.Rational)
    if rank==bad_rank:
        coeff,pars=M[:,:-1].gauss_jordan_solve(M[:,-1]);coeff=coeff.subs({p:0 for p in pars});out['sampled_target_expansion']=list(map(str,coeff))
    else:
        w=next(v for v in M[:,:-1].T.nullspace()if(v.T*M[:,-1])[0]);w/=((w.T*M[:,-1])[0]);out['exact_grid_separator']=list(map(str,w))
    out['seconds']=time.monotonic()-start;out['scope']='Exact finite evaluation gate. A no-gap expansion still requires a symbolic rational identity check. A positive grid separator is an actual combination of leading-coefficient operations once the analytic finite-state reduction is justified.';Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print('ranks',out['ranks'],'seconds',out['seconds'],out.get('sampled_target_expansion','gap'),flush=True)
if __name__=='__main__':main()
