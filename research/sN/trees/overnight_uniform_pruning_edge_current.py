"""Small exact/modular gates for a head-compatible odd-tree current score.

The candidate is Q_H=J_a sum_v outdeg_B(v) J_v on a canonical leaf head.
Head exchange is automatic, but rational-kernel descent is a separate test.
No new Fourier evaluations are generated: saved exact N5 and modular N7 rows
are reused, and their status is preserved explicitly.
"""
from pathlib import Path
import itertools,json,sys,time
import numpy as np
import networkx as nx
import sympy as S
sys.path.append(str(Path('research/sN/dfs/h5-growth/venv/lib/python3.12/site-packages')))
from flint import fmpq,fmpq_mat
from overnight_uniform_pruning_signbalance import extensions
from overnight_uniform_pruning_signed7 import reduce
HERE=Path(__file__).parent

def signed_roots(G):
    n=len(G);ans=[]
    for r in range(n):
        parent={r:None};todo=[r];edges=[]
        for v in todo:
            for w in G[v]:
                if w!=parent[v]:parent[w]=v;todo.append(w);edges.append((v,w))
        ans.append(extensions(n,edges)[1])
    assert sum(ans)==0
    return ans

def score(unit):
    E=[tuple(e)for e in unit['edges']]+[(unit['root'],0)]
    G=nx.Graph(E);J=signed_roots(G);k=[0]*len(G)
    for u,v in E:k[u]+=1
    return J[0]*sum(x*y for x,y in zip(k,J)),{'J':J,'outdegree':k}

def main():
    start=time.monotonic();data=json.loads((HERE/'overnight_uniform_pruning_signed_gate.json').read_text());units=data['units'];rows=data['rows'];qmeta=[score(u)for u in units];values=[q for q,m in qmeta]
    M=fmpq_mat([[fmpq(x)for x in row[:-1]]for row in rows]);R,rank=M.rref();piv=[next(j for j in range(len(units))if R[i,j])for i in range(rank)];null=[]
    for j in range(len(units)):
        if j in piv:continue
        v=[S.Rational(0)]*len(units);v[j]=1
        for i,k in enumerate(piv):v[k]=-S.Rational(str(R[i,j]))
        pairing=sum(x*y for x,y in zip(v,values))
        if pairing:null.append((sum(bool(x)for x in v),v,pairing))
    result={'status':'HEAD_COMPATIBLE_CURRENT_DESCENT_GATE','formula':'J_apex * sum_v outdegree_B(v) J_v','N5':{'exact_grid_rank':rank,'score_compatible_with_exact_grid':not null,'values':values,'metadata':[m for q,m in qmeta]}}
    if null:
        _,v,pairing=min(null,key=lambda x:x[0]);result['N5']['violated_grid_relation']={str(i):str(x)for i,x in enumerate(v)if x};result['N5']['pairing']=str(pairing)
    else:
        A=S.Matrix(rows).applyfunc(S.Rational);w,pars=A[:,:-1].T.gauss_jordan_solve(S.Matrix(values));w=w.subs({p:0 for p in pars});result['N5']['exact_evaluation_weights']=list(map(str,w));result['N5']['target_response']=str((w.T*A[:,-1])[0])
    # A previously independently proved all-frequency relation is an immediate
    # exact descent refutation if its score pairing is nonzero.
    relation={3:-3,16:1};result['N5']['previous_exact_identity_pairing']=sum(values[i]*w for i,w in relation.items())
    print('N5',result['N5']['score_compatible_with_exact_grid'],'known exact pairing',result['N5']['previous_exact_identity_pairing'],flush=True)
    saved=json.loads((HERE/'overnight_uniform_pruning_signed7.json').read_text());p=saved['prime'];units7=saved['units'];A=np.fromfile(HERE/'overnight_uniform_pruning_signed7.u32',dtype='<u4').reshape(saved['rows'],len(units7)+1).astype(np.int64);basis={}
    for row in A:
        v=reduce(row,basis,p);nz=np.flatnonzero(v[:-1])
        if len(nz):j=int(nz[0]);basis[j]=v*pow(int(v[j]),-1,p)%p
        else:assert v[-1]==0
    values7=[score(u)[0]for u in units7];rem=reduce(values7+[0],basis,p);result['N7']={'status':'MODULAR_ONLY','prime':p,'rows':len(A),'rank':len(basis),'score_compatible_with_sampled_rowspan':bool(np.all(rem[:-1]==0)),'target_response_if_compatible':int(-rem[-1]%p),'values':values7}
    result['seconds']=time.monotonic()-start;result['scope']='Head-exchange compatibility alone does not prove descent. A failed finite relation is not a rational identity unless separately checked; the named prior exact identity already has an independent polynomial check.';Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print('N7',result['N7']['score_compatible_with_sampled_rowspan'],'seconds',result['seconds'],flush=True)
if __name__=='__main__':main()
