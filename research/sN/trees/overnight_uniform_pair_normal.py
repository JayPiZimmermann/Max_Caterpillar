"""Exact finite gate varying paired-collision NORMAL directions at five labels.

This is distinct from evaluating/combining the already refuted fixed-normal
residue curve. Base=(0,1,-1,z,-z), normal=(-2(p+q),p,p,q,q), p=1.
All arithmetic is Fraction; exact row ranks and separator (if any) use SymPy.
Finite success would still not be a uniform all-arity matching theorem.
"""
from pathlib import Path
from fractions import Fraction
import itertools,json,math,time
import sympy as S
from dfs_review_fourier import family
from overnight_lower_pairlimit import coeff_minus_one

def main():
    start=time.monotonic();fam=family(5,'nopath');perms=list(itertools.permutations(range(5)));rows=[];points=[]
    # z=2 creates extra q-a=0 resonances; keep the generic paired stratum.
    for z,q in itertools.product(range(3,10),range(1,8)):
        base=[0,1,-1,z,-z];normal=[-2*(1+q),1,1,q,q]
        row=[sum(coeff_minus_one(u,[base[i] for i in p],[normal[i] for i in p]) for p in perms) for u in fam]
        target=Fraction(1,normal[0]*z*z);rows.append(row+[target]);points.append({'z':z,'q':q})
    A=S.Matrix(rows);ranks=[A[:,:-1].rank(),A.rank()]
    result={'arity':5,'ranks':ranks,'points':points,'rows':[[str(v) for v in r] for r in rows],
            'representatives':fam,'seconds':time.monotonic()-start}
    if ranks[0]<ranks[1]:
        v=next(v for v in A[:,:-1].T.nullspace() if (v.T*A[:,-1])[0]!=0);v=v/(v.T*A[:,-1])[0]
        assert v.T*A[:,:-1]==S.zeros(1,len(fam)) and (v.T*A[:,-1])[0]==1
        result['status']='EXACT_GENERIC_NORMAL_PAIRED_RESIDUE_SEPARATOR';result['weights']=list(map(str,v))
    else:
        sol,params=A[:,:-1].gauss_jordan_solve(A[:,-1]);sol=sol.subs({p:0 for p in params})
        result['status']='NO_SEPARATION_IN_EXACT_NORMAL_GRID';result['target_combination']=list(map(str,sol))
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(result['status'],ranks,result['seconds'],flush=True)

if __name__=='__main__':main()
