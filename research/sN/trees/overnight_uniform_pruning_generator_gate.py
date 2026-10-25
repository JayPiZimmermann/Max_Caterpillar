"""Exact small gate for a relative-kernel leaf-grafting operation.

Fixed-apex S4 identities at N5 lift to full S9 identities after grafting a
leaf at each old nonapex vertex. This tests the sparse score on a genuine
relative generating operation, without a generic N9 rank computation.
"""
from pathlib import Path
from fractions import Fraction as Q
import itertools,json,time,sys
import sympy as S
sys.path.append(str(Path('research/sN/dfs/h5-growth/venv/lib/python3.12/site-packages')))
from flint import fmpq,fmpq_mat
from dfs_review_fourier import family,points
from overnight_uniform_pruning_candidate_target import score
HERE=Path(__file__).parent

def fixed(unit,point):
    a=point[0];total=Q(0)
    for p in itertools.permutations(point[1:]):
        om=[a]+list(p);den=1
        for C,eps in unit['cuts']:
            q=sum(om[v]for v in C);den*=q*(q+eps*a)
        total+=Q(-a,den)
    return total

def main():
    start=time.monotonic();units=family(5,'all');pts=list(points(5,24));rows=[[fixed(u,p)for u in units]for p in pts]
    (HERE/'overnight_uniform_pruning_generator_gate_rows.json').write_text(json.dumps({'units':units,'points':pts,'rows':[[str(x)for x in row]for row in rows]},indent=2)+'\n');print('exact rows complete',time.monotonic()-start,flush=True)
    R,rank=fmpq_mat([[fmpq(str(x))for x in row]for row in rows]).rref();piv=[next(j for j in range(26)if R[i,j])for i in range(rank)];null=[]
    for j in range(26):
        if j in piv:continue
        v=S.zeros(26,1);v[j]=1
        for i,k in enumerate(piv):v[k]=-S.Rational(str(R[i,j]))
        null.append(v)
    result={'status':'EXACT_RELATIVE_GRAFT_SCORE_GATE','source_arity':5,'target_arity':9,'source_rank':rank,'units':units,'points':pts,'rows':[[str(x)for x in row]for row in rows],'grafts':{},'benchmark_note':'Initial SymPy elimination was stopped after69 seconds; this run uses FLINT exact rational RREF and preserves rows before elimination.'}
    for eps in(-1,1):
        lifted=[{'root':u['root'],'edges':list(u['edges'])+[(v+4,v)if eps==1 else(v,v+4)for v in range(1,5)]}for u in units];values=S.Matrix([score(u)for u in lifted]);bad=[v for v in null if(values.T*v)[0]];entry={'lifted_units':lifted,'score':list(map(str,values)),'sampled_relations_violated':len(bad)}
        if bad:
            v=min(bad,key=lambda v:sum(bool(x)for x in v));entry['relation']=list(map(str,v));entry['score_pairing']=str((values.T*v)[0]);print('eps',eps,'violation',[(i,str(x))for i,x in enumerate(v)if x],entry['score_pairing'],flush=True)
        else:print('eps',eps,'PASS finite source relation gate',flush=True)
        result['grafts'][str(eps)]=entry
    for k in(1,2,3):
        values=[]
        for u in units:
            total=Q(0)
            for positive in itertools.combinations(range(1,5),k):
                total+=score({'root':u['root'],'edges':list(u['edges'])+[(v+4,v)if v in positive else(v,v+4)for v in range(1,5)]})
            values.append(total)
        values=S.Matrix(values);bad=[v for v in null if(values.T*v)[0]];entry={'score_sum':list(map(str,values)),'sampled_relations_violated':len(bad)}
        if bad:
            v=min(bad,key=lambda v:sum(bool(x)for x in v));entry['relation']=list(map(str,v));entry['score_pairing']=str((values.T*v)[0]);print('mixed positives',k,'violation',[(i,str(x))for i,x in enumerate(v)if x],entry['score_pairing'],flush=True)
        else:print('mixed positives',k,'PASS finite source relation gate',flush=True)
        result['grafts']['mixed_'+str(k)]=entry
    for bits in itertools.product((-1,1),repeat=4):
        values=[]
        for u in units:
            total=Q(0)
            for v in range(1,5):
                path=[v,5,6,7,8];edges=list(u['edges'])+[(b,a)if eps==1 else(a,b)for a,b,eps in zip(path,path[1:],bits)]
                total+=score({'root':u['root'],'edges':edges})
            values.append(total)
        values=S.Matrix(values);bad=[v for v in null if(values.T*v)[0]];entry={'relative_signs':bits,'score_sum':list(map(str,values)),'sampled_relations_violated':len(bad)}
        if bad:
            v=min(bad,key=lambda v:sum(bool(x)for x in v));entry['relation']=list(map(str,v));entry['score_pairing']=str((values.T*v)[0]);print('path graft',bits,'violation',[(i,str(x))for i,x in enumerate(v)if x],entry['score_pairing'],flush=True)
        result['grafts']['path_'+''.join('p'if x==1 else'm'for x in bits)]=entry
    result['seconds']=time.monotonic()-start;result['scope']='A failed sampled source relation still requires exact all-frequency verification at N5. Once verified, the explicit grafting map makes the induced N9 obstruction exact.';Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print('rank',result['source_rank'],'seconds',result['seconds'],flush=True)
if __name__=='__main__':main()
