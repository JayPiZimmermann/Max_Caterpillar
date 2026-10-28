"""Extract exact curvature-cancelling triples, then free every pair coefficient.

Finite pattern exploration only; no general negative conclusion. The output
of every successful continuous LP is independently checked globally.
"""
import argparse,hashlib,itertools,json,math,signal,time
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
import sympy as sp
from scipy.sparse import load_npz
from overnight_fixed_fullpair_dictionary import SETS,SID,PERMS,FEATURE,primitive
from overnight_fixed_fullpair_pattern import EDGES,network
from overnight_fixed_cross_pattern import refine
from overnight_fixed_cross_verify import check

PERMIX=[[SID[sum(1<<p[i]for i in range(5)if s>>i&1)]for s in SETS]for p in PERMS]
TRANSFORMS={}
GLOBAL_IDS={}

def orbit_key(vectors,weights):
    # Cache all symmetry images once per form; compare only integer IDs.
    # Global positive output scaling can be absorbed into the refined forms.
    den=math.lcm(*(d.denominator for d in weights));ww=[int(d*den)for d in weights];common=math.gcd(*ww);ww=[d//common for d in ww]
    images=[]
    for raw in vectors:
        v=tuple(map(int,raw))
        if v not in TRANSFORMS:
            out=[]
            for ix in PERMIX:
                vv=primitive([v[i]for i in ix])
                if vv not in GLOBAL_IDS:GLOBAL_IDS[vv]=len(GLOBAL_IDS)
                out.append(GLOBAL_IDS[vv])
            TRANSFORMS[v]=out
        images.append(TRANSFORMS[v])
    return min(tuple(sorted((im[k],d)for im,d in zip(images,ww)))for k in range(120))


def enumerate_cores(V,A):
    A=A[:-16].tocsc();m=len(V);curves=[{int(i):int(v)for i,v in zip(A.indices[A.indptr[j]:A.indptr[j+1]],A.data[A.indptr[j]:A.indptr[j+1]])}for j in range(m)];sets=[frozenset(c)for c in curves];nonzero=[j for j in range(m)if sets[j]];zero=[j for j in range(m)if not sets[j]];seen=set();cores=[]
    for c in nonzero:
        rows=sorted(sets[c]);eligible=[j for j in nonzero if j!=c and sets[j]<=sets[c]];groups={};parallel=[]
        for j in eligible:
            ratio=tuple(Q(curves[j].get(r,0),curves[c][r])for r in rows);base=ratio[0];diff=[x-base for x in ratio];scale=next((x for x in diff if x),None)
            if scale is None:parallel.append((j,base));continue
            normalized=tuple(x/scale for x in diff);groups.setdefault(normalized,[]).append((j,base,scale))
        proposals=[]
        for group in groups.values():
            for (a,x,t),(b,y,s)in itertools.combinations(group,2):
                det=x*s-y*t
                if not det:continue
                la=s/det;lb=-t/det
                if la>0 and lb>0:proposals.append(([a,b,c],[la,lb,Q(-1)]))
        for (a,x),(b,y)in itertools.combinations(parallel,2):proposals.append(([a,b,c],[1/(2*x),1/(2*y),Q(-1)]))
        # One cancellation pair plus a non-crossing form; its magnitude may
        # move under coefficient refinement, so choose one initial magnitude.
        for a,x in parallel:
            for b in zero:
                for sg in(1,-1):proposals.append(([a,b,c],[1/x,Q(sg),Q(-1)]))
        for ids,weights in proposals:
            key=orbit_key([V[i]for i in ids],weights)
            if key in seen:continue
            seen.add(key);cores.append((ids,weights))
    return cores,zero


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--source',default='overnight_fixed_fullpair_dictionary_1');ap.add_argument('--budget',type=int,default=240);args=ap.parse_args();start=time.monotonic();V=np.load(args.source+'_values.npz')['values'];A=load_npz(args.source+'_matrix.npz');cores,zero=enumerate_cores(V,A);prefix=args.source+'_cores'
    print(json.dumps({'stage':'CORES_READY','cores':len(cores),'noncrossing_forms':len(zero),'seconds':time.monotonic()-start}),flush=True)
    # Initial locality coverage is only an ordering heuristic, never a theorem.
    top=[s for s in SETS if s.bit_count()==3];events=[(SID[s],SID[s|(1<<i)])for s in top for i in range(5)if not s>>i&1]
    def score(core):
        ids,_=core;return sum(any(V[j,a]==V[j,b]==0 for j in ids)for a,b in events)
    cores.sort(key=score,reverse=True);F=sp.Matrix(FEATURE.tolist());ids=[i for i,s in enumerate(SETS)if s.bit_count()>=3][:14];inv=sp.Matrix(F[ids,:]).inv();coefficients={}
    records=[];found=False;signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('declared budget')));signal.alarm(args.budget)
    try:
        for number,(ids0,dd)in enumerate(cores):
            for j in ids0:
                if j not in coefficients:coefficients[j]=list(map(str,inv*sp.Matrix([int(V[j,i])for i in ids])))
            for flip in(1,-1):
                candidate={'first_layer_edges':EDGES,'outer_forms':[coefficients[j]for j in ids0],'output':[str(flip*d)for d in dd]};r=refine(candidate,[0,1,2]);records.append({'core':number,'indices':ids0,'weights':[str(flip*d)for d in dd],'initial_coverage':score((ids0,dd)),**{k:v for k,v in r.items()if k!='candidate'}})
                if'candidate'in r:
                    path=Path(prefix+'_net.json');path.write_text(json.dumps(network(r['candidate']),indent=2)+'\n');receipt=check(path);Path(prefix+'_check.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n');found=True;break
            if number%20==0 or found:print(json.dumps({'stage':'REFINEMENT','core':number,'cases':len(records),'found':found,'seconds':time.monotonic()-start}),flush=True)
            if found:break
    except TimeoutError:print('DECLARED_BUDGET_REACHED',flush=True)
    finally:signal.alarm(0)
    result={'status':'EXACT_MATCHED_SIXTEEN_FIVE_CONSTRUCTION'if found else'FINITE_CORE_PATTERN_SEARCH_INCOMPLETE','total_cores':len(cores),'records':records,'seconds':time.monotonic()-start,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};Path(prefix+'.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k!='records'}),flush=True)

if __name__=='__main__':main()
