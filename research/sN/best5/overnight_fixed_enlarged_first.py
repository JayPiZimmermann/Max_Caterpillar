"""Try three free neurons after adding all original crease hyperplanes.

Every ray of the central first-layer arrangement is enumerated exactly
from triples of independent normals in the four-dimensional quotient.
The old outer forms have no interior zero inside this arrangement. Their
signs determine a continuous pattern refinement LP over all new features.
"""
import argparse,hashlib,itertools,json,math,time
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from overnight_fixed_fullpair_pattern import EDGES
from overnight_fixed_fullpair_dictionary import primitive


def det3(a):return a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])-a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])+a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0])

def rays(first):
    hyperplanes=sorted({primitive(row)for row in first});directions=set()
    for selected in itertools.combinations(hyperplanes,3):
        rows=[h[1:]for h in selected];v=[(-1)**j*det3([[a[i]for i in range(4)if i!=j]for a in rows])for j in range(4)];p=primitive(v)
        if p:directions.add(p)
    return [(0,)+tuple(s*c for c in p)for p in sorted(directions)for s in(1,-1)]


def refine(first,initial,output,target=None):
    X=np.asarray(rays(first),dtype=np.int64);Phi=np.maximum(X@np.asarray(first,dtype=np.int64).T,0);nf=len(first);K=len(initial);G=Phi@np.asarray(initial,dtype=float).T;E=np.hstack([Phi]+[Phi*(G[:,j:j+1]>0)*int(output[j])for j in range(K)]);b=np.max(X,axis=1)if target is None else target;I=[];Z=[]
    for q,row in enumerate(Phi):
        for j in range(K):
            block=[0]*(nf*(K+1));block[nf*(j+1):nf*(j+2)]=list(row)
            if G[q,j]==0:Z.append(block)
            else:I.append([-int(np.sign(G[q,j]))*int(c)for c in block])
    if Z:E=np.r_[E,np.asarray(Z)];b=np.r_[b,np.zeros(len(Z))]
    r=linprog(np.zeros(nf*(K+1)),A_eq=E,b_eq=b,A_ub=np.asarray(I),b_ub=np.zeros(len(I)),bounds=[(None,None)]*(nf*(K+1)),method='highs')
    report={'solver_status':r.status,'message':r.message,'rays':len(X),'equations':len(E),'inequalities':len(I),'free_width':K,'first_features':nf}
    if r.x is not None:
        x=[Q(float(c)).limit_denominator(1000000)for c in r.x]
        assert all(sum(Q(int(c))*v for c,v in zip(row,x))==Q(float(rhs)).limit_denominator(1000000)for row,rhs in zip(E,b))
        assert all(sum(Q(int(c))*v for c,v in zip(row,x))<=0 for row in I)
        report['candidate']={'first_layer':first,'remainder':list(map(str,x[:nf])),'outer_forms':[list(map(str,x[nf*(j+1):nf*(j+2)]))for j in range(K)],'output':list(map(str,output)),'initial_forms':[list(map(str,w))for w in initial]}
    return report


def network(c):
    first=c['first_layer']+[[1,0,0,0,0],[-1,0,0,0,0]];r=list(map(Q,c['remainder']));W=[list(map(str,r))+['1','-1'],list(map(str,[-v for v in r]))+['-1','1']];W.extend(row+['0','0']for row in c['outer_forms']);return{'N':5,'first_layer':first,'second_layer':W,'output':['1','-1']+c['output']}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--pool',type=int,default=0);args=ap.parse_args();start=time.monotonic();prefix=f'overnight_fixed_enlarged_first_{args.pool}';known=json.loads(Path('overnight_fixed_fullpair_pattern_control_net.json').read_text());new=np.load('overnight_fixed_nonpair_remainder_0_dictionary.npz')['normals'].tolist();first=known['first_layer'][:14]+new;initial=[list(map(Q,row[:14]))+[Q(0)]*len(new)for row in known['second_layer'][2:]];output=list(map(int,known['output'][2:]));positive=refine(first,initial,output);assert'candidate'in positive;Path(prefix+'_control_candidate.json').write_text(json.dumps(positive['candidate'],indent=2)+'\n');records=[];found=False
    for keep in itertools.combinations(range(4),3):
        r=refine(first,[initial[j]for j in keep],[output[j]for j in keep]);record={'keep':list(keep),**{k:v for k,v in r.items()if k!='candidate'}};records.append(record);print(json.dumps(record),flush=True)
        if'candidate'in r:
            Path(prefix+'_candidate.json').write_text(json.dumps(r['candidate'],indent=2)+'\n');Path(prefix+'_net.json').write_text(json.dumps(network(r['candidate']),indent=2)+'\n');found=True;break
    result={'status':'RATIONAL_CANDIDATE_REQUIRES_INDEPENDENT_CHECK'if found else'FOUR_DELETION_PATTERNS_INFEASIBLE','records':records,'positive_control':{k:v for k,v in positive.items()if k!='candidate'},'seconds':time.monotonic()-start,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};Path(prefix+'.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k!='records'}),flush=True)

if __name__=='__main__':main()
