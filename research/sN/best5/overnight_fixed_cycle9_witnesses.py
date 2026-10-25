"""Turn every failed orientation into two explicit indistinguishable inputs."""
from fractions import Fraction as Q
from itertools import permutations
from pathlib import Path
import json,hashlib,time
from overnight_fixed_bowtie_verify import rref
HERE=Path(__file__).resolve().parent


def main():
    start=time.monotonic();inventory=json.loads((HERE/'overnight_fixed_cycle9_orientations.json').read_text());out=[]
    for rec in inventory['results']:
        edges=rec['edges'];w=rec['witness']
        if w is None:out.append({'orientation':rec['orientation'],'edges':edges,'status':'GLOBAL_FEATURE_FACTORISATION','vertex1_anchor':0 if(1,0)in map(tuple,edges)else 2});continue
        B=[list(map(Q,row))for row in w['active_rows']];rr=rref(B);piv=[next(i for i,v in enumerate(row)if v)for row in rr];top=w['possible_maximum'];target=[Q(i==top)-Q(i==0)for i in range(5)];direction=None
        for j in range(5):
            if j in piv:continue
            v=[Q(i==j)for i in range(5)]
            for p,row in zip(piv,rr):v[p]=-row[j]
            if sum(x*y for x,y in zip(target,v)):
                direction=[x-v[0]for x in v];break
        assert direction is not None and direction[0]==direction[2]==0;perm=next(p for p in permutations(range(5))if p[0]==top and tuple(p.index(i)<p.index(j)for i,j in edges)==tuple(w['cell']));x=[Q(4-perm.index(i))for i in range(5)];M=max(abs(direction[i]-direction[j])for i in range(5)for j in range(5));eps=1/(2*(M+1));y=[a+eps*v for a,v in zip(x,direction)]
        def features(z):return[max(z[i]-z[j],Q(0))for i,j in edges]+[max(s*z[i],Q(0))for i in(0,2)for s in(1,-1)]
        assert features(x)==features(y)and max(x)!=max(y);out.append({'orientation':rec['orientation'],'edges':edges,'status':'EXACT_IDENTICAL_FIRST_LAYER_DIFFERENT_MAX','x':list(map(str,x)),'y':list(map(str,y))})
    result={'status':'COMPLETE_CYCLE9_ORIENTATION_WITNESSES','results':out,'seconds':time.monotonic()-start,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};(HERE/'overnight_fixed_cycle9_witnesses.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print('COMPLETE',len(out),'seconds',time.monotonic()-start)
if __name__=='__main__':main()
