"""Independent exact full32-orientation gate, using only explicit inputs."""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json,hashlib,time


def main():
    start=time.monotonic();here=Path(__file__).parent;path=here/'overnight_fixed_cycle9_witnesses.json';data=json.loads(path.read_text());base=[(0,1),(1,2),(2,3),(3,4),(4,0)];seen=set();bad=good=0
    for rec in data['results']:
        s=tuple(rec['orientation']);assert s not in seen and len(s)==5 and all(x in(-1,1)for x in s);seen.add(s);edges=[(i,j)if d>0 else(j,i)for(i,j),d in zip(base,s)];assert edges==list(map(tuple,rec['edges']))
        if rec['status']=='EXACT_IDENTICAL_FIRST_LAYER_DIFFERENT_MAX':
            x=list(map(Q,rec['x']));y=list(map(Q,rec['y']));assert len(x)==len(y)==5
            def features(z):return[max(z[i]-z[j],Q(0))for i,j in edges]+[max(d*z[i],Q(0))for i in(0,2)for d in(1,-1)]
            assert features(x)==features(y)and max(x)!=max(y);bad+=1
        else:
            assert rec['status']=='GLOBAL_FEATURE_FACTORISATION';anchor=rec['vertex1_anchor'];assert anchor in(0,2)and(1,anchor)in edges and(3,2)in edges and(4,0)in edges;good+=1
            # Therefore max(x)=max(x0,x2,x_anchor+σ(x1-x_anchor),
            # x2+σ(x3-x2),x0+σ(x4-x0)) identically, by max(a,b)=a+σ(b-a).
    assert seen==set(product((1,-1),repeat=5))and(bad,good)==(26,6);out={'status':'INDEPENDENT_EXACT_ALL32_CYCLE9_ORIENTATIONS_PASS','impossible_first_layers':bad,'feature_factorisations':good,'seconds':time.monotonic()-start,'certificate_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'26 orientations fail for every possible second hidden layer. Six admit an explicit continuous factorization; a finite ReLU completion is still not established.'};(here/'overnight_fixed_cycle9_witnesses_check.json').write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(json.dumps(out,sort_keys=True))
if __name__=='__main__':main()
