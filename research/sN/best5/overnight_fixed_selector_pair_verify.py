"""Independent exact34-equation obstruction for the corrected selector pattern.

No producer, symbolic-algebra package, solver, or precomputed row matrix
is imported. The first14 features and every equation are rebuilt directly.
The arbitrary-first-layer wall-removal bridge is a separate written proof.
"""
import hashlib,itertools,json,time
from fractions import Fraction as Q
from pathlib import Path


def main():
    start=time.monotonic();path=Path('overnight_fixed_selector_pair_certificate.json');proof=json.loads(path.read_text());edges=[(i,0)for i in range(1,5)]+list(itertools.combinations(range(5),2));left=[Q(0)]*56;right=Q(0);kinds={}
    for term in proof['terms']:
        x=list(map(Q,term['point']));assert len(x)==5 and x[0]==0;coefficient=Q(term['coefficient']);a,b,c,d,e=x;m=min(a,b);D=max(d,e);p=a-max(b,c)+D-m;q=b-max(a,c)+D-m;G=(p,q,-max(p,q));phi=[max(x[i]-x[j],Q(0))for i,j in edges];kind=term['kind'];kinds[kind]=kinds.get(kind,0)+1
        if kind=='value':row=phi+[v*int(G[0]>0)for v in phi]+[v*int(G[1]>0)for v in phi]+[-v*int(G[2]>0)for v in phi];rhs=max(x)
        else:
            assert kind=='zero';j=term['unit'];assert j in(0,1,2)and G[j]==0;row=[Q(0)]*56;row[14*(j+1):14*(j+2)]=phi;rhs=Q(0)
        left=[u+coefficient*v for u,v in zip(left,row)];right+=coefficient*rhs
    assert all(v==0 for v in left)and right==1
    report={'status':'INDEPENDENT_EXACT_SELECTOR_PAIR_PATTERN_EXCLUSION_PASS','equations':len(proof['terms']),'kinds':kinds,'coefficient_parameters':56,'summed_left':'0','summed_right':'1','seconds':time.monotonic()-start,'certificate_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};Path('overnight_fixed_selector_pair_check.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True))

if __name__=='__main__':main()
