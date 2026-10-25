"""Independent direct controls for the generic-tie equations with linear anchors."""
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import json,time,hashlib
HERE=Path(__file__).resolve().parent


def run(name):
    net=json.loads((HERE/name).read_text());A=[list(map(Q,r))for r in net['first_layer']];W=[list(map(Q,r))for r in net['second_layer']];D=list(map(Q,net['output']));sets=[frozenset(s)for k in range(1,6)for s in combinations(range(5),k)];values={S:[max(sum(r[i]for i in S),Q(0))for r in A]for S in sets};g=[{S:sum(w*x for w,x in zip(row,values[S]))for S in sets}for row in W[2:]];signs=D[2:];full=frozenset(range(5));assert all(row[full]==0 for row in g)
    for S in sets:
        head=sum(w*x for w,x in zip(W[0],values[S]));out=head+sum(d*max(row[S],Q(0))for d,row in zip(signs,g));assert out==1
    localities=[(U,o)for U in sets if len(U)==3 for o in range(5)if o not in U]+[(U,None)for U in sets if len(U)in(4,5)]
    for U,o in localities:
        total=Q(0)
        for d,row in zip(signs,g):
            active=len(U)==5 or row[U]==0
            if o is not None:active=active and row[U|{o}]==0
            if active:total+=d*sum(((-1)**(len(U)-len(S)))*abs(row[S])for S in sets if S<U)
        assert total==2*((-1)**(len(U)+1)),(name,U,o,total)
    return{'network':name,'boolean_values':len(sets),'generic_ties':len(localities),'free_units':len(g),'network_sha256':hashlib.sha256((HERE/name).read_bytes()).hexdigest()}


def main():
    start=time.monotonic();out={'status':'INDEPENDENT_EXACT_LINEAR_ANCHOR_LOCALITY_CONTROLS_PASS','controls':[run(name)for name in('netB_10_6.json','overnight_fixed_cross_net9_14_simple.json','overnight_fixed_anchor_control12_network.json')],'seconds':time.monotonic()-start,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};(HERE/'overnight_fixed_locality_controls.json').write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(json.dumps(out,sort_keys=True))
if __name__=='__main__':main()
