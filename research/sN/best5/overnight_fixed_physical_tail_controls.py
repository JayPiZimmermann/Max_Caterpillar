"""Independent arithmetic controls for both physical translation-tail identities.

Checks their formula against exact finite difference quotients of actual
networks, and checks all26 top-tie equations at each translation end.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import combinations
import hashlib,json,time
HERE=Path(__file__).resolve().parent


def run(name):
    net=json.loads((HERE/name).read_text());A=[list(map(Q,r))for r in net['first_layer']];W=[list(map(Q,r))for r in net['second_layer']];D=list(map(Q,net['output']));sets=[frozenset(s)for k in range(1,6)for s in combinations(range(5),k)];localities=[(U,o)for U in sets if len(U)==3 for o in range(5)if o not in U]+[(U,None)for U in sets if len(U)in(4,5)];records=[]
    def evalnet(x):
        phi=[max(sum(a*b for a,b in zip(row,x)),Q(0))for row in A];return sum(d*max(sum(a*b for a,b in zip(w,phi)),Q(0))for d,w in zip(D,W))
    for tail in(1,-1):
        row_base=[tail*sum(row)for row in A];phi_base=[max(v,Q(0))for v in row_base];outer_base=[sum(a*b for a,b in zip(w,phi_base))for w in W];assert sum(d*max(v,Q(0))for d,v in zip(D,outer_base))==tail
        def derivative(x):
            raw=[sum(a*b for a,b in zip(row,x))for row in A];first=[r if b>0 else(Q(0)if b<0 else max(r,Q(0)))for b,r in zip(row_base,raw)];B=[sum(a*b for a,b in zip(w,first))for w in W];value=sum(d*(b if a>0 else(Q(0)if a<0 else max(b,Q(0))))for d,a,b in zip(D,outer_base,B));eps=Q(1,2)
            for a,b in zip(row_base,raw):
                if a and b:eps=min(eps,abs(a)/(2*abs(b)))
            for a,b in zip(outer_base,B):
                if a and b:eps=min(eps,abs(a)/(2*abs(b)))
            quotient=(evalnet([Q(tail)+eps*v for v in x])-Q(tail))/eps;assert quotient==value==max(x);return B
        values={S:derivative([Q(i in S)for i in range(5)])for S in sets}
        for x in((3,4,2,1,0),(-3,-1,-5,-2,-4),(2,-3,1,-4,0)):derivative(list(map(Q,x)))
        for U,o in localities:
            total=Q(0)
            for k,d in enumerate(D):
                active=outer_base[k]==0 and(len(U)==5 or values[U][k]==0)
                if o is not None:active=active and values[U|{o}][k]==0
                if active:total+=d*sum(((-1)**(len(U)-len(S)))*abs(values[S][k])for S in sets if S<U)
            assert total==2*((-1)**(len(U)+1)),(name,tail,U,o,total)
        records.append({'tail':tail,'finite_difference_controls':34,'generic_ties':26})
    return{'network':name,'sha256':hashlib.sha256((HERE/name).read_bytes()).hexdigest(),'tails':records}


def main():
    start=time.monotonic();names=['netB_10_6.json','overnight_fixed_cross_net9_14_simple.json','overnight_fixed_anchor_control12_network.json','overnight_fixed_physical_nonlinearhead_control.json'];out={'status':'INDEPENDENT_EXACT_PHYSICAL_TAIL_CONTROLS_PASS','controls':[run(n)for n in names],'seconds':time.monotonic()-start,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};(HERE/'overnight_fixed_physical_tail_controls.json').write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(json.dumps(out,sort_keys=True))
if __name__=='__main__':main()
