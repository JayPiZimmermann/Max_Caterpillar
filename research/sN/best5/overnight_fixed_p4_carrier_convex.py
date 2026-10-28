"""Exact supporting-plane obstruction to any positive-ReLU correction.

For fixed three positive carriers P, if P-max is R+sum sigma(h_j), it
extends to a homogeneous convex function of the seven features. At a
smooth input point there is a feature-space support plane with the right
input gradient and below every tested feature ray. One rational
infeasibility certificate refutes that entire completion route.
"""
from fractions import Fraction as Q
from pathlib import Path
from itertools import permutations,combinations,product
import json,time,hashlib,sys
from overnight_fixed_k2_certify import certified_feasible
HERE=Path(__file__).resolve().parent


def main():
    start=time.monotonic();net=json.loads((HERE/'overnight_fixed_cross_net9_14_simple.json').read_text());A=[[Q(x)for x in r]for r in net['first_layer'][:7]];sets=[S for k in range(1,5)for S in combinations(range(5),k)];Z=[[max(sum(row[i]for i in S),Q(0))for row in A]for S in sets];choices=list(product((0,1),(0,1),(0,-1),(0,-1),(0,1)));results=[]
    for ci,(p13,p14,q14,r14,last)in enumerate(choices):
        plus=[[Q(x)for x in r]for r in [[1,0,p13,-1,0,0,0],[1,0,p14,0,-1,q14,r14],([0,0,0,0,0,1,-1]if last==0 else[0,1,0,-1,0,0,0])]];Y=[sum(max(sum(w*x for w,x in zip(row,z)),Q(0))for row in plus)-Q(1-int(0 in S))for S,z in zip(sets,Z)];II=[(['ray',j],[y]+[-x for x in z])for j,(y,z)in enumerate(zip(Y,Z))];witness=None
        for perm in permutations(range(5)):
            rank={v:i for i,v in enumerate(perm)};act=[row if rank[next(i for i,x in enumerate(row)if x>0)]<rank[next(i for i,x in enumerate(row)if x<0)]else[Q(0)]*5 for row in A];point=[Q(16**(4-rank[i]))for i in range(5)];grad=[Q(i==0)-Q(i==perm[0])for i in range(5)]
            for w in plus:
                g=[sum(w[j]*act[j][i]for j in range(7))for i in range(5)];value=sum(x*y for x,y in zip(g,point));assert value or not any(g)
                if value>0:grad=[x+y for x,y in zip(grad,g)]
            EE=[(['grad',i],[-grad[i]]+[act[j][i]for j in range(7)])for i in range(5)];feasible,proof=certified_feasible(EE,II,7)
            if not feasible:witness={'permutation':perm,'point':list(map(str,point)),'gradient':list(map(str,grad)),'proof':proof};break
        record={'config':ci,'parameters':choices[ci],'status':'EXACT_CONVEX_EXTENSION_OBSTRUCTION'if witness else'SUPPORT_PLANE_TEST_SURVIVOR','witness':witness};results.append(record);print(ci,record['status'],None if witness is None else witness['permutation'],flush=True)
    report={'status':'BOUNDED_NATURAL_CARRIER_SUPPORT_PLANE_GATE','results':results,'seconds':time.monotonic()-start,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Only the32 explicitly specified positive-carrier choices. A witnessed case cannot be completed by any number of negative outer ReLUs plus a W7 remainder. No general five-free-term lower bound.'};(HERE/'overnight_fixed_p4_carrier_convex.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print('DONE',time.monotonic()-start,flush=True)
if __name__=='__main__':main()
