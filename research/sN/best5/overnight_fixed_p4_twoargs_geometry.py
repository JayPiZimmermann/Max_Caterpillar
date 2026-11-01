"""Exact geometric reduction of the two-fixed-symmetric-term P4 family.
Three open positive-input cells force the two free forms up to sign.
Every resulting candidate is tested with the independent global checker.
"""
from fractions import Fraction as Q
from itertools import product
import hashlib,json,sys
from pathlib import Path
from overnight_fixed_cross_verify import check


def solve(A,b):
    M=[list(map(Q,row))+[Q(v)]for row,v in zip(A,b)];piv={};rank=0
    for j in range(7):
        i=next((i for i in range(rank,len(M))if M[i][j]),None)
        if i is None:continue
        M[rank],M[i]=M[i],M[rank];v=M[rank][j];M[rank]=[x/v for x in M[rank]]
        for i in range(len(M)):
            if i==rank:continue
            v=M[i][j];M[i]=[x-v*y for x,y in zip(M[i],M[rank])]
        piv[j]=rank;rank+=1
    if any(not any(row[:7])and row[7]for row in M):return None
    assert rank==7
    return [M[piv[j]][7]for j in range(7)]


def main():
    base=Path(__file__).parent
    # Rows are feature gradients in input order u,v,s,t.
    Z1=((1,0,0,0),(0,1,0,0),(-1,1,0,0),(0,0,1,0),(0,0,0,1),(0,0,1,-1),(0,1,0,-1))
    Z2=Z1[:2]+((0,0,0,0),)+Z1[3:]
    Z3=Z1[:2]+((0,0,0,0),)+Z1[3:5]+((0,0,0,0),(0,0,0,0))
    cells=[Z1,Z2,Z3];A=[[cell[j][i]for j in range(7)]for cell in cells for i in range(4)]
    Lrhs=((0,-1,1,0),(-1,0,1,0),(-1,0,0,1))
    Mrhs=((Q(1,2),Q(-1,2),Q(1,2),Q(-1,2)),(Q(-1,2),Q(1,2),Q(1,2),Q(-1,2)),(Q(-1,2),Q(1,2),Q(-1,2),Q(1,2)))
    forms=[]
    for name,rhs in(('L',Lrhs),('M',Mrhs)):
        out=[]
        for signs in product((-1,1),repeat=3):
            sol=solve(A,[s*v for s,row in zip(signs,rhs)for v in row])
            if sol is not None:out.append({'signs':signs,'coefficients':list(map(str,sol))})
        forms.append(out)
    L0=list(map(Q,(-1,0,-1,0,1,1,0)));M0=list(map(Q,(Q(-1,2),Q(1,2),-1,Q(-1,2),Q(1,2),1,0)))
    old=json.loads((base/'overnight_fixed_cross_net9_14_simple.json').read_text());candidates=[]
    for i,(l,m)in enumerate(product(*forms)):
        L=list(map(Q,l['coefficients']));M=list(map(Q,m['coefficients']));R=[(x-y+z-w)/2 for x,y,z,w in zip(L0,L,M,M0)];R[0]+=1;carrier=R+[Q(1),Q(-1)];net={'N':5,'first_layer':old['first_layer'],'second_layer':[list(map(str,carrier)),list(map(str,[-v for v in carrier])),list(map(str,L))+[0,0],list(map(str,M))+[0,0],[-1,1,0,-1,1,0,0,0,0],[-1,1,0,1,-1,0,0,0,0]],'output':[1,-1,1,-1,'1/2','1/2']};path=base/f'overnight_fixed_p4_twoargs_geometry_candidate_{i}.json';path.write_text(json.dumps(net,indent=2)+'\n')
        try:receipt=check(path);status='EXACT_GLOBAL_PASS'
        except AssertionError as error:receipt={'error':str(error)};status='EXACT_GLOBAL_FAIL'
        x=list(map(Q,(0,4,4,2,-1)));first=[max(sum(Q(a)*b for a,b in zip(row,x)),Q(0))for row in net['first_layer']];actual=sum(Q(out)*max(sum(Q(a)*b for a,b in zip(row,first)),Q(0))for row,out in zip(net['second_layer'],net['output']));assert actual==3 and max(x)==4
        candidates.append({'index':i,'L_signs':l['signs'],'M_signs':m['signs'],'status':status,'receipt':receipt,'exact_counterexample':{'x':list(map(str,x)),'actual':'3','target':'4'}})
    report={'status':'EXACT_THREE_CELL_GEOMETRY_COMPLETE','L_forms':forms[0],'M_forms':forms[1],'candidate_count':len(candidates),'candidates':candidates,'scope':'The family with the two symmetric half-weight terms fixed, arbitrary two remaining preactivations, and arbitrary first-feature linear remainder. The geometric crease-uniqueness bridge is required for completeness.','producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};(base/'overnight_fixed_p4_twoargs_geometry.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True,indent=2))
if __name__=='__main__':main()
