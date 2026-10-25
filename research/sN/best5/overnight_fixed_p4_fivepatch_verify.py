"""Independent exact five-patch obstruction; no producer imports or LP."""
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import json,hashlib,time


def inconsistent(rows):
    M=[list(map(Q,row))for row in rows];rank=0;n=len(M[0])-1
    for col in range(n):
        k=next((k for k in range(rank,len(M))if M[k][col]),None)
        if k is None:continue
        M[rank],M[k]=M[k],M[rank];p=M[rank][col];M[rank]=[x/p for x in M[rank]]
        for j in range(rank+1,len(M)):
            p=M[j][col]
            if p:M[j]=[x-p*y for x,y in zip(M[j],M[rank])]
        rank+=1
    return any(not any(row[:-1])and row[-1]for row in M)


def main():
    start=time.monotonic();here=Path(__file__).parent;path=here/'overnight_fixed_p4_fivepatch.json';data=json.loads(path.read_text());A=[[-1,1,0,0,0],[-1,0,1,0,0],[0,-1,1,0,0],[-1,0,0,1,0],[-1,0,0,0,1],[0,0,0,1,-1],[0,0,1,0,-1]];pairs=patches=0
    for case in data['cases']:
        eqs=[];plus=case['positive_carriers'];assert len(plus)==3 and all(len(row)==7 for row in plus)
        for patch in case['patches']:
            x=list(map(Q,patch['point']));assert len(x)==len(set(x))==5;act=[]
            for row in A:
                value=sum(v*t for v,t in zip(row,x));assert value;act.append(row if value>0 else[0]*5)
            assert list(map(any,act))==patch['feature_active'];top=max(range(5),key=lambda i:x[i]);grad=[Q(i==0)-Q(i==top)for i in range(5)]
            for w in plus:
                g=[sum(Q(w[j])*act[j][i]for j in range(7))for i in range(5)];value=sum(v*t for v,t in zip(g,x));assert value or not any(g)
                if value>0:grad=[u+v for u,v in zip(grad,g)]
            assert grad==list(map(Q,patch['correction_gradient']));rows=[[act[j][i]for j in range(7)]+[grad[i]]for i in range(5)];assert not inconsistent(rows);eqs.append(rows);patches+=1
        assert len(eqs)==5
        for a,b in combinations(eqs,2):assert inconsistent(a+b);pairs+=1
    report={'status':'INDEPENDENT_EXACT_FIVE_PATCH_OBSTRUCTIONS_PASS','carrier_choices':len(data['cases']),'open_patches':patches,'incompatible_pairs':pairs,'seconds':time.monotonic()-start,'certificate_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Each of the eight listed fixed three-positive-carrier choices requires at least five feature-linear planes in its correction, excluding two negative ReLUs plus arbitrary feature-linear remainder. Other five-term formulas remain open.'};(here/'overnight_fixed_p4_fivepatch_check.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps(report,sort_keys=True))
if __name__=='__main__':main()
