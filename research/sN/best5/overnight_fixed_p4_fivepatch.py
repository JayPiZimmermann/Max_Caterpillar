"""Extract tiny open-patch certificates from the support-region diagnostics."""
from fractions import Fraction as Q
from pathlib import Path
from itertools import permutations,product
import json,time,hashlib
from overnight_fixed_bowtie_verify import rref
HERE=Path(__file__).resolve().parent
A=[[-1,1,0,0,0],[-1,0,1,0,0],[0,-1,1,0,0],[-1,0,0,1,0],[-1,0,0,0,1],[0,0,0,1,-1],[0,0,1,0,-1]]


def main():
    start=time.monotonic();choices=list(product((0,1),(0,1),(0,-1),(0,-1),(0,1)));out=[]
    for ci in(2,6,8,10,16,18,22,24):
        data=json.loads((HERE/f'overnight_fixed_p4_support_regions_{ci}.json').read_text());wanted={tuple(tuple(map(Q,row))for row in data['regions'][i]['equations']):None for i in data['five_clique']};p13,p14,q14,r14,last=choices[ci];plus=[[1,0,p13,-1,0,0,0],[1,0,p14,0,-1,q14,r14],([0,0,0,0,0,1,-1]if last==0 else[0,1,0,-1,0,0,0])]
        for radius in(3,4,5,6):
            for tail in permutations([x for x in range(-radius,radius+1)if x],4):
                x=[0]+list(tail);act=[[Q(v)for v in row]if sum(v*t for v,t in zip(row,x))>0 else[Q(0)]*5 for row in A];top=max(range(5),key=lambda i:x[i]);grad=[Q(i==0)-Q(i==top)for i in range(5)];smooth=True
                for w in plus:
                    g=[sum(w[j]*act[j][i]for j in range(7))for i in range(5)];value=sum(v*t for v,t in zip(g,x))
                    if not value and any(g):smooth=False;break
                    if value>0:grad=[u+v for u,v in zip(grad,g)]
                if not smooth:continue
                eq=rref([[act[j][i]for j in range(7)]+[grad[i]]for i in range(5)])
                if eq in wanted and wanted[eq]is None:wanted[eq]={'point':x,'correction_gradient':list(map(str,grad)),'feature_active':list(map(any,act))}
                if all(v is not None for v in wanted.values()):break
            if all(v is not None for v in wanted.values()):break
        assert all(v is not None for v in wanted.values());out.append({'config':ci,'parameters':choices[ci],'positive_carriers':plus,'patches':list(wanted.values())});print('FIVE_PATCHES',ci,[r['point']for r in wanted.values()],flush=True)
    record={'status':'EIGHT_EXACT_FIVE_PATCH_CERTIFICATES','cases':out,'seconds':time.monotonic()-start,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};(HERE/'overnight_fixed_p4_fivepatch.json').write_text(json.dumps(record,sort_keys=True,indent=2)+'\n')
if __name__=='__main__':main()
