"""Exact complete correction regions and supporting-plane compatibility.

A sum of two positive ReLUs plus a linear remainder is a support function
of a translated parallelogram. Its four vertex planes must cover all
linear regions. This file first tests an exact five-region obstruction.
"""
from fractions import Fraction as Q
from pathlib import Path
from itertools import permutations,product,combinations
import json,sys,time,hashlib,math
from overnight_fixed_bowtie_verify import rref
from overnight_fixed_p4_k4_raycone_probe import ray_kernel
HERE=Path(__file__).resolve().parent


def aff(rows):
    rr=rref(rows)
    return None if any(not any(r[:-1])and r[-1]for r in rr)else rr


def main():
    config=int(sys.argv[1]);start=time.monotonic();net=json.loads((HERE/'overnight_fixed_cross_net9_14_simple.json').read_text());A=[[Q(x)for x in row]for row in net['first_layer'][:7]];W=[[Q(x)for x in row[:7]]for row in net['second_layer'][2:]];D=list(map(Q,net['output'][2:]));R0=list(map(Q,net['second_layer'][0][:7]));choices=list(product((0,1),(0,1),(0,-1),(0,-1),(0,1)));p13,p14,q14,r14,last=choices[config];plus=[[Q(x)for x in row]for row in [[1,0,p13,-1,0,0,0],[1,0,p14,0,-1,q14,r14],([0,0,0,0,0,1,-1]if last==0 else[0,1,0,-1,0,0,0])]];cells={}
    for p in permutations(range(5)):
        rank={v:i for i,v in enumerate(p)};act=[row if rank[next(i for i,x in enumerate(row)if x>0)]<rank[next(i for i,x in enumerate(row)if x<0)]else[Q(0)]*5 for row in A];key=tuple(any(row)for row in act);cell=cells.setdefault(key,{'active':act,'sets':set()});cell['sets'].update(tuple(sorted(p[:t]))for t in range(1,5))
    regions=[];points=set();known=set()
    for key,cell in cells.items():
        act=cell['active'];linear=[-sum(w*row[i]for w,row in zip(R0,act))for i in range(5)];curv={}
        for w,d in zip(W+plus,[-d for d in D]+[Q(1)]*3):
            g=tuple(sum(w[j]*act[j][i]for j in range(7))for i in range(5));vs=[sum(g[j]for j in S)for S in cell['sets']]
            if min(vs)>=0:linear=[x+d*y for x,y in zip(linear,g)]
            elif max(vs)<=0:pass
            else:
                sc=next(x for x in g if x);normal=tuple(x/sc for x in g);curv[normal]=curv.get(normal,Q(0))+d*abs(sc)
                if sc<0:linear=[x+d*y for x,y in zip(linear,g)]
        normals=[(g,c)for g,c in sorted(curv.items())if c];assert all(c>0 for g,c in normals)
        for signs in product((1,-1),repeat=len(normals)):
            inequalities=[[Q(1 if k else-1)*x for x in row[1:]]for k,row in zip(key,A)]+[[s*x for x in g[1:]]for s,(g,c)in zip(signs,normals)];rays=set()
            for sub in combinations(inequalities,3):
                ray=ray_kernel(sub,4)
                if ray is None:continue
                for s in(1,-1):
                    r=tuple(s*x for x in ray)
                    if all(sum(x*y for x,y in zip(row,r))>=0 for row in inequalities):rays.add(r)
            if len(rref(rays))<4:continue
            grad=[linear[i]+sum(c*g[i]for s,(g,c)in zip(signs,normals)if s>0)for i in range(5)];eq=aff([[act[j][i]for j in range(7)]+[grad[i]]for i in range(5)]);assert eq is not None
            for ray in rays:
                z=[sum(row[i+1]*ray[i]for i in range(4))for row in act];value=sum(grad[i+1]*ray[i]for i in range(4));assert all(v>=0 for v in z)
                if any(z):scale=next(v for v in z if v);points.add(tuple(v/scale for v in z+[value]))
                else:assert value==0
            if eq not in known:known.add(eq);regions.append({'cell':key,'signs':signs,'gradient':grad,'equations':eq})
    graph=[set()for _ in regions]
    for i,r in enumerate(regions):
        for j in range(i):
            if aff(list(r['equations'])+list(regions[j]['equations']))is None:graph[i].add(j);graph[j].add(i)
    def clique(chosen,candidates):
        if len(chosen)==5:return chosen
        if len(chosen)+len(candidates)<5:return None
        candidates=sorted(candidates,key=lambda i:len(graph[i]&set(candidates)),reverse=True)
        while candidates:
            i=candidates.pop(0);found=clique(chosen+[i],[j for j in candidates if j in graph[i]])
            if found:return found
        return None
    found=clique([],list(range(len(regions))));out={'config':config,'parameters':choices[config],'status':'EXACT_FIVE_SUPPORTING_PLANE_OBSTRUCTION'if found else'NO_FIVE_PAIRWISE_INCOMPATIBLE_REGIONS','regions':[{'cell':r['cell'],'signs':r['signs'],'gradient':list(map(str,r['gradient'])),'equations':[[str(x)for x in row]for row in r['equations']]}for r in regions],'ray_points':[[str(x)for x in row]for row in sorted(points)],'incompatible_pairs':sum(map(len,graph))//2,'five_clique':found,'seconds':time.monotonic()-start,'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Only the specified three positive carriers. A five-clique rules out two negative correction ReLUs even with arbitrary W7 remainder.'};(HERE/f'overnight_fixed_p4_support_regions_{config}.json').write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k not in('regions','ray_points')},sort_keys=True),flush=True);print('COUNTS',len(regions),len(points),flush=True)
if __name__=='__main__':main()
