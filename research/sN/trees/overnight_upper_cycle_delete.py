#!/usr/bin/env python3
"""Independent raw-head coordinate-deletion closure controls for cycles."""
from pathlib import Path
import hashlib,json,time

HERE=Path(__file__).parent


def check(n):
    apex=n-1;vertices=list(range(n-1));counts={};survivors=0
    for mode in ('cycle','path'):
        edges=list(zip(vertices,vertices[1:]))
        if mode=='cycle':edges.append((vertices[-1],vertices[0]))
        for root in vertices:
            for shift in (0,) if mode=='cycle' else (-1,0,1):
                head=[0]*n;head[root]=1;head[apex]=-1;head[0]+=shift;head[n-2]-=shift
                for mask in range(1<<len(edges)):
                    oriented=[(v,u) if mask>>j&1 else (u,v) for j,(u,v) in enumerate(edges)]
                    for deleted in range(n):
                        free=[(u,v) for u,v in oriented if deleted not in (u,v)]
                        for sign in (-1,1):
                            value=sign*head[deleted]+sum(max(0,sign*((u==deleted)-(v==deleted))) for u,v in oriented)
                            if value or deleted==apex or len(free)<n-3:continue
                            newhead=head.copy();newhead[deleted]=0
                            for u,v in oriented:
                                if sign*((u==deleted)-(v==deleted))>0:
                                    if u!=deleted:newhead[u]+=1
                                    if v!=deleted:newhead[v]-=1
                            remaining=set(vertices)-{deleted};degrees={v:0 for v in remaining}
                            for u,v in free:degrees[u]+=1;degrees[v]+=1
                            ends=sorted(v for v,d in degrees.items() if d==1)
                            assert len(ends)==2 and len(free)==len(remaining)-1
                            matches=[]
                            for newroot in remaining:
                                for newshift in (-1,0,1):
                                    expected=[0]*n;expected[newroot]=1;expected[apex]=-1
                                    expected[ends[0]]+=newshift;expected[ends[1]]-=newshift
                                    if expected==newhead:matches.append((newroot,newshift))
                            assert matches,(n,mode,root,shift,mask,deleted,sign,newhead)
                            if mode=='cycle':assert any(s==0 for r,s in matches)
                            survivors+=1;key=f'{mode}:deleted_{"root" if deleted==root else "other"}'
                            counts[key]=counts.get(key,0)+1
    return dict(n=n,surviving_directional_germs=survivors,classification=counts)


def main():
    started=time.monotonic();results=[]
    for n in range(4,10):
        results.append(check(n));print(results[-1],flush=True)
    out=dict(status='EXACT_RAW_ORIENTATION_DELETION_CONTROLS_PASS',results=results,
             producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-started,
             scope='Complete raw root/orientation/endpoint-shift/direction cases at each listed arity; uniform case proof is in the accompanying note.')
    (HERE/'overnight_upper_cycle_delete.json').write_text(json.dumps(out,indent=2)+'\n')


if __name__=='__main__':main()
