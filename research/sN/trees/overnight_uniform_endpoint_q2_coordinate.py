#!/usr/bin/env python3
"""Exact coordinate-pole reduction by signed leaf deletion and colored trees."""
from collections import Counter
from pathlib import Path
import hashlib,json,time

HERE=Path(__file__).parent


def key(root,edges):
    vertices={root}|{v for edge in edges for v in edge};adj={v:[]for v in vertices}
    kappa={v:int(v==root)for v in vertices}
    for u,v in edges:adj[u].append(v);adj[v].append(u);kappa[u]+=1
    def rooted(v,parent):return (kappa[v],tuple(sorted(rooted(w,v)for w in adj[v]if w!=parent)))
    return min(rooted(v,None)for v in vertices)


def main():
    started=time.monotonic();units=json.loads((HERE/'overnight_uniform_q9_inventory.json').read_text())['units']
    p=json.loads((HERE/'overnight_uniform_endpoint_q2.json').read_text())['results'][1]['proposals'][0]
    groups=Counter();representatives={};terms=[]
    for index,weight in p['integer_proposal'].items():
        u=units[int(index)];root=u['root'];edges=list(map(tuple,u['edges']));degree=Counter(v for e in edges for v in e)
        if degree[root]==1:
            neighbor=next(v if w==root else w for w,v in edges if root in(w,v))
            assert (neighbor,root)in edges
            edges.remove((neighbor,root));edges.append((root,neighbor));root=neighbor
        assert degree[root]>1
        for leaf in degree:
            if degree[leaf]!=1:continue
            edge=next(e for e in edges if leaf in e);epsilon=1 if edge[0]==leaf else-1
            reduced=[e for e in edges if e!=edge];coefficient=-int(weight)*epsilon
            canonical=key(root,reduced);groups[canonical]+=coefficient
            representatives[canonical]=dict(root=root,edges=reduced)
            terms.append(dict(original=int(index),leaf=leaf,coefficient=coefficient))
    surviving={k:c for k,c in groups.items()if c}
    out=dict(status='EXACT_COORDINATE_RESIDUE_COLORED_TREE_REDUCTION',input_terms=len(terms),classes=len(groups),
             surviving_classes=len(surviving),literal_cancellation=not surviving,
             survivors=[dict(coefficient=c,**representatives[k])for k,c in surviving.items()],
             seconds=time.monotonic()-started,producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             scope='Each leaf deletion is the exact coordinate-pole residue of a canonical kernel. Equal colored-tree keys give identical full label sums. Surviving classes need further rational identities.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))


if __name__=='__main__':main()
