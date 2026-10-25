#!/usr/bin/env python3
"""Exact graph/head embedding audit of the established NC7 positive witness.

The fixed order is the increasing label order. Permutations are used only
to enumerate twin BST pairs at this finite arity, not to close the family
under arbitrary relabelings. A direct embedding uses graph apex b != root r:
head r-a = (r-b)+(b-a), with edge ba frozen when b != a.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations,permutations
from pathlib import Path
import hashlib,json,time
from overnight_upper_baxter_union import bst
HERE=Path(__file__).parent

def main():
    start=time.monotonic();n=7
    path=HERE/'all_tree_dfs/nc_fast_7.json'
    compact_path=HERE/'overnight_upper_baxter_nc7_embedding.json'
    if path.exists():
        data=json.loads(path.read_text());coefficients=list(map(Q,data['coefficient_proposal']))
        units=[(index,data['units'][index],c) for orbit,c in zip(data['orbits'],coefficients) if c for index in orbit]
        source_hash=hashlib.sha256(path.read_bytes()).hexdigest()
    else:
        # The compact witness is a complete mathematical seed. The original
        # search inventory is not required for a clean replay.
        seed=json.loads(compact_path.read_text());source_hash=seed['source_witness_sha256']
        units=[(i,dict(apex=a,root=r,edges=e),Q(c))
               for i,(a,r,e,c,b,w,refl) in enumerate(seed['compact_atoms'])]
        data={'units':{i:u for i,u,c in units}}
    edges=list(combinations(range(n),2));index={e:j for j,e in enumerate(edges)}
    def mask(es):return sum(1<<index[tuple(sorted(e))] for e in set(tuple(sorted(e)) for e in es))
    graphs=[];twin_counts=[]
    for b in range(n):
        labels=[v for v in range(n) if v!=b];pairs={}
        for word in permutations(labels):
            pair=(bst(word),bst(word[::-1]))
            pairs.setdefault(pair,word)
        by_graph={}
        for pair,word in pairs.items():
            graph=tuple(sorted(set(tuple(sorted(e)) for tree in pair for e in tree)|
                               {tuple(sorted((b,v))) for v in labels}))
            by_graph.setdefault(mask(graph),(pair,word,graph))
        graphs.extend((b,m,*v) for m,v in sorted(by_graph.items()))
        twin_counts.append(dict(apex=b,twin_pairs=len(pairs),union_graphs=len(by_graph)))
    embedded=[];reflection_only=[];uncovered=[];graph_uncovered=[]
    for idx,u,c in units:
        m=mask(u['edges']);a=u['apex'];r=u['root']
        candidates=[g for g in graphs if m&g[1]==m]
        if not candidates:
            graph_uncovered.append(idx);uncovered.append(idx);continue
        direct=next((g for g in candidates if g[0]!=r),None)
        if direct is not None:
            b,gm,pair,word,graph=direct
            # Keep the exact original orientations. The only additional
            # frozen segment is ba, absent because a is isolated in u.
            if b!=a:assert tuple(sorted((b,a))) in graph and all(a not in e for e in u['edges'])
            head=[int(i==r)-int(i==b) for i in range(n)]
            if b!=a:head[b]+=1;head[a]-=1
            assert head==[int(i==r)-int(i==a) for i in range(n)]
            embedded.append(dict(unit_index=idx,graph_apex=b,witness_word=word))
        else:
            # Graph centre is the head root. Reflect input: the head becomes
            # a-r and every inner orientation reverses. This is a candidate
            # unit; generic Fourier parity multiplies its top class by(-1)^N.
            b,gm,pair,word,graph=candidates[0];assert b==r
            reflection_only.append(dict(unit_index=idx,graph_apex=b,witness_word=word))
    embeddings={v['unit_index']:(v['graph_apex'],v['witness_word'],False) for v in embedded}
    embeddings.update({v['unit_index']:(v['graph_apex'],v['witness_word'],True) for v in reflection_only})
    compact=[]
    for idx,u,c in units:
        if idx not in embeddings:continue
        b,word,reflected=embeddings[idx]
        compact.append([u['apex'],u['root'],u['edges'],str(c),b,word,reflected])
    result=dict(status='EXACT_NC7_WITNESS_GRAPH_HEAD_EMBEDDING_AUDIT',labels=n,
        supported_units=len(units),twin_counts=twin_counts,graph_descriptions=len(graphs),
        direct_embeddings=len(embedded),top_reflection_embeddings=len(reflection_only),
        uncovered_units=len(uncovered),uncovered_graph_units=len(graph_uncovered),
        compact_atoms=compact,uncovered=uncovered,
        first_uncovered=[dict(unit_index=i,unit=data['units'][i]) for i in uncovered[:8]],
        source_witness_sha256=source_hash,
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-start,
        scope='Exact containment of the already certified finite NC7 witness. Direct embeddings preserve whole functions. Reflection embeddings preserve only top classes with Fourier parity. This is not uniform sufficiency.')
    (HERE/'overnight_upper_baxter_nc7_embedding.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print(result['status'],'UNITS',len(units),'DIRECT',len(embedded),'REFLECTED',len(reflection_only),
          'UNCOVERED',len(uncovered),'GRAPHS',len(graphs),'SECONDS',result['seconds'],flush=True)

if __name__=='__main__':main()
