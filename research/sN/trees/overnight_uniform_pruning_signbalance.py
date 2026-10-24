"""Exact finite controls for the tree-poset signed-extension PM detector.

Every unlabelled even tree shape through8 vertices, all edge orientations.
Left side: signed subset DP over topological orders.
Right side: greedy forced-pair pruning, then unsigned DP on the contracted
matching tree, multiplied by the fixed domino-block permutation sign.
This is combinatorial only; no Fourier functional is claimed.
"""
from pathlib import Path
import itertools,json,time
import networkx as nx

def extensions(n,edges):
    pred=[0]*n
    for u,v in edges:pred[v]|=1<<u
    count=[0]*(1<<n);signed=[0]*(1<<n);count[0]=signed[0]=1
    for mask in range(1<<n):
        if not count[mask]:continue
        for v in range(n):
            bit=1<<v
            if mask&bit or pred[v]&~mask:continue
            nxt=mask|bit;count[nxt]+=count[mask]
            signed[nxt]+=signed[mask]*(-1 if (mask>>(v+1)).bit_count()%2 else 1)
    return count[-1],signed[-1]

def forced_matching(G):
    adj={v:set(G[v]) for v in G};remaining=set(G);pairs=[]
    while remaining:
        if any(not(adj[v]&remaining) for v in remaining):return None
        leaf=next(v for v in sorted(remaining) if len(adj[v]&remaining)==1);hub=next(iter(adj[leaf]&remaining));pairs.append(tuple(sorted((leaf,hub))));remaining.remove(leaf);remaining.remove(hub)
    return sorted(pairs)

def predicted(n,edges,pairs):
    if pairs is None:return 0,0
    oriented=set(edges);words=[(u,v) if(u,v) in oriented else(v,u) for u,v in pairs];word=[v for p in words for v in p];sign=(-1)**sum(word[i]>word[j] for i in range(n) for j in range(i+1,n));block={v:i for i,p in enumerate(pairs) for v in p};contracted=[(block[u],block[v]) for u,v in edges if block[u]!=block[v]];e,_=extensions(n//2,contracted)
    return sign*e,e

def main():
    start=time.monotonic();counts={};examples=[]
    for n in [2,4,6,8]:
        shapes=orientations=bad=good=0
        for G in nx.nonisomorphic_trees(n):
            G=nx.convert_node_labels_to_integers(G);shapes+=1;E=list(G.edges);pairs=forced_matching(G)
            for bits in itertools.product([0,1],repeat=n-1):
                edges=[(u,v) if b else(v,u) for (u,v),b in zip(E,bits)];e,signed=extensions(n,edges);want,dominoes=predicted(n,edges,pairs);assert signed==want;assert (signed==0)==(pairs is None)
                orientations+=1
                if pairs is None:bad+=1
                else:good+=1
                if n==8 and len(examples)<3 and pairs is not None:examples.append({'edges':edges,'matching':pairs,'extensions':e,'signed_extensions':signed,'contracted_extensions':dominoes})
        counts[str(n)]={'tree_shapes':shapes,'oriented_trees':orientations,'no_perfect_matching':bad,'perfectly_matchable':good}
    result={'status':'EXACT_TREE_SIGN_IMBALANCE_CONTROLS_PASS','counts':counts,'examples':examples,'seconds':time.monotonic()-start,'scope':'Uniform combinatorial proof is in the pruning note; no kernel functional or lower bound follows without a separate bridge.'}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':main()
