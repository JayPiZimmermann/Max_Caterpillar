"""Exact necessary target values of the sparse score via the proved caterpillar sum.

A zero is a decisive obstruction to this score detecting max, whether or not
it descends. A nonzero is not a proof of quotient descent.
"""
from pathlib import Path
from fractions import Fraction as Q
import itertools,json,math,time

def root_counts(T):
    V=sorted(T);unused=set(V);M=[]
    while unused:
        if any(not(T[v]&unused)for v in unused):return {v:0 for v in V}
        v=next(v for v in sorted(unused)if len(T[v]&unused)==1);w=next(iter(T[v]&unused));M.append((v,w));unused-={v,w}
    block={v:i for i,e in enumerate(M)for v in e};B={i:set()for i in range(len(M))}
    for v in V:
        for w in T[v]:
            if block[v]!=block[w]:B[block[v]].add(block[w])
    out={}
    for root in V:
        parent={root:None};order=[root]
        for v in order:
            for w in T[v]:
                if w!=parent[v]:parent[w]=v;order.append(w)
        rb=block[root];pb={rb:None};blocks=[rb]
        for b in blocks:
            for c in sorted(B[b]):
                if c!=pb[b]:pb[c]=b;blocks.append(c)
        perm=[]
        for b in blocks:
            v,w=M[b]
            if parent[v]==w:v,w=w,v
            perm.extend((v,w))
        sign=(-1)**sum(perm[i]>perm[j]for i in range(len(V))for j in range(i+1,len(V)))
        size={b:1 for b in blocks}
        for b in reversed(blocks[1:]):size[pb[b]]+=size[b]
        e=math.factorial(len(M)-1)//math.prod(size[b]for b in blocks[1:]);out[root]=sign*e
    return out

def score(U):
    E=set(U['edges']);V=sorted({v for e in E for v in e});T={v:set()for v in V}
    for v,w in E:T[v].add(w);T[w].add(v)
    I=root_counts(T)
    if not any(I.values()):return 0
    parent={U['root']:None};order=[U['root']];eps=1;kap={v:int(v==U['root'])for v in V};chi={U['root']:1}
    for v,w in E:kap[v]+=1
    for v in order:
        for w in T[v]:
            if w!=parent[v]:parent[w]=v;order.append(w);chi[w]=-chi[v];eps*=1 if(w,v)in E else -1
    D1=K1=D1c=K1c=D2=0
    for v in V:
        dist={v:0};todo=[v]
        for w in todo:
            for x in T[w]:
                if x not in dist:dist[x]=dist[w]+1;todo.append(x)
        for w in V:
            t=I[v]*I[w]*dist[w];c=chi[v]*chi[w];k=kap[v]+kap[w];D1+=t;D2+=t*dist[w];D1c+=c*t;K1+=k*t;K1c+=k*c*t
    return Q(15,8)*(36*D1-2*K1+2*eps*D1-6*K1c-2*eps*D1c-3*eps*D2)

def main():
    start=time.monotonic();result={'status':'EXACT_NECESSARY_TARGET_SCORE_VIA_SIGNED_CATERPILLAR_IDENTITY','arities':[]}
    for N in(3,5,7,9,11,13):
        s=Q(0);nonzero=0;positive=negative=Q(0);examples=[]
        for mask in range(1,1<<(N-2)):
            S={j for j in range(1,N-1)if mask>>(j-1)&1};q=max(S);E=[]
            for j in range(1,N-1):
                p=max([0]+[i for i in S if i<j]);E.append((p+1,j+1))
            U={'root':q+1,'edges':E};v=(-1)**(N+len(S))*score(U);s+=v
            if v:nonzero+=1
            if v>0:positive+=v
            else:negative+=v
        row={'arity':N,'descriptions':(1<<(N-2))-1,'nonzero_scores':nonzero,'signed_sum':str(s),'necessary_target_response':str(s/math.factorial(N)),'positive_part':str(positive),'negative_part':str(negative),'elapsed_seconds':time.monotonic()-start};result['arities'].append(row);print(row,flush=True)
        Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
    result['scope']='Uses the proved top-class signed caterpillar identity. Responses are necessary if the score descends; no descent assertion. A zero response refutes a nonzero-target separator with this exact fixed formula.';Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
