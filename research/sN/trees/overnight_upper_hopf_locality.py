#!/usr/bin/env python3
"""All-real two-flag obstruction for the associated Baxter wheel graph.

One evaluator updates head/free-edge germs. The other evaluates the original
nested ReLUs on exact lexicographic jets, without any germ simplification.
"""
from collections import defaultdict
from pathlib import Path
import hashlib,json
from overnight_upper_baxter_locality import words_target
HERE=Path(__file__).parent

def prune_D(chain,u):
    out=defaultdict(int)
    for sign in (1,-1):
        direction=tuple(sign*v for v in u)
        for (head,edges),coefficient in chain.items():
            h=list(head);free=[];height=sum(a*b for a,b in zip(head,direction))
            for i,j in edges:
                slope=direction[i]-direction[j];height+=max(0,slope)
                if slope>0:h[i]+=1;h[j]-=1
                elif not slope:free.append((i,j))
            if not height:out[(tuple(h),tuple(free))]+=sign*coefficient
    return {k:c for k,c in out.items() if c}

def value(chain,x):
    return sum(c*max(0,sum(a*b for a,b in zip(h,x))+sum(max(0,x[i]-x[j]) for i,j in edges))
               for (h,edges),c in chain.items())

def jet_relu(vector):
    return vector if next((v for v in vector if v),0)>0 else (0,0,0)

def jet_value(chain,point):
    result=[0,0,0]
    for (head,edges),coefficient in chain.items():
        pre=[sum(head[i]*point[i][k] for i in range(5)) for k in range(3)]
        for i,j in edges:
            val=jet_relu(tuple(point[i][k]-point[j][k] for k in range(3)))
            pre=[a+b for a,b in zip(pre,val)]
        val=jet_relu(tuple(pre))
        result=[a+coefficient*b for a,b in zip(result,val)]
    return tuple(result)

def exact_two_germs(chain,u,v,x):
    # Lexicographic coefficients of 1,epsilon,epsilon*delta.
    return sum(s*t*jet_value(chain,[(s*u[i],t*v[i],x[i]) for i in range(5)])[2]
               for s in (1,-1) for t in (1,-1))

def main():
    words=((3,1,4,2),(3,4,1,2));target=words_target(words)
    graph=((0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(2,4),(3,4))
    u=(-1,0,1,0,0);v=(0,0,0,-1,0);x=(1,0,0,0,0);y=(0,1,0,0,0)
    slopes=[(u[i]-u[j],v[i]-v[j]) for i,j in graph]
    assert all(a or b for a,b in slopes)
    first=prune_D(target,u);second=prune_D(first,v)
    z=tuple(a+b for a,b in zip(x,y));neg=lambda w:tuple(-a for a in w)
    points=[z,neg(z),x,neg(x),y,neg(y)];weights=[1,-1,-1,1,-1,1]
    exact=[exact_two_germs(target,u,v,p) for p in points]
    simplified=[value(second,p) for p in points]
    witness=sum(a*b for a,b in zip(weights,exact))
    assert witness==-1==sum(a*b for a,b in zip(weights,simplified))
    result=dict(status='EXACT_ALL_REAL_FIXED_BAXTER_WHEEL_OBSTRUCTION',
        class_words=words,graph=graph,first_direction=u,second_direction=v,
        graph_edge_direction_pairs=slopes,odd_additivity_points=points,odd_additivity_weights=weights,
        raw_lexicographic_jet_values=exact,pruned_germ_values=simplified,defect=witness,
        first_surviving_units=len(first),second_surviving_units=len(second),
        final_units=[dict(head=h,edges=e,coefficient=c) for (h,e),c in second.items()],
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        raw_target_builder_sha256=hashlib.sha256((HERE/'overnight_upper_baxter_locality.py').read_bytes()).hexdigest(),
        scope='Arbitrary real linear heads, arbitrary signed inner/output weights and arbitrary width using only comparisons from this fixed graph, plus an arbitrary shallow remainder or L3 remainder on the four-dimensional translation quotient. Other graph centres/orders are not excluded.')
    (HERE/'overnight_upper_hopf_locality.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],'EXACT_DEFECT',witness,'JET_VALUES',exact)

if __name__=='__main__':main()
