"""Independent exact N5 coverage/arithmetic check of the simple signed-root score.

Standard library only. Re-enumerates labelled trees from Pruefer words and
all roots/orientations. Uses normalized heads, direct S5 kernel sums, and
signed extensions by all24 orders. Does not import any producer module.
"""
from pathlib import Path
from collections import deque
from fractions import Fraction as Q
import hashlib,itertools,json,math,time
HERE=Path(__file__).parent

def canon(root,E):
    return min((p[root-1],tuple(sorted((p[u-1],p[v-1]) for u,v in E))) for p in itertools.permutations(range(1,5)))

def trees():
    for word in itertools.product(range(1,5),repeat=2):
        degrees={v:1+word.count(v) for v in range(1,5)};E=[]
        for v in word:
            leaf=min(x for x in degrees if degrees[x]==1);E.append((leaf,v));degrees[leaf]-=1;degrees[v]-=1
        last=[v for v in degrees if degrees[v]==1];E.append(tuple(last));yield E

def normalized(unit):
    edges=[tuple(sorted(e)) for e in unit['edges']];adj={v:set() for v in range(1,5)}
    for u,v in edges:adj[u].add(v);adj[v].add(u)
    head=[-1,0,0,0,0];head[unit['root']]+=1
    for u,v in unit['edges']:
        if u>v:head[u]+=1;head[v]-=1
    out=[]
    for u,v in edges:
        C={u};todo=[u]
        for x in todo:
            for y in adj[x]:
                if {x,y}=={u,v}:continue
                if y not in C:C.add(y);todo.append(y)
        out.append((C,sum(head[i] for i in C)))
    return adj,out

def evaluate(unit,point):
    adj,factors=normalized(unit);total=Q(0)
    for om in itertools.permutations(point):
        a=om[0];den=1
        for C,h in factors:
            q=sum(om[i] for i in C);den*=(q+h*a)*(q+(h+1)*a)
        assert den;total+=Q(-a,den)
    return total

def score(unit):
    adj,_=normalized(unit);I={};colors={1:1};todo=[1]
    for v in todo:
        for w in adj[v]:
            if w not in colors:colors[w]=-colors[v];todo.append(w)
    for r in adj:
        parent={r:None};todo=[r]
        for v in todo:
            for w in adj[v]:
                if w!=parent[v]:parent[w]=v;todo.append(w)
        total=0
        for p in itertools.permutations(range(1,5)):
            pos={v:i for i,v in enumerate(p)}
            if all(pos[v]>pos[w] for v,w in parent.items() if w is not None):
                total+=(-1)**sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))
        I[r]=total
    parent={unit['root']:None};todo=[unit['root']];A={unit['root']};sgn=1;E=set(map(tuple,unit['edges']))
    for v in todo:
        for w in adj[v]:
            if w!=parent[v]:
                parent[w]=v;todo.append(w);e=1 if(w,v)in E else -1;sgn*=e
                if v in A and e==1:A.add(w)
    q=sum(I[v] for v in A)**2+sum(colors[v]*I[v] for v in A)**2-(1+sgn)*sum(z*z for z in I.values())//2
    return q

def main():
    start=time.monotonic();data_path=HERE/'overnight_uniform_pruning_signed_gate.json';cert_path=HERE/'overnight_uniform_pruning_signed_family.json';data=json.loads(data_path.read_text());cert=json.loads(cert_path.read_text());units=data['units'];provided={canon(u['root'],u['edges']) for u in units};assert len(provided)==26
    exhaustive=set()
    for E in trees():
        for root in range(1,5):
            for flips in itertools.product((0,1),repeat=3):
                exhaustive.add(canon(root,[(v,u)if f else(u,v) for(u,v),f in zip(E,flips)]))
    assert exhaustive==provided
    w=[Q(x) for x in cert['modes']['basic']['evaluation_weights']];active=[(i,x)for i,x in enumerate(w)if x];responses=[]
    for u in units:
        response=sum(weight*evaluate(u,data['points'][i]) for i,weight in active);assert response==-15*score(u);responses.append(str(response))
    maximum=sum(weight*Q(1,math.prod(data['points'][i]))for i,weight in active);assert maximum==1
    result={'status':'INDEPENDENT_EXACT_N5_SIGNED_SCORE_PASS','all_labelled_tree_coverage':True,'root_orientation_orbits':26,'active_evaluation_points':len(active),'identity':'L(F_U)=-15 Q(U), L(R_max)=1','scope':'Exact N5 functional only; the same Q fails the N7 finite modular gate. No uniform lower bound.','seconds':time.monotonic()-start,'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in(data_path,cert_path)}}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':main()
