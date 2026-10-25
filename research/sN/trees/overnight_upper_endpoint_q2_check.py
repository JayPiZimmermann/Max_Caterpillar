#!/usr/bin/env python3
"""Independent coordinate replay: no root slide or colored-tree grouping."""
import collections,hashlib,itertools,json,math,time
from fractions import Fraction as Q
from pathlib import Path
HERE=Path(__file__).parent

def cuts(root,edges):
    vertices=sorted({v for e in edges for v in e})
    adj={v:[] for v in vertices}
    for u,v in edges:adj[u].append(v);adj[v].append(u)
    answer=[]
    for u,v in edges:
        seen={u};stack=[u]
        while stack:
            a=stack.pop()
            for b in adj[a]:
                if {a,b}=={u,v} or b in seen:continue
                seen.add(b);stack.append(b)
        if root in seen:side=set(vertices)-seen;epsilon=-1
        else:side=seen;epsilon=1
        answer.append((side,epsilon))
    return answer

def primitive(vector):
    g=math.gcd(*vector)
    assert g
    if next(x for x in vector if x)<0:g=-g
    return tuple(x//g for x in vector)

def main():
    started=time.monotonic()
    inventory_path=HERE/'overnight_uniform_q9_inventory.json'
    proposal_path=HERE/'overnight_uniform_endpoint_q2.json'
    inventory=json.loads(inventory_path.read_text())['units']
    proposal=json.loads(proposal_path.read_text())['results'][1]['proposals'][0]
    assert len(proposal['integer_proposal'])==36 and not proposal['target_coefficient']
    state=collections.Counter()
    for i,c in proposal['integer_proposal'].items():
        u=inventory[int(i)];edges=tuple(sorted(map(tuple,u['edges'])))
        cut_list=cuts(u['root'],edges)
        assert all(s==1 or len(C)==1 for C,s in cut_list)
        poles=[]
        for C,s in cut_list:
            poles.extend([primitive(tuple(int(v in C) for v in range(1,9))),
                          primitive(tuple(int(v in C)-s for v in range(1,9)))])
        assert len(poles)==len(set(poles))==14
        state[(u['root'],edges)]+=int(c)
    stages=[]
    for N in (9,8,7,6):
        nxt=collections.Counter()
        for (root,edges),weight in state.items():
            degree=collections.Counter(v for e in edges for v in e)
            for v in degree:
                if degree[v]!=1:continue
                edge=next(e for e in edges if v in e)
                neighbor=next(x for x in edge if x!=v)
                if v==root:
                    if edge[0]==root:continue
                    newroot=neighbor;sign=-1
                else:
                    newroot=root;sign=-1 if edge[0]==v else 1
                nxt[(newroot,tuple(e for e in edges if e!=edge))]+=weight*sign
        state=collections.Counter({k:v for k,v in nxt.items() if v})
        stages.append(dict(arity=N-1,labelled_states=len(state)))
    frequencies=(-40,1,3,9,27);answer=Q(0);summands=0
    for (root,edges),weight in state.items():
        vertices=sorted({v for e in edges for v in e});assert len(vertices)==4
        cut_list=cuts(root,edges)
        for perm in itertools.permutations(frequencies):
            a=perm[0];omega=dict(zip(vertices,perm[1:]));denominator=1
            for C,epsilon in cut_list:
                q=sum(omega[v] for v in C)
                denominator*=q*(q+epsilon*a)
            assert denominator
            answer+=weight*Q(-a,denominator);summands+=1
    assert answer==0
    result=dict(status='INDEPENDENT_DIRECT_COORDINATE_RESIDUES_PASS',
        endpoint_units=36,individual_poles_simple=True,
        no_root_slide_preprocessing=True,no_colored_tree_grouping=True,
        stages=stages,frequency=frequencies,summands=summands,value=str(answer),
        zero=answer==0,seconds=time.monotonic()-started,
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        input_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in (inventory_path,proposal_path)},
        scope='Independent coordinate constant step and initial endpoint/simple-pole checks. Proper-cut pole elimination is separately audited and replayed.')
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
