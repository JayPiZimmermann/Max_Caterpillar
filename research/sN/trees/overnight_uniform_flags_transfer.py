"""Exact vertex control of the anchored complete-flag transfer obstruction."""
from pathlib import Path
from collections import Counter
from fractions import Fraction as Q
import itertools,json,time
HERE=Path(__file__).parent

def apply(verts,dirs):
    if not dirs:return Counter({tuple(sorted(verts)):1})
    values=[sum(a*b for a,b in zip(v,dirs[0]))for v in verts];out=Counter()
    for sign,extreme in((1,max(values)),(-1,min(values))):
        face=tuple(v for v,s in zip(verts,values)if s==extreme)
        for key,c in apply(face,dirs[1:]).items():out[key]+=sign*c
    return Counter({k:v for k,v in out.items()if v})

def zonotope(N,root,apex,edges):
    out=set()
    for bits in itertools.product((0,1),repeat=len(edges)):
        v=[int(i==root)-int(i==apex)for i in range(N)]
        for bit,(a,b)in zip(bits,edges):
            if bit:v[a]+=1;v[b]-=1
        out.add(tuple(v))
    return tuple(sorted(out))

def main():
    start=time.monotonic();flags=json.loads((HERE/'dfs_review_flag_certificate.log').read_text())['flags'];core_edges=[(2,1),(3,2),(4,3)];edges=core_edges+[(j,1)for j in range(5,9)];Z=zonotope(9,1,0,edges);P=tuple(sorted(set(Z)|{(0,)*9}));Zcore=zonotope(5,1,0,core_edges);Pcore=tuple(sorted(set(Zcore)|{(0,)*5}));simplex9=tuple(tuple(int(i==j)for i in range(9))for j in range(9));simplex5=tuple(tuple(int(i==j)for i in range(5))for j in range(5));anchor=(0,1,0,0,0);rows=[];weighted=Q(0)
    assert max(sum(bits)for bits in itertools.product((0,1),repeat=7)if len([v for b,e in zip(bits,edges)if b for v in e])==len({v for b,e in zip(bits,edges)if b for v in e}))==2
    block=[5,6,7,8,1]
    def project(v):return tuple(v[i]+(sum(v[j]for j in range(5,9)) if i==1 else 0)for i in range(5))
    for flag in flags:
        local=flag['directions']+[[int(i==flag['final_coordinate'])for i in range(5)]];dirs=[]
        for u in local:
            d=[u[4]]*9
            for j,v in enumerate(block):d[v]=u[j]
            dirs.append(tuple(d))
        results=[]
        for poly in(P,simplex9):
            out=Counter()
            for face,c in apply(poly,dirs).items():out[tuple(sorted(set(map(project,face))))]+=c
            results.append(Counter({k:v for k,v in out.items()if v}))
        target_key=tuple(sorted(simplex5));eta=results[1].get(target_key,0);expected_target=Counter({target_key:eta,(anchor,):-eta});expected_target=Counter({k:v for k,v in expected_target.items()if v});assert results[1]==expected_target
        expected=Counter({Pcore:eta,Zcore:-eta});expected=Counter({k:v for k,v in expected.items()if v});assert results[0]==expected
        weighted+=Q(flag['weight'])*eta;rows.append({'flag':flag,'zero_fiber_coefficient':eta,'grafted_tree_transfer_exact':True,'simplex_transfer_exact':True})
    assert weighted
    def base_value(poly):
        value=Q(0)
        for p in itertools.permutations(range(5)):
            vertices=tuple(tuple(v[i]for i in p)for v in poly)
            for flag in flags:
                for face,c in apply(vertices,flag['directions']).items():
                    a=[v[flag['final_coordinate']]for v in face];value+=Q(flag['weight'])*c*(max(a)-min(a))
        return value
    core_value=base_value(Pcore);target_value=base_value(simplex5);assert core_value and target_value==120 and base_value(Zcore)==0
    out={'status':'EXACT_COMPLETE_FLAG_TRANSFER_OBSTRUCTION','core_unit':{'apex':0,'root':1,'edges':core_edges},'grafted_edges':edges,'grafted_matching_number':2,'weighted_six_flag_transfer_coefficient':str(weighted),'base_separator_core_value':str(core_value),'base_separator_target_value':str(target_value),'composed_grafted_bad_tree_value':str(weighted*core_value),'composed_maximum_value':str(weighted*target_value),'rows':rows,'scope':'These are exact identities of virtual polytopes after four exposed-face differences and merging the deleted coordinates. The general proof uses the identical zero-vertex normal cones of the cube and simplex, and applies to every complete block flag. It excludes a fixed-block/single-anchor scalar transfer, not all pairing-indexed flag assemblies.','seconds':time.monotonic()-start};Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2),flush=True)

if __name__=='__main__':main()
