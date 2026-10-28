"""Enumerate pair-comparison first-layer graphs that can retain max minus a linear form.

Necessary factorization test on every strict braid cone. For each connected
component C of the active comparison graph, ell(C) must be one exactly
when C contains the maximizing label. This is a construction-family probe,
not the all-real first-layer classification (non-pair rows are omitted).
"""
import hashlib
import itertools
import json
import time
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
from overnight_fixed_bowtie_verify import rref


def main():
    start=time.monotonic();pairs=list(itertools.combinations(range(5),2));perms=list(itertools.permutations(range(5)))
    ranks=[{v:i for i,v in enumerate(p)}for p in perms];oriented=[(i,j)for i in range(5)for j in range(5)if i!=j];oid={e:i for i,e in enumerate(oriented)}
    components=[]
    for mask in range(1<<10):
        parent=list(range(5))
        def root(i):
            while parent[i]!=i:i=parent[i]
            return i
        for q,(i,j)in enumerate(pairs):
            if mask>>q&1:parent[root(i)]=root(j)
        part={}
        for i in range(5):part[root(i)]=part.get(root(i),0)|(1<<i)
        components.append(tuple(part.values()))
    ordermask=[]
    for rank in ranks:ordermask.append(sum((rank[i]<rank[j])<<q for q,(i,j)in enumerate(pairs)))
    solution_cache={};records={};counts=Counter()
    for width in(6,7):
        classes={};accepted=0
        for chosen in itertools.combinations(range(10),width):
            edge_mask=sum(1<<q for q in chosen)
            for orientation in range(1<<width):
                forward=sum(((orientation>>k)&1)<<q for k,q in enumerate(chosen));equations={31:1};valid=True
                for perm,order in zip(perms,ordermask):
                    active=edge_mask&~(forward^order)
                    for component in components[active]:
                        target=int(bool(component&(1<<perm[0])))
                        if component in equations and equations[component]!=target:valid=False;break
                        equations[component]=target
                    if not valid:break
                if not valid:continue
                key=tuple(sorted(equations.items()))
                if key not in solution_cache:
                    matrix=rref([[Q(int(mask>>i&1))for i in range(5)]+[Q(value)]for mask,value in key])
                    solution_cache[key]=None if any(not any(row[:5])and row[5]for row in matrix)else matrix
                solution=solution_cache[key]
                if solution is None:continue
                accepted+=1;edges=[pairs[q]if forward>>q&1 else pairs[q][::-1]for q in chosen]
                canonical=min(sum(1<<oid[p[i],p[j]]for i,j in edges)for p in perms)
                if canonical not in classes:
                    coordinate=[i for i in range(5)if all(int(bool(mask&(1<<i)))==value for mask,value in key)]
                    classes[canonical]={"edges":edges,"coordinate_carriers":coordinate,"ell_equations":[list(map(str,row))for row in solution],"labeled_count":0}
                classes[canonical]["labeled_count"]+=1
        records[str(width)]={"accepted_labeled_orientations":accepted,"classes":list(classes.values())};counts[width]=len(classes)
    result={"status":"PAIR_GRAPH_FACTORIZATION_PROBE_COMPLETE","rows":records,"class_counts":counts,"seconds":time.monotonic()-start,
            "scope":"Distinct oriented pair rows only; necessary full-braid factorization condition; not a global network certificate",
            "producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path("overnight_fixed_nine_graphs.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps({"status":result["status"],"class_counts":counts,"labeled_counts":{k:v["accepted_labeled_orientations"]for k,v in records.items()},"seconds":result["seconds"]}),flush=True)


if __name__=="__main__":main()
