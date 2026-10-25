"""Independent standard-library exhaustive edge-zero orbit-cover check."""
from pathlib import Path
from itertools import permutations,combinations
import json,hashlib,time


def main():
    start=time.monotonic();path=Path('overnight_fixed_complete_edge_orbits.json');data=json.loads(path.read_text());edges=list(combinations(range(5),2));assert data['edge_order']==[list(e)for e in edges];powers=[3**i for i in range(10)];colors=list(permutations(range(3)));moves=[[edges.index(tuple(sorted((p[i],p[j]))))for i,j in edges]for p in permutations(range(5))];covered=set()
    for rec in data['orbits']:
        row=rec['colors'];assert len(row)==10 and all(c in range(3)for c in row);assert sum(v*p for v,p in zip(row,powers))==rec['code'];orbit=set()
        for move in moves:
            for color in colors:orbit.add(sum(color[row[i]]*powers[move[i]]for i in range(10)))
        assert len(orbit)==rec['orbit_size'];assert covered.isdisjoint(orbit);covered.update(orbit)
    assert covered==set(range(3**10));out={'status':'INDEPENDENT_EXACT_EDGE_COLOR_ORBIT_COVER_PASS','orbits':len(data['orbits']),'assignments':len(covered),'seconds':time.monotonic()-start,'inventory_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};Path('overnight_fixed_complete_edge_orbits_check.json').write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(json.dumps(out,sort_keys=True))
if __name__=='__main__':main()
