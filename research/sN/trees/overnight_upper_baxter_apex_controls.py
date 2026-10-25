#!/usr/bin/env python3
"""Direct integer vertex/facet controls of the graphic tiling evaluator."""
from itertools import combinations
from pathlib import Path
import hashlib,json,random,time
import overnight_upper_baxter_apex_geometry as geom

HERE=Path(__file__).parent

def main():
    start=time.monotonic();records=[];rng=random.Random(25102549)
    graphs=[((0,1),(0,2),(0,3),(1,2),(2,3)),tuple(combinations(range(4),2))]
    for graph in graphs:
        zero=(0,)*4
        direct=geom.direct_facets_3d([v[1:] for v in geom.vertices(4,graph)])
        expected={}
        for mask,fixed,tiles in geom.facets(4,graph):
            normal=tuple(int(mask>>i&1)-int(mask&1) for i in range(1,4))
            height=sum(fixed[i] for i in range(4) if mask>>i&1)
            expected[(normal,height)]=True
        assert set(direct)==set(expected),'complete facet inventory versus vertex triples'
        heads=[(-2,2,0,0),(-4,4,0,0),(-3,0,0,3),(2,-1,-1,0)]
        for head in heads:
            atoms=geom.atoms(4,graph,head);checks=0
            while checks<3:
                rest=[rng.randrange(1,30) for _ in range(3)];point=(-sum(rest),*rest)
                try:
                    first=geom.evaluate_atoms(4,atoms,point)
                    second=geom.direct_kernel_4(graph,head,point)
                except ZeroDivisionError:continue
                assert first==second,(graph,head,point,first,second)
                checks+=1
            records.append(dict(graph=graph,head=head,facets=len(direct),
                                forest_atoms=len(atoms),exact_rational_points=checks))
            print('DIRECT POLYTOPE CONTROL',records[-1],'SECONDS',time.monotonic()-start,flush=True)
    result=dict(status='DIRECT_VERTEX_FACET_GRAPHIC_TILING_CONTROLS_PASSED',
        records=records,seconds=time.monotonic()-start,
        evaluator_sha256=hashlib.sha256((HERE/'overnight_upper_baxter_apex_geometry.py').read_bytes()).hexdigest(),
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        scope='Complete facet inventory checked against all vertex triples; exact rational kernel checks use independent tetrahedron triangulation. Finite convention controls, not a uniform construction.')
    (HERE/'overnight_upper_baxter_apex_controls.json').write_text(json.dumps(result,indent=2)+'\n')

if __name__=='__main__':main()
