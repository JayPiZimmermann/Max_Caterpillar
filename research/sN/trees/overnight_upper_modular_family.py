#!/usr/bin/env python3
"""Complete function-orbit inventory for modular-affine BFS closure at N7."""
from fractions import Fraction
from pathlib import Path
import hashlib
import json
import time

from exponential_families_probe import canonical, permute
from exponential_families import normalize
from overnight_upper_linear_groups import action, modular_affine_group

HERE = Path(__file__).parent


def main():
    started = time.monotonic()
    source = HERE/'overnight_upper_modular_group_inventory_7.json'
    data = json.loads(source.read_text())
    group = modular_affine_group(7)
    orbits = []
    graphs = set()
    for entry in data['covered']:
        apex, edges = entry['representative']
        graphs.update(action((apex, edges), pi) for pi in group)
        base = set()
        for root in set(range(7))-{apex}:
            h = [0]*7
            h[apex],h[root] = -1,1
            for mask in range(32):
                oriented = [(v,u) if mask >> j & 1 else (u,v)
                            for j,(u,v) in enumerate(edges)]
                base.add(canonical(h,oriented))
        local = {}
        for key in sorted(base):
            orbit = tuple(sorted({permute(key, pi) for pi in group}))
            local.setdefault(orbit[0],orbit)
        orbits.extend(local.values())
    orbits.sort(key=lambda o:o[0])
    assert len({o[0] for o in orbits}) == len(orbits)
    witness_path = HERE/'all_tree_dfs/nc_fast_7.json'
    witness = json.loads(witness_path.read_text())
    inside=outside=0
    for c,indices in zip(witness['coefficient_proposal'],witness['orbits']):
        if not Fraction(c): continue
        for i in indices:
            u = witness['units'][i]
            if (u['apex'],normalize(u['edges'])) in graphs: inside+=1
            else: outside+=1
    out=dict(status='EXACT_FAMILY_ENUMERATION_NO_SPAN_CLAIM', n=7,
             family='full_bfs_modular_affine_closure', group_order=42,
             graph_count=len(graphs), graph_orbit_count=len(data['covered']),
             orbit_count=len(orbits), unit_count=sum(map(len,orbits)), orbits=orbits,
             existing_nc7_witness_inside=inside,existing_nc7_witness_outside=outside,
             source=source.name,source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
             witness_source_sha256=hashlib.sha256(witness_path.read_bytes()).hexdigest(),
             producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             elapsed_seconds=time.monotonic()-started)
    (HERE/'overnight_upper_modular_bfs_7_family.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='orbits'}),flush=True)


if __name__=='__main__': main()
