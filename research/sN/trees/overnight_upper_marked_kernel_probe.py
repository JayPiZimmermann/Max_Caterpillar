#!/usr/bin/env python3
"""Exact coning kernels retaining the two characters of a marked ear edge."""
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
import hashlib, json, math, random, time
from flint import nmod_mat
import overnight_upper_marked_kernel_inventory as inventory
import overnight_upper_product_family as base
from overnight_upper_modular_cache import Evaluator

HERE = Path(__file__).parent
PRIME = 1000000007


def plane_orbit(plane):
    result = []
    for pi in (tuple(range(6)), inventory.REFLECTION):
        values = [0]*6
        for i, value in enumerate(plane):
            values[pi[i]] = value
        values = [v-values[0] for v in values]
        common = math.gcd(*values)
        if next(v for v in values if v) < 0:
            common = -common
        result.append(tuple(v//common for v in values))
    return min(result)


def main():
    start = time.monotonic()
    source = HERE/'overnight_upper_marked_kernel_inventory_6.json'
    data = json.loads(source.read_text())
    completed = []
    for sector in data['sectors']:
        character = sector['character']
        descriptors = sector['descriptors']
        chains = [inventory.projected_chain(d, character) for d in descriptors]
        columns = [base.expression(c) for c in chains]
        planes = sorted({p for c in columns for p in c})
        representatives = {}
        for plane in planes:
            representatives.setdefault(plane_orbit(plane), plane)
        row_plan = []
        for plane in representatives.values():
            active = sum(bool(c.get(plane)) for c in columns)
            row_plan.append((plane, min(active+4, 64)))
        width = len(columns)
        assert sum(q for _, q in row_plan)*(width+1) <= 8_000_000
        print('MARKED SECTOR', character, 'COLUMNS', width, 'PLANES', len(planes),
              'ROW ORBITS', len(row_plan), 'ROWS', sum(q for _, q in row_plan),
              'SECONDS', time.monotonic()-start, flush=True)
        evaluate = Evaluator()
        rng = random.Random(251040+character)
        rows, points = [], []
        for plane, quota in row_plan:
            accepted = 0
            while accepted < quota:
                point = tuple(rng.randrange(1, 2000) for _ in range(4))
                try:
                    row = [evaluate(c.get(plane, {}), point, PRIME) for c in columns]
                except ZeroDivisionError:
                    continue
                rows.append(row)
                points.append((plane, point))
                accepted += 1
        rr, rank = nmod_mat(rows, PRIME).rref()
        pivots = [next(j for j in range(width) if rr[i, j]) for i in range(rank)]
        free = [j for j in range(width) if j not in pivots]
        record = dict(status='MODULAR_MARKED_EDGE_KERNEL_DIAGNOSTIC', n=6,
                      character=character, descriptors=descriptors,
                      rank=rank, proposed_kernel_dimension=len(free), prime=PRIME,
                      points=points, modular_rows=rows,
                      source_inventory_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                      producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                      scope='The entire marked-edge reflection-character sector of the fixed six-type two-page N6 subfamily. Both characters are treated separately; no D6 averaging is imposed.')
        dest = HERE/('overnight_upper_marked_kernel_'+('minus' if character == -1 else 'plus')+'_6.json')
        dest.write_text(json.dumps(record, separators=(',', ':'))+'\n')
        print('MARKED RANK', character, rank, 'KERNEL', len(free),
              'SECONDS', time.monotonic()-start, flush=True)
        gate = base.Verifier(500)
        relations = []
        supports = []
        formal = 0
        for j in free:
            coefficients = {j: Q(1)}
            for i, pivot in enumerate(pivots):
                value = base.ratrec(int(rr[i, j]), PRIME)
                assert value is not None, ('marked rational reconstruction', character, j, pivot)
                if value:
                    coefficients[pivot] = -value
            chain = defaultdict(Q)
            for index, coefficient in coefficients.items():
                for key, value in chains[index].items():
                    chain[key] += coefficient*value
            chain = {k: v for k, v in chain.items() if v}
            if not chain:
                formal += 1
            else:
                expression = base.expression(chain)
                orbit_reps = {}
                for plane in expression:
                    orbit_reps.setdefault(plane_orbit(plane), plane)
                for plane in orbit_reps.values():
                    assert gate.check(expression[plane]), ('marked exact kernel', character, j, plane)
            relations.append([[i, str(c)] for i, c in sorted(coefficients.items())])
            supports.append(len(chain))
            if len(relations) % 50 == 0:
                print('MARKED EXACT KERNELS', character, len(relations), '/', len(free),
                      'FORMAL ZERO', formal, 'SECONDS', time.monotonic()-start, flush=True)
        record.update(status='EXACT_MARKED_EDGE_CONING_KERNEL_SPACE',
                      relations_sparse=relations, free_columns=free,
                      formal_cube_supports=supports, formally_zero_relations=formal,
                      seconds=time.monotonic()-start)
        dest.write_text(json.dumps(record, separators=(',', ':'))+'\n')
        completed.append(dict(character=character, rank=rank, kernel_dimension=len(free),
                              formal_zero=formal, file=dest.name))
        print('MARKED SECTOR DONE', character, rank, len(free), 'SECONDS', time.monotonic()-start, flush=True)
    print('ALL MARKED SECTORS EXACT', completed, 'SECONDS', time.monotonic()-start, flush=True)


if __name__ == '__main__':
    main()
