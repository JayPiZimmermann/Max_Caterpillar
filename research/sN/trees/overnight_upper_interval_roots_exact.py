#!/usr/bin/env python3
"""Independent cut enumeration and exact kernel gate for the N5 root rule."""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
import hashlib, json, sys, time
from flint import fmpq_mat
import overnight_upper_interval_roots as source
from overnight_upper_interval_states import pruefer, crosses
from overnight_upper_triangle_attachment_exact import evaluate

HERE = Path(__file__).parent
sys.path.insert(0, str(HERE/'all_tree_dfs'))
from rational_identity import term, Verifier


def cut_inventory(vertices, root):
    result = []
    for local in pruefer(len(vertices)):
        if any(crosses(e, f) for e, f in combinations(local, 2)):
            continue
        graph = [(vertices[u], vertices[v]) for u, v in local]
        cuts = []
        for edge in graph:
            component = {edge[0]}
            changed = True
            while changed:
                changed = False
                for other in graph:
                    if other == edge:
                        continue
                    if bool(other[0] in component) != bool(other[1] in component):
                        component.update(other)
                        changed = True
            if root in component:
                component = set(vertices)-component
            cuts.append(tuple(sorted(component)))
        result.append(cuts)
    return result


def main():
    start = time.monotonic()
    path = HERE/'overnight_upper_interval_roots.json'
    record = next(r for r in json.loads(path.read_text())['records'] if r['n'] == 5)
    n = 5
    descriptors = [tuple(d) for d in record['descriptors']]
    index = {d: i for i, d in enumerate(descriptors)}
    columns = [defaultdict(Q) for _ in descriptors]
    forms = [tuple(int(i == j) for j in range(n-1))+(0,) for i in range(n-1)]
    forms.append((-1,)*(n-1)+(0,))
    def add_forms(vertices):
        return tuple(sum(forms[v][j] for v in vertices) for j in range(n))
    for size in range(1, n//2+1):
        for shift in range(n):
            cyclic = tuple((shift+i) % n for i in range(n))
            left, right = cyclic[:size], cyclic[size:]
            external = add_forms(right)
            for r in range(size):
                for s in range(n-size):
                    first = cut_inventory(left, left[r])
                    second = cut_inventory(right, right[s])
                    for cuts1 in first:
                        for cuts2 in second:
                            for signs in product((-1, 1), repeat=n-2):
                                i = sum(v == 1 for v in signs[:size-1])
                                j = sum(v == 1 for v in signs[size-1:])
                                descriptor = source.canonical(n, (size, r, s, i, j))
                                denominator = []
                                for cut, sign in zip(cuts1+cuts2, signs):
                                    q = add_forms(cut)
                                    denominator += [(q, 1), (tuple(x+sign*y for x, y in zip(q, external)), 1)]
                                key, coefficient = term(1, tuple(-v for v in external), n-4, denominator)
                                columns[index[descriptor]][key] += coefficient
    # Check the independent direct-tree expansion against two complete DP rows.
    for omega, integer_row in zip(record['points'][:2], record['integer_rows'][:2]):
        target = Q(1)
        for value in omega:
            target /= value
        scale = target/Q(integer_row[-1])
        for expression, value in zip(columns, integer_row[:-1]):
            assert evaluate(expression, omega[:-1]) == scale*value, 'DP/direct-cut disagreement'
    rr, rank = fmpq_mat(record['integer_rows']).rref()
    width = len(columns)
    pivots = [next(j for j in range(width+1) if rr[i, j]) for i in range(rank)]
    assert width in pivots
    free = [j for j in range(width) if j not in pivots]
    verifier = Verifier(300)
    relations = []
    for j in free:
        coefficients = [Q(0)]*width
        coefficients[j] = Q(1)
        for i, pivot in enumerate(pivots):
            if pivot < width:
                coefficients[pivot] = -Q(str(rr[i, j]))
        expression = defaultdict(Q)
        for coefficient, column in zip(coefficients, columns):
            for key, value in column.items():
                expression[key] += coefficient*value
        assert verifier.check(expression), ('failed exact root-state relation', j)
        relations.append([[i, str(c)] for i, c in enumerate(coefficients) if c])
    result = dict(status='EXACT_INTERVAL_ROOT_POSITION_RULE_OBSTRUCTION', n=5,
                  ranks=[rank-1, rank], columns=width, exact_relations=relations,
                  independent_complete_DP_rows_checked=2,
                  source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  scope=json.loads(path.read_text())['scope'], seconds=time.monotonic()-start)
    (HERE/'overnight_upper_interval_roots_exact_5.json').write_text(json.dumps(result, indent=2)+'\n')
    print(result['status'], result['ranks'], 'KERNELS', len(relations), 'SECONDS', result['seconds'], flush=True)


if __name__ == '__main__':
    main()
