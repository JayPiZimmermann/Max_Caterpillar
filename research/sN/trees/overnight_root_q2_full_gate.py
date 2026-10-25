"""Bounded, necessary full mixed-family N9 gate for the existing Q2 score.

This neither enlarges the score alphabet nor overwrites frozen q9 receipts.
A sampled kernel vector is only a proposal until checked as a rational or
whole-function identity. Even a consistent score is not a descent proof.
"""
from pathlib import Path
from fractions import Fraction
import json, math, os, resource, subprocess, sys, time

os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
os.environ.setdefault('OMP_NUM_THREADS', '1')
import numpy as np
sys.path.append(str(Path('research/sN/dfs/h5-growth/venv/lib/python3.12/site-packages')))
from flint import nmod_mat, ctx
from dfs_review_fourier import points
from overnight_uniform_q9_benchmark import valid
from overnight_uniform_fay import vec, KEYS
from overnight_uniform_fay_q2_verify import COEFF, target_formula

HERE = Path(__file__).absolute().parent
BASE = HERE / 'overnight_root_q2_full_gate'
P = 1000003


def reconstruct(a):
    a %= P
    if a > P // 2:
        a -= P
    if abs(a) <= 1000:
        return Fraction(a)
    r0, r1, t0, t1 = P, a % P, 0, 1
    bound = math.isqrt(P // 2)
    while abs(r1) > bound:
        q = r0 // r1
        r0, r1, t0, t1 = r1, r0 - q * r1, t1, t0 - q * t1
    if t1 and abs(t1) <= bound and math.gcd(r1, t1) == 1:
        value = Fraction(r1, t1)
        if (value.numerator - a * value.denominator) % P == 0:
            return value
    return None


def main(total):
    ctx.threads = 1
    resource.setrlimit(resource.RLIMIT_AS, (3 * 2**30, 3 * 2**30))
    started = time.monotonic()
    inventory = json.loads((HERE / 'overnight_uniform_q9_inventory.json').read_text())
    classes = json.loads((HERE / 'overnight_uniform_q9_quotient.json').read_text())['class_data']
    old_state = json.loads((HERE / 'overnight_uniform_q9_rows_state.json').read_text())
    old = old_state['rows']
    assert old < total <= 4200
    width = len(inventory['units']) + 1
    pts = []
    for pt in points(9, total + 300):
        if valid(pt):
            pts.append(pt)
        if len(pts) == total:
            break
    assert len(pts) == total
    assert [list(p) for p in pts[:old]] == json.loads((HERE / old_state['points']).read_text())
    point_file = HERE / f'{BASE.name}_{total}.points.txt'
    point_file.write_text(f'{total-old} 9\n' + '\n'.join(' '.join(map(str, p)) for p in pts[old:]) + '\n')
    batch = HERE / f'{BASE.name}_{total}.u32'
    if not batch.exists() or batch.stat().st_size != (total-old)*width*4:
        subprocess.run(['/tmp/overnight_lower_dp_engine', str(HERE / 'overnight_uniform_q9_inventory.bin'), str(point_file), str(batch)], check=True, timeout=300)
    print('evaluation complete', total, time.monotonic()-started, flush=True)
    cols = [c['representative'] for c in classes if c['matching'] < 4]
    cols += [c['representative'] for c in classes if c['matching'] == 4]
    cols += [width-1]
    old_rows = np.memmap(HERE / old_state['matrix'], dtype='<u4', mode='r', shape=(old, width))
    new_rows = np.memmap(batch, dtype='<u4', mode='r', shape=(total-old, width))
    A = nmod_mat(total, len(cols), P)
    for i in range(total):
        row = old_rows[i] if i < old else new_rows[i-old]
        for j, col in enumerate(cols):
            A[i, j] = int(row[col])
    print('matrix built', A.nrows(), A.ncols(), time.monotonic()-started, flush=True)
    R, rank = A.rref()
    del A
    weights = [COEFF.get(key, Fraction(0)) for key in KEYS]
    exact_scores = []
    for col in cols[:-1]:
        exact_scores.append(sum(w*int(v) for w, v in zip(weights, vec(inventory['units'][col]))))
    exact_scores.append(target_formula(4) / math.factorial(9))
    assert exact_scores[-1] == Fraction(-1, 810)
    score = np.array([q.numerator*pow(q.denominator, -1, P) % P for q in exact_scores], dtype=np.int64)
    pivots = []
    cursor = 0
    for i in range(rank):
        while not R[i, cursor]:
            cursor += 1
        pivots.append(cursor)
        coeff = int(score[cursor])
        cursor += 1
        if coeff:
            score = (score - coeff*np.array([int(R[i, j]) for j in range(len(cols))], dtype=np.int64)) % P
    bad = []
    for j in np.flatnonzero(score):
        relation = {int(j): 1}
        for i, k in enumerate(pivots):
            value = -int(R[i, int(j)]) % P
            if value:
                relation[k] = value
        bad.append((len(relation), int(j), relation))
    proposals = []
    for size, j, relation in sorted(bad, key=lambda x: x[:2])[:12]:
        rational = {k: reconstruct(v) for k, v in relation.items()}
        item = dict(support=size, pairing_mod=int(score[j]), relation_mod={str(cols[k]): v for k, v in relation.items()})
        if all(v is not None for v in rational.values()):
            scale = math.lcm(*(v.denominator for v in rational.values()))
            integer = {cols[k]: int(scale*v) for k, v in rational.items()}
            item['integer_proposal'] = integer
            item['exact_score_pairing'] = str(sum(int(scale*v)*exact_scores[k] for k, v in rational.items()))
            item['target_coefficient'] = integer.get(width-1, 0)
        proposals.append(item)
    out = dict(status='NECESSARY_MODULAR_FULL_MIXED_N9_Q2_GATE', prime=P, rows=total,
               columns=len(cols), rank=rank, score_in_sampled_rowspan=not bool(bad),
               target_score=str(exact_scores[-1]), violations=len(bad), proposals=proposals,
               seconds=time.monotonic()-started, peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
               scope='No score descent, rank upper bound, or relation identity is inferred from finite evaluations.')
    (HERE / f'{BASE.name}_{total}.json').write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps({k: v for k, v in out.items() if k != 'proposals'}, indent=2), flush=True)
    print('small proposal sizes', [p['support'] for p in proposals], flush=True)


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 3400)
