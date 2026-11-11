"""Six support cases of the same-label three-shared-contact MAX5 sector.

Imports the already audited necessary model unchanged. No finite sample SAT
answer is interpreted as a network. UNSAT needs independent CPC/Ethos replay.
All outputs stay in this directory, with frozen source hashes in each record.
"""
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path
import argparse
import hashlib
import importlib
import json
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
OLD = ROOT / 'research/sN/frontier5'
INDICES = (275, 277, 280, 307, 353, 355)

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def work(job):
    index, budget, mode = job
    sys.path.insert(0, str(OLD))
    model = importlib.import_module('max5_exact_three_shared_local')
    cover_path = OLD / 'max5_three_shared_one_each_cover.json'
    cover = json.loads(cover_path.read_text())
    rec = cover['kinds']['three_roots']['records'][index]
    assert rec['status'] == 'REMAINS'
    assert sum(len(s) == 2 for s in rec['supports']) == 3
    solver, variables, meta = model.build(
        'one_each_same', samples='boolean', shared_germs=True,
        timeout=1000*budget, rigid=True, supports=rec['supports'],
        coefficient_gauge=True)
    prefix = HERE / f'case{index}'
    source = prefix.with_suffix('.smt2')
    raw = solver.to_smt2()
    source.write_text(raw)
    out = dict(index=index, scope='One necessary support class only; not a global MAX5 exclusion.',
               model_source=str((OLD/'max5_exact_three_shared_local.py').relative_to(ROOT)),
               model_sha256=sha(OLD/'max5_exact_three_shared_local.py'),
               cover_sha256=sha(cover_path), producer_sha256=sha(__file__),
               source=source.name, source_sha256=sha(source), **meta)
    prefix.with_suffix('.metadata.json').write_text(json.dumps(out, indent=2)+'\n')
    if mode == 'emit':
        return dict(index=index, status='EMITTED')
    started = time.monotonic()
    answer = solver.check()
    out.update(status=str(answer), seconds=time.monotonic()-started)
    if answer == model.z.sat:
        md = solver.model()
        out['model'] = {str(v):str(md.eval(v, model_completion=True)) for v in variables}
    elif answer == model.z.unknown:
        out['reason'] = solver.reason_unknown()
    prefix.with_suffix('.z3.json').write_text(json.dumps(out, indent=2)+'\n')
    return dict(index=index, status=out['status'], seconds=out['seconds'])

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--budget', type=int, default=60)
    p.add_argument('--workers', type=int, default=2)
    p.add_argument('--mode', choices=['emit','z3'], default='z3')
    p.add_argument('--index', type=int, choices=INDICES)
    a = p.parse_args()
    indices = INDICES if a.index is None else (a.index,)
    rows=[]
    with ProcessPoolExecutor(max_workers=a.workers) as pool:
        fs=[pool.submit(work,(i,a.budget,a.mode)) for i in indices]
        for f in as_completed(fs):
            row=f.result(); rows.append(row); print(json.dumps(row),flush=True)
            (HERE/'run_results.json').write_text(json.dumps(dict(
                status='COMPLETE' if len(rows)==len(indices) else 'RUNNING',
                expected=len(indices), budget=a.budget, results=sorted(rows,key=lambda r:r['index'])),indent=2)+'\n')

if __name__ == '__main__':
    main()
