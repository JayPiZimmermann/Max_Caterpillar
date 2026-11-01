"""Small reproducible K4 cone probe; no complete-domain lower bound is claimed."""
from collections import defaultdict
from pathlib import Path
import itertools,json,random,signal,time
import overnight_root9_equations as E
from overnight_root9_cones import certify

HERE=Path(__file__).resolve().parent


def main():
    start=time.monotonic();E.initialize()
    inv=json.loads((HERE/'overnight_root9_inventory.json').read_text())
    covers={int(z):r['cover'] for z,r in inv['flats'].items()};zs=sorted(covers)
    buckets=defaultdict(list)
    for i,z in enumerate(zs):
        for w in zs[i:]:buckets[covers[z]|covers[w]].append((z,w))
    unions=list(buckets);full=(1<<25)-1;eligible={};rng=random.Random(2026102517);samples=set()
    while len(samples)<512:
        u=rng.choice(unions)
        if u not in eligible:eligible[u]=[v for v in unions if u|v==full]
        if not eligible[u]:continue
        v=rng.choice(eligible[u]);quad=tuple(sorted(rng.choice(buckets[u])+rng.choice(buckets[v])))
        samples.add(quad)
    counts={'rational_cone_exclusions':0,'unresolved_relaxations':0};survivors=[];done=0
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('120 second probe')));signal.alarm(120)
    try:
        for quad in sorted(samples):
            for signs in itertools.product((1,-1),repeat=4):
                proof=certify(quad,signs);done+=1
                if proof:counts['rational_cone_exclusions']+=1
                else:counts['unresolved_relaxations']+=1;survivors.append(dict(flats=quad,signs=signs))
                if done%1000==0:print('PROBED',done,counts,flush=True)
    except TimeoutError:print('PROBE_BUDGET_STOP',flush=True)
    finally:signal.alarm(0)
    out=dict(status='INCOMPLETE_K4_CONE_DIAGNOSTIC_ONLY',seed=2026102517,
             sampled_quadruples=len(samples),checked_sign_cases=done,counts=counts,
             survivors=survivors,seconds=time.monotonic()-start,
             scope='Samples only512 of296861 covering quadruples. A relaxation survivor is not a network or proof of feasibility.')
    (HERE/'overnight_root9_k4_probe.json').write_text(json.dumps(out,indent=2)+'\n')
    print({k:v for k,v in out.items() if k!='survivors'},flush=True)


if __name__=='__main__':main()
