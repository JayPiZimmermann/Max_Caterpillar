"""Produce and immediately check rational cone exclusions for the P4 K3 domain."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib,itertools,json,signal,time
import overnight_root9_equations as E
from overnight_fixed_k2_certify import certified_feasible

HERE=Path(__file__).resolve().parent


def certify(zs,ds):
    equation,forms,offsets=E.case_data(zs,ds);rows=[equation(i) for i in range(49)];m=len(forms)
    for i,(e,rhs) in enumerate(rows):
        if rhs and all(c*rhs<=0 for c in e.values()):
            sign=Q(1 if rhs>0 else -1)
            proof=['cone',[[i,str(sign)]],[[j,str(-sign*c)] for j,c in sorted(e.items())],[]]
            E.arithmetic.cone(proof,equation,forms);return proof
    equalities=[(['e',i],[-rhs]+[e.get(j,Q(0)) for j in range(m)]) for i,(e,rhs) in enumerate(rows)]
    inequalities=[(['y',i],[Q(0)]+[Q(i==j) for j in range(m)]) for i in range(m)]
    feasible,witness=certified_feasible(equalities,inequalities,m)
    if feasible:return None
    proof=['cone',[],[],[]]
    for (kind,i),c in witness:proof[1 if kind=='e' else 2].append([i,c])
    E.arithmetic.cone(proof,equation,forms);return proof


def main():
    start=time.monotonic();E.initialize();triples=json.loads((HERE/'overnight_root9_triples.json').read_text())
    output=HERE/'overnight_root9_cones.jsonl';counts={};done=set()
    if output.exists():
        for line in output.read_text().splitlines():
            r=json.loads(line);done.add((tuple(r['flats']),tuple(r['signs'])));counts[r['status']]=counts.get(r['status'],0)+1
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('300 second budget')));signal.alarm(300)
    try:
        with output.open('a') as out:
            for zs in triples:
                for ds in itertools.product((1,-1),repeat=3):
                    if (tuple(zs),ds) in done:continue
                    proof=certify(zs,ds)
                    r=dict(flats=zs,signs=ds,status='EXACT_CONE_EXCLUSION' if proof else 'RELAXATION_SURVIVOR')
                    if proof:r['proof']=proof
                    out.write(json.dumps(r,separators=(',',':'))+'\n');out.flush()
                    counts[r['status']]=counts.get(r['status'],0)+1
                    if sum(counts.values())%100==0:print(counts,flush=True)
    except TimeoutError:print('BUDGET_STOP_NO_COMPLETENESS_CLAIM',flush=True)
    finally:signal.alarm(0)
    result=dict(status='RATIONAL_CONE_DOMAIN_PROBE',counts=counts,expected_cases=8*len(triples),seconds=time.monotonic()-start,
                producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                proof_sha256=hashlib.sha256(output.read_bytes()).hexdigest())
    (HERE/'overnight_root9_cones.json').write_text(json.dumps(result,indent=2)+'\n');print(result,flush=True)


if __name__=='__main__':main()
