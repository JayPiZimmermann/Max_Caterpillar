"""Independent exact evaluation of every retained failed synthesis candidate.

Uses no search code, SMT solver, global-cone checker, or floating arithmetic.
"""
from pathlib import Path
from fractions import Fraction as Q
import json,hashlib,time
HERE=Path(__file__).resolve().parent
PREFIXES=['overnight_fixed_cycle9_cegis_o2_p3','overnight_fixed_cycle9_cellcegis_o2_p3','overnight_fixed_cycle9_cellcegis_o0_p2','overnight_fixed_cycle9_cellcegis_o0_p3','overnight_fixed_cycle9_cellcegis_o1_p3','overnight_fixed_cycle9_gradcegis_o2_p3','overnight_fixed_cycle9_physical_o2_p4','overnight_fixed_cycle9_physicaltail_o2_p4']

def main():
    start=time.monotonic();records=[]
    for prefix in PREFIXES:
        report=json.loads((HERE/(prefix+'.json')).read_text());path=HERE/(prefix+'_steps.jsonl');assert hashlib.sha256(path.read_bytes()).hexdigest()==report['steps_sha256'];count=0
        for line in path.read_text().splitlines():
            rec=json.loads(line)
            if 'counterexample'not in rec:continue
            netpath=HERE/rec['candidate'];assert hashlib.sha256(netpath.read_bytes()).hexdigest()==rec['candidate_sha256'];net=json.loads(netpath.read_text());c=rec['counterexample'];x=list(map(Q,c['point']));first=[max(sum(Q(a)*b for a,b in zip(row,x)),Q(0))for row in net['first_layer']];second=[max(sum(Q(a)*b for a,b in zip(row,first)),Q(0))for row in net['second_layer']];actual=sum(Q(d)*v for d,v in zip(net['output'],second));target=max(x);assert actual==Q(c['network_value'])and target==Q(c['target_value'])and actual!=target;count+=1
        assert count==report.get('exact_counterexamples',report.get('counterexamples'));records.append({'campaign':prefix,'exact_counterexamples':count,'status':report['status']})
    out={'status':'INDEPENDENT_EXACT_SYNTHESIS_COUNTEREXAMPLES_PASS','campaigns':records,'counterexamples':sum(r['exact_counterexamples']for r in records),'seconds':time.monotonic()-start,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};(HERE/'overnight_fixed_cycle9_counterexamples_check.json').write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(json.dumps(out,sort_keys=True))
if __name__=='__main__':main()
