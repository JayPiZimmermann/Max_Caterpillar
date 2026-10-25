"""Replay positive and deliberately false full-physical-network controls."""
from pathlib import Path
import json,hashlib,time
from overnight_fixed_physical_verify import check
HERE=Path(__file__).resolve().parent

def main():
    start=time.monotonic();positive=['netB_10_6.json','overnight_fixed_cross_net9_14_simple.json','overnight_fixed_anchor_control12_network.json','overnight_fixed_physical_nonlinearhead_control.json'];negative=['overnight_fixed_anchor_control_bad_anchor_pair.json','overnight_fixed_anchor_control_bad_comparison_gradient.json'];passes=[{'network':name,'receipt':check(HERE/name)}for name in positive];failures=[]
    for name in negative:
        try:check(HERE/name)
        except AssertionError as exc:failures.append({'network':name,'failure':str(exc),'network_sha256':hashlib.sha256((HERE/name).read_bytes()).hexdigest()})
        else:raise AssertionError(('accepted deliberately false network',name))
    out={'status':'INDEPENDENT_EXACT_FULL_PHYSICAL_CONTROLS_PASS','positive':passes,'negative':failures,'seconds':time.monotonic()-start,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};(HERE/'overnight_fixed_physical_controls.json').write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(json.dumps(out,sort_keys=True))
if __name__=='__main__':main()
