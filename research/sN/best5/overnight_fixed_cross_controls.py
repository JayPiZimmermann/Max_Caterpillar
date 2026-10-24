"""Exact positive and deliberately corrupted controls for the new checker."""
import copy
import hashlib
import json
import tempfile
from fractions import Fraction as Q
from pathlib import Path
from overnight_fixed_cross_verify import check


def main():
    good=check("netB_10_6.json");new=check("overnight_fixed_cross_net9_17.json")
    original=json.loads(Path("overnight_fixed_cross_net9_17.json").read_text());failures=[]
    with tempfile.TemporaryDirectory() as directory:
        for mutation in ("output_coefficient","carrier_coefficient","input_dimension"):
            net=copy.deepcopy(original)
            if mutation=="output_coefficient":net["output"][2]=str(Q(net["output"][2])+1)
            elif mutation=="carrier_coefficient":net["second_layer"][0][-2]="2"
            else:net["first_layer"][0].append(0)
            path=Path(directory)/"mutant.json";path.write_text(json.dumps(net))
            try:check(path)
            except AssertionError:failures.append(mutation)
            else:raise AssertionError(("MUTANT_ACCEPTED",mutation))
    result={"status":"EXACT_GLOBAL_CHECKER_CONTROLS_PASS","known_network":good,"new_network":new,
            "rejected_mutations":failures,"producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path("overnight_fixed_cross_controls.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps(result,sort_keys=True))


if __name__=="__main__":main()
