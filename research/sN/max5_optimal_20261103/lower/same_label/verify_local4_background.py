"""Fresh Ethos replay of the imported local-MAX4 288-case arithmetic lemma.

Preserves all upstream receipts and sources; writes only the new replay
receipt in this task directory. Mathematical model coverage remains the
separately recorded local4_one_root_audit.md dependency.
"""
from pathlib import Path
import importlib.util
import json
import shutil
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
OLD = ROOT/'research/sN/frontier5'

def main():
    auditor_path = OLD/'max5_exact_one_shared_proof_audit.py'
    spec = importlib.util.spec_from_file_location('local4_background_auditor', auditor_path)
    audit = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(audit)
    name = 'max5_exact_local4_one_root_germs'
    with tempfile.TemporaryDirectory(prefix='same_label_local4_') as dirname:
        tmp = Path(dirname)
        for suffix in ('.smt2', '_audit.smt2', '_audit.proof.cpc', '_audit.cvc5.json'):
            shutil.copyfile(OLD/(name+suffix), tmp/(name+suffix))
        audit.HERE = tmp
        audit.replay(tmp/(name+'.smt2'), 120)
        receipt = json.loads((tmp/(name+'_audit.ethos.json')).read_text())
    receipt.update(scope='Imported local-MAX4 288-case arithmetic certificate, freshly replayed.',
                   checker_sha256=audit.sha(__file__))
    (HERE/'local4_background_replay.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt))

if __name__ == '__main__':
    main()
