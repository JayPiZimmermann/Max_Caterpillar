"""Verify frozen source/proof receipts; optionally rerun Ethos without an SMT solver."""
from pathlib import Path
import argparse
import gzip
import hashlib
import importlib.util
import json
import shutil
import tempfile
import time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--replay',action='store_true')
    args=parser.parse_args();manifest=json.loads((HERE/'manifest.json').read_text())
    assert manifest['certified_indices']==[275,277,280,307,353,355]
    assert manifest['unresolved_indices']==[]
    for rel,digest in manifest['dependencies'].items(): assert sha(ROOT/rel)==digest,rel
    for rel,digest in manifest['controls'].items(): assert sha(HERE/rel)==digest,rel
    for row in manifest['entries']:
        for key in ('source','normalized_source','cvc5_receipt','ethos_receipt'):
            assert sha(HERE/row[key])==row[key+'_sha256'],row[key]
        assert sha(HERE/row['proof'])==row['compressed_sha256']
        proof=gzip.decompress((HERE/row['proof']).read_bytes())
        assert hashlib.sha256(proof).hexdigest()==row['uncompressed_proof_sha256']
        cv=json.loads((HERE/row['cvc5_receipt']).read_text())
        et=json.loads((HERE/row['ethos_receipt']).read_text())
        assert cv['status']=='unsat' and cv['proof_roots']==1 and not cv['trust_rule_present']
        assert et['status']=='INDEPENDENT_ETHOS_PASS'
        assert cv['original_source_sha256']==et['original_source_sha256']==row['source_sha256']
        assert cv['proof_sha256']==et['proof_sha256']==row['uncompressed_proof_sha256']
    fresh=[]
    if args.replay:
        auditor_path=ROOT/'research/sN/frontier5/max5_exact_one_shared_proof_audit.py'
        spec=importlib.util.spec_from_file_location('same_label_auditor',auditor_path)
        audit=importlib.util.module_from_spec(spec);spec.loader.exec_module(audit)
        for row in manifest['entries']:
            with tempfile.TemporaryDirectory(prefix='same_label_replay_') as dirname:
                tmp=Path(dirname);audit.HERE=tmp
                for key in ('source','normalized_source','cvc5_receipt'):
                    shutil.copyfile(HERE/row[key],tmp/row[key])
                cv=json.loads((HERE/row['cvc5_receipt']).read_text())
                (tmp/cv['proof']).write_bytes(gzip.decompress((HERE/row['proof']).read_bytes()))
                audit.replay(tmp/row['source'],300)
                source=tmp/row['source']
                receipt=json.loads(source.with_name(source.stem+'_audit').with_suffix('.ethos.json').read_text())
                fresh.append(dict(index=row['index'],**receipt))
    result=dict(status='ALL_SIX_FROZEN_SOURCE_AND_PROOF_HASHES_PASS',
        fresh_ethos_replay=args.replay,indices=manifest['certified_indices'],
        manifest_sha256=sha(HERE/'manifest.json'),checker_sha256=sha(__file__),fresh=fresh)
    out=HERE/('fresh_replay_receipt.json' if args.replay else 'bundle_check.json')
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='fresh'}),flush=True)

if __name__=='__main__':main()
