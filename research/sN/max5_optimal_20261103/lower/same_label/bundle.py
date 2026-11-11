"""Pin and compact completed proof cases, retaining original proof hashes."""
from pathlib import Path
import gzip
import hashlib
import json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
OLD=ROOT/'research/sN/frontier5'

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()

rows=[]
for index in (275,277,280,307,353,355):
    stem=HERE/f'case{index}_audit'
    if index==277 and (HERE/'case277_single_audit.ethos.json').exists():
        stem=HERE/'case277_single_audit'
    ep=stem.with_suffix('.ethos.json')
    if not ep.exists(): continue
    et=json.loads(ep.read_text())
    cvp=stem.with_suffix('.cvc5.json');cv=json.loads(cvp.read_text())
    assert et['status']=='INDEPENDENT_ETHOS_PASS'
    assert cv['status']=='unsat' and cv['proof_roots']==1 and not cv['trust_rule_present']
    source=HERE/cv['original_source'];normalized=HERE/cv['normalized_source']
    assert sha(source)==cv['original_source_sha256']==et['original_source_sha256']
    assert sha(normalized)==cv['normalized_source_sha256']==et['normalized_source_sha256']
    proof=HERE/cv['proof'];compressed=proof.with_suffix(proof.suffix+'.gz')
    data=proof.read_bytes() if proof.exists() else gzip.decompress(compressed.read_bytes())
    assert hashlib.sha256(data).hexdigest()==cv['proof_sha256']==et['proof_sha256']
    compressed.write_bytes(gzip.compress(data,compresslevel=9,mtime=0))
    assert hashlib.sha256(gzip.decompress(compressed.read_bytes())).hexdigest()==cv['proof_sha256']
    if proof.exists(): proof.unlink()
    rows.append(dict(index=index,source=source.name,source_sha256=sha(source),
        normalized_source=normalized.name,normalized_source_sha256=sha(normalized),
        proof=compressed.name,compressed_sha256=sha(compressed),
        uncompressed_proof_sha256=cv['proof_sha256'],uncompressed_bytes=len(data),
        compressed_bytes=compressed.stat().st_size,
        cvc5_receipt=cvp.name,cvc5_receipt_sha256=sha(cvp),
        ethos_receipt=ep.name,ethos_receipt_sha256=sha(ep),
        status='INDEPENDENT_ETHOS_PASS'))
deps=[OLD/'max5_exact_three_shared_local.py',OLD/'max5_three_shared_one_each_cover.json',
      OLD/'max5_exact_one_shared_proof_audit.py',
      OLD.parent/'best5/overnight_root_complete_ethos_manifest.json',
      OLD.parent/'best5/overnight_root_complete_ethos_verify.py']
out=dict(status='ALL_SIX_ARITHMETICALLY_REFUTED' if len(rows)==6 else 'PARTIAL_CERTIFIED_EXCLUSION',
    scope='Six minimal-root same-label exactly-three-shared-contact necessary models only. No general MAX5 width optimum.',
    expected_indices=[275,277,280,307,353,355],certified_indices=[r['index'] for r in rows],
    unresolved_indices=[i for i in (275,277,280,307,353,355) if i not in [r['index'] for r in rows]],
    entries=rows, dependencies={str(p.relative_to(ROOT)):sha(p) for p in deps},
    controls={p.name:sha(p) for p in [HERE/'run.py',HERE/'proof.py',Path(__file__)]})
(HERE/'manifest.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(status=out['status'],certified=out['certified_indices'],
    unresolved=out['unresolved_indices'],compressed_bytes=sum(r['compressed_bytes'] for r in rows))),flush=True)
