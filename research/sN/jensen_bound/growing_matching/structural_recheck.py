"""Build and exact-check conditional growing-arity actual-model structural transfer.

Run under the shared Lean lock. This creates a content-bound workspace receipt;
a publication gate should re-run it against the final committed source closure.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import subprocess

ROOT=Path(__file__).resolve().parents[4]
HERE=Path(__file__).resolve().parent
MODULE='MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.Structural'
DRIVER=Path('verification/frontier/CountGrowingMatchingStructuralCheck.lean')
PREFIX='structural'
ALLOWED={'propext','Classical.choice','Quot.sound'}

def run(tag,args):
    result=subprocess.run(args,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (HERE/f'{PREFIX}_{tag}.log').write_text(result.stdout)
    (HERE/f'{PREFIX}_{tag}.exit').write_text(str(result.returncode)+'\n')
    if result.returncode:
        print(result.stdout)
        raise SystemExit(result.returncode)
    return result.stdout

run('module',['lake','build',MODULE,'MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.FiveInstance'])
log=run('exact',['lake','env','lean','-j1',str(DRIVER)])
checks=[]
for name,axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log):
    got={x.strip() for x in axioms.split(',') if x.strip()}
    assert got<=ALLOWED,(name,got)
    checks.append({'declaration':name,'axioms':sorted(got)})
required={
 'MaxCaterpillar.Frontier.RandomRestriction.GrowingMatching.'+name for name in [
 'localized_support_le_two','localized_dead_weights',
 'original_outer_zero_of_local_matching','localized_braidGraph_eq_comap',
 'structural_witness_of_generic_embedding','exists_structural_witness_threshold',
 'selected_event_witness_of_generic_embedding','localMatchingObstruction_five_two']}
required|={'GrowingMatchingChecks.'+name for name in [
 'linearOne_normalized','linearOne_max','not_obstruction_one_one']}
assert required=={x['declaration'] for x in checks},checks
pending=[ROOT/str(DRIVER),ROOT/(MODULE.replace('.','/')+'.lean')]
seen=set()
while pending:
    path=pending.pop()
    if path in seen:continue
    seen.add(path)
    for imp in re.findall(r'^import\s+(\S+)',path.read_text(),re.M):
        q=ROOT/(imp.replace('.','/')+'.lean')
        if q.is_file():pending.append(q)
spec=importlib.util.spec_from_file_location('project_source_verifier',ROOT/'scripts/verify.py')
verifier=importlib.util.module_from_spec(spec)
spec.loader.exec_module(verifier)
for source in seen:
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',verifier.uncomment(source.read_text())),source
seen|={ROOT/'lean-toolchain',ROOT/'lake-manifest.json'}
receipt={'status':'PASS',
'scope':'Conditional growing-arity actual-network structural transfer: H(k,q) on actual normalized homogeneous MAX_k braid/skip models forces an original surviving outer index and a literal q-edge ambient matching at the unchanged embedded dominant-gap point of an actual normalized MAX_N model.',
'evidence_kind':'Content-bound workspace receipt; final clean-commit publication gate remains a separate promotion step.',
'build_module':MODULE,'exact_driver':str(DRIVER),'axiom_checks':checks,
'new_hypothesis':'LocalMatchingObstruction k q quantifies only over actual indexed NormalizedNetwork k h1h2, translation normalization, primitive support<=2 of every first row, and all-real-input MAX_k equality. It concludes an outer actual braid interaction graph contains q ordinary disjoint edges. It has no event, counting or probability premise.',
'parameter_conditions':'Positive k,N (NeZero instances), q>0, actual complementary keep/tail embeddings, and absence of original support>=3 rows wholly inside the kept coordinates. q>0 is needed to infer survival from a nonempty local matching.',
'semantic_checks':['Expected-type driver expands H to its complete actual-model formula and matching data to ordinary unordered edge subsets of cardinality q.',
 'The structural witness uses the original Fin h2 outer index, the caller actualGapPoint e p T, and the original signed ambient braidEdgeWeight graph.',
 'A proved actual localization/comap equality and injective matching transport establish the ambient matching; neither is assumed.',
 'The standalone threshold conclusion has no generic-point/model-bridge hypothesis.',
 'An actual normalized MAX1 model with no hidden neurons proves H(1,1) is false.',
 'The independently closed real star certificate proves unconditional H(5,2), calibrating the hypothesis against the known case.'],
'proof_method':'Apply the actual local H(k,q) theorem to the literal normalized MAX_k localization after original support exclusion derives its braid rows. A positive q-matching supplies a nonzero local edge, which forces its original outer preactivation to vanish. Exact original signed edge aggregates identify the local graph with the ambient induced comap; ordinary unordered matching transport preserves all q edges and endpoints.',
'not_claimed':'No H(k,q) theorem for growing k or larger q, and no unconditional growing-arity quantitative lower bound, is asserted here.',
'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(seen)},
'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
'exact_log_sha256':hashlib.sha256(log.encode()).hexdigest()}
(HERE/f'{PREFIX}_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'status':'PASS','axiom_checks':len(checks),'project_source_closure':len(seen)},indent=2))
