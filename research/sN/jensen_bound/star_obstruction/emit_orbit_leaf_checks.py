#!/usr/bin/env python3
"""Emit bounded exact sign-descriptor checks on the actual geometry leaves."""
from __future__ import annotations
import argparse,hashlib,json
from emit_functional_tree import (ROOT,INPUT,OUT,Lean,atomic,load,partition,
    terminals,collect_chunks,outside,cleared,tree_term,Chunk,Solved,Impossible,Branch,SIGNS)
TARGET = ROOT/'MaxCaterpillar/Frontier/StarCertificate/XiOrbitLeafChecks'
REP = '(∀ r : Fin 67, ∀ z, actualSigns subsetForms z = orbitRepresentativePattern r → AllStarAnovaZero z)'
F = '(fun z t => evalForm (starAnovaCoefficients (actualSigns subsetForms z) t) z)'

def render_chunk(chunk,descriptors,sha):
    label=f'Chunk{chunk.index:04d}'
    base=f'Generated.{label}'
    lines=[]
    for leaf in terminals(chunk.tree)[0]:
        i=leaf.index; d=descriptors[i]
        lines += [f'def descriptor{i} : OrbitDescriptor := ⟨{d["representative"]}, {d["permutation"]}, {str(d["negative"]).lower()}⟩',
          f'''theorem checked{i} : orbitPatternTransform descriptor{i} ({base}.pattern{i}) =
    orbitRepresentativePattern descriptor{i}.representative :=
  of_decide_eq_true (by with_unfolding_all rfl)''',
          f'''theorem leaf{i} (hRep : {REP}) :
    ∀ z, actualSigns subsetForms z = {base}.pattern{i} → AllStarAnovaZero z :=
  orbit_reduce_pattern ({base}.pattern{i}) descriptor{i} checked{i} (hRep descriptor{i}.representative)''']
    lines.append(f'''theorem valid (hRep : {REP}) :
    {base}.tree.FunctionalValid starIntegerSubsetForms
      {F} {base}.regionContext := by
  apply Generated.Functional{label}.valid
'''+'\n'.join(f'  · exact leaf{leaf.index} hRep' for leaf in terminals(chunk.tree)[0]))
    text=f'''import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.Functional{label}
import MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport
/-! Generated exact sign/permutation transport checks; input SHA256 {sha}.
Real target transport is uniform and proved; only15sign comparisons perleaf
are computed. The representative premise is discharged by the67actual certificates. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.{label}
'''+ '\n\n'.join(lines)+f'''
#print axioms valid
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.{label}
'''
    return text


def top_proof(node,ctx,indent='  '):
    if isinstance(node,Chunk):
        base=f'Generated.Chunk{node.index:04d}'
        return [indent+f'have hp : ({ctx}) = {base}.regionContext :=',
                indent+'  of_decide_eq_true (by with_unfolding_all rfl)',
                indent+'rw [hp]',indent+f'exact XiOrbitLeafChecks.Chunk{node.index:04d}.valid hRep']
    if isinstance(node,Impossible):
        return [indent+f'exact (integerFarkasCheck_eq_true starIntegerSubsetForms ({ctx}) weights{node.index}).mp',indent+'  (by with_unfolding_all rfl)']
    if isinstance(node,Solved):raise ValueError('Solved leaf escaped bounded chunk')
    result=[indent+'refine ⟨?_, ?_, ?_⟩']
    for sign,child in zip((-1,0,1),node.children):
        lines=top_proof(child,f'Function.update ({ctx}) {node.depth} (some {SIGNS[sign]})',indent+'  ')
        result.append(indent+'· '+lines[0][len(indent)+2:]);result.extend(lines[1:])
    return result


def emit_coverage(top,sha):
    negative,zero=top.children[:2]
    chunks=collect_chunks(negative)+collect_chunks(zero)
    imports='\n'.join(f'import MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafChecks.Batch{j:03d}' for j in sorted({c.index//8 for c in chunks}))
    lines=[]
    for leaf in outside(negative)+outside(zero):
        _,weights=cleared(leaf.weights)
        lines.append(f'def weights{leaf.index} : Fin 15 → ℤ := {Lean.integers(weights)}')
    def rootterm(node):
        return tree_term(node).replace('Chunk','Generated.Chunk')
    for name,sign,subtree in [('negative',-1,negative),('zero',0,zero)]:
        ctx=f'Function.update (emptyContext 15) 0 (some {SIGNS[sign]})'
        lines += [f'def {name}Tree : IntegerCertificateTree 15 80 :=\n  {rootterm(subtree)}',
          f'''theorem {name}_valid (hRep : {REP}) :
    {name}Tree.FunctionalValid starIntegerSubsetForms {F} ({ctx}) := by
'''+ '\n'.join(top_proof(subtree,ctx))]
    text=imports+f'''
/-! Exhaustive real star transport assembly; input SHA256 {sha}.
Both closed halfspace branches are checked, including equality faces.
The real evenness theorem covers the remaining positive halfspace. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
namespace MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafCoverage
'''+ '\n\n'.join(lines)+f'''

theorem canonical_forms : integerForms starIntegerSubsetForms = subsetForms := by
  funext j i
  exact starIntegerSubsetForms_cast j i

theorem first_form (x : Fin 4 → ℝ) : evalForm (subsetForms 0) x = x 0 := by
  simp [evalForm, subsetForms, Fin.sum_univ_succ]

theorem all_real_of_representatives (hRep : {REP}) : ∀ z, AllStarAnovaZero z :=
  functional_halfspace_even_sound starIntegerSubsetForms 0 0
    (fun x => by rw [canonical_forms,first_form]) {F} negativeTree zeroTree
    (negative_valid hRep) (zero_valid hRep) starAnova_eval_neg

#print axioms all_real_of_representatives
end MaxCaterpillar.Frontier.StarCertificate.XiOrbitLeafCoverage
'''
    path=TARGET.parent/'XiOrbitLeafCoverage.lean';atomic(path,text);return path


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--probe-index',type=int)
    args=parser.parse_args()
    tree,_=load(INPUT);chunks,top=partition(tree,63,8)
    selected=collect_chunks(top.children[0])+collect_chunks(top.children[1])
    if args.probe_index is not None:selected=[chunks[args.probe_index]]
    data=json.loads(INPUT.with_name('orbit_manifest.json').read_text())
    sha=hashlib.sha256(INPUT.read_bytes()).hexdigest()
    assert data['input_sha256']==sha
    reps=data['representatives']
    if len(reps)!=67 or any(type(i) is not int or not 0<=i<900 for i in reps):
        raise ValueError('Invalid representative IDs')
    descriptors=data['descriptors']
    if len(descriptors)<900:
        raise ValueError('Incomplete descriptor catalogue')
    for i,d in enumerate(descriptors[:900]):
        if (type(d['representative']) is not int or not 0<=d['representative']<67 or
            type(d['permutation']) is not int or not 0<=d['permutation']<24 or
            type(d['negative']) is not bool or
            d['representative_leaf']!=reps[d['representative']]):
            raise ValueError(f'Invalid finite orbit descriptor {i}')
    outputs=[]
    if args.probe_index is not None:
        path=TARGET/f'Chunk{selected[0].index:04d}.lean'
        atomic(path,render_chunk(selected[0],data['descriptors'],sha));outputs.append(path)
    else:
        for start in range(0,len(selected),8):
            group=selected[start:start+8]
            assert group[0].index==start
            imports='\n'.join(f'import MaxCaterpillar.Frontier.StarCertificate.Checker.Generated.FunctionalChunk{c.index:04d}' for c in group)
            bodies=[]
            for c in group:
                text=render_chunk(c,data['descriptors'],sha)
                bodies.append(text[text.index('namespace '):])
            header=imports+'\nimport MaxCaterpillar.Frontier.StarCertificate.XiOrbitTransport\nset_option autoImplicit false\nset_option maxRecDepth 100000\nset_option maxHeartbeats 200000000\n'
            path=TARGET/f'Batch{start//8:03d}.lean'
            atomic(path,header+'\n'.join(bodies));outputs.append(path)
        outputs.append(emit_coverage(top,sha))
    record={'input_sha256':sha,'orbit_manifest_sha256':hashlib.sha256(INPUT.with_name('orbit_manifest.json').read_bytes()).hexdigest(),
            'producer_sha256':hashlib.sha256(__import__('pathlib').Path(__file__).read_bytes()).hexdigest(),
            'outputs':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in outputs}}
    name='orbit_leaf_probe_generation.json' if args.probe_index is not None else 'orbit_leaf_generation.json'
    atomic(INPUT.with_name(name),json.dumps(record,indent=2)+'\n')
    print(json.dumps({'outputs':len(outputs),'last':str(outputs[-1].relative_to(ROOT))}))

if __name__=='__main__':main()
