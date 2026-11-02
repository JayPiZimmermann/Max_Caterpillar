"""Emit bounded kernel checks for rational selector identities.

Each chunk checks eight complete permutations, including masked coarse
compatibility and coordinate projection, then combines its eight lemmas.
"""
from pathlib import Path
import argparse
ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'MaxCaterpillar/Frontier/StarCertificate'

def atom_compat(p):return f'''theorem masked_compatible_{p} : ∀ (T : Fin 16) (t : Fin 10) (i : Fin 4),
    (maskedCoarse T {p} t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T {p} j).form subsetForms i := of_decide_eq_true (by with_unfolding_all rfl)

'''
def atom_projection(p):return f'''theorem chain_masked_projection_{p} : ∀ (T : Fin 16) (j i : Fin 4),
    (maskedChain T {p} j).form subsetForms i =
      if i ∈ maskSet T then (maskedChain 15 {p} j).form subsetForms i else 0 := of_decide_eq_true (by with_unfolding_all rfl)

'''
def write_atomic(p,s):
 p.parent.mkdir(parents=True,exist_ok=True);q=p.with_suffix('.lean.tmp');q.write_text(s);q.replace(p)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--chunks',type=int,default=15);args=ap.parse_args()
 for k in range(args.chunks):
  s='import MaxCaterpillar.Frontier.StarCertificate.XiMasks\n\n/-! Generated bounded rational selector checks. -/\nset_option autoImplicit false\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace MaxCaterpillar.Frontier.StarCertificate\nopen BigOperators\n\n'
  for p in range(k*8,k*8+8):s+=atom_compat(p)+atom_projection(p)
  s+=f'''theorem masked_compatible_chunk_{k} (T : Fin 16) (p : Fin 8) :
    ∀ (t : Fin 10) (i : Fin 4),
    (maskedCoarse T ⟨{k*8}+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt {k*8}) (by decide)⟩ t).form subsetForms i =
      ∑ j, coarseForms t j * (maskedChain T ⟨{k*8}+p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt {k*8}) (by decide)⟩ j).form subsetForms i := by
  fin_cases p
'''
  for p in range(k*8,k*8+8):s+=f'  · exact masked_compatible_{p} T\n'
  s+='\nend MaxCaterpillar.Frontier.StarCertificate\n'
  write_atomic(BASE/'XiSelectorChecks'/f'Chunk{k:02d}.lean',s)
 if args.chunks==15:
  s=''.join(f'import MaxCaterpillar.Frontier.StarCertificate.XiSelectorChecks.Chunk{k:02d}\n' for k in range(15))
  s+='\nset_option autoImplicit false\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace MaxCaterpillar.Frontier.StarCertificate\nopen BigOperators\n\n'
  for name,args_,body,atom in [
   ('masked_compatible','(T : Fin 16) (p : Fin 120) (t : Fin 10) (i : Fin 4)', '(maskedCoarse T p t).form subsetForms i =\n      ∑ j, coarseForms t j * (maskedChain T p j).form subsetForms i','masked_compatible'),
   ('chain_masked_projection','(T : Fin 16) (p : Fin 120) (j i : Fin 4)', '(maskedChain T p j).form subsetForms i =\n      if i ∈ maskSet T then (maskedChain 15 p j).form subsetForms i else 0','chain_masked_projection')]:
   s+=f'theorem {name} {args_} :\n    {body} := by\n  fin_cases p\n'
   for p in range(120):s+=f'  · exact {atom}_{p} T '+('t i' if name=='masked_compatible' else 'j i')+'\n'
   s+='\n'
  s+='end MaxCaterpillar.Frontier.StarCertificate\n';write_atomic(BASE/'XiSelectorProofs.lean',s)
if __name__=='__main__':main()
