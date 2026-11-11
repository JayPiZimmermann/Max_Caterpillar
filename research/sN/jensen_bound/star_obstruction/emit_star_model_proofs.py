"""Emit bounded exact checks connecting permutation prefixes to star slopes."""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'MaxCaterpillar/Frontier/StarCertificate'
def write(p,s):
 p.parent.mkdir(parents=True,exist_ok=True);q=p.with_suffix('.lean.tmp');q.write_text(s);q.replace(p)
def main():
 for chunk in range(4):
  s='''import MaxCaterpillar.Frontier.StarCertificate.StarCoefficients
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
'''
  for p in range(30*chunk,30*chunk+30):
   for name,weights in [('starVCoefficient','1 else 0'),('starVPrimeCoefficient','0 else 1')]:
    s+=f'''theorem {name}_coupling_{p} : ∀ (r i : Fin 4),
    {name} {p} r i = (maskedChain 15 {p} r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask {p}) then {weights}) :=
  of_decide_eq_true (by with_unfolding_all rfl)

'''
  s+='end MaxCaterpillar.Frontier.StarCertificate\n';write(BASE/'StarModelChecks'/f'Chunk{chunk:02d}.lean',s)
 s=''.join(f'import MaxCaterpillar.Frontier.StarCertificate.StarModelChecks.Chunk{k:02d}\n' for k in range(4))
 s+='''set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
'''
 for name,weights in [('starVCoefficient','1 else 0'),('starVPrimeCoefficient','0 else 1')]:
  s+=f'''theorem {name}_coupling (p : Fin 120) (r i : Fin 4) :
    {name} p r i = (maskedChain 15 p r).form subsetForms i *
      (if i ∈ maskSet (centerBeforeMask p) then {weights}) := by
  fin_cases p
'''
  for p in range(120):s+=f'  · exact {name}_coupling_{p} r i\n'
 s+='end MaxCaterpillar.Frontier.StarCertificate\n';write(BASE/'StarModelProofs.lean',s)
if __name__=='__main__':main()
