"""Emit the integral arithmetic representation and its exact rational bridge."""
from pathlib import Path
from fractions import Fraction
import json
ROOT=Path(__file__).resolve().parents[4]
D=Path(__file__).parent
OUT=ROOT/'MaxCaterpillar/Frontier/StarCertificate/XiIntegerData.lean'
def vec(xs):return '!['+', '.join(xs)+']'
def lookup(es,depth=1):
 pad='  '*depth
 if not es:return pad+'0'
 if len(es)==1:
  code,v=es[0];return pad+f'if code = {code} then {v} else 0'
 mid=len(es)//2;return pad+f'if code < {es[mid][0]} then (\n'+lookup(es[:mid],depth+1)+'\n'+pad+') else (\n'+lookup(es[mid:],depth+1)+'\n'+pad+')'
def main():
 c=json.load(open(D/'certificate_small_candidate.json'))
 entries=[]
 for j,p in sorted(enumerate(c['patterns']),key=lambda ip:sum((x+1)*3**i for i,x in enumerate(ip[1]))):
  code=sum((x+1)*3**i for i,x in enumerate(p));coeff=[Fraction(x)*2 for x in c['coefficients'][4*j:4*j+4]];assert all(x.denominator==1 for x in coeff)
  entries.append((code,vec([f'({int(x)} : ℤ)' for x in coeff])))
 s='''import MaxCaterpillar.Frontier.StarCertificate.XiSelectors
/-! Generated integral coefficient data; equality with the rational dictionary
is proved below, so this is an arithmetic representation of the same Xi. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators
abbrev IntegerForm (n : ℕ) := Fin n → ℤ

def starIntegerKappa (p : Fin 10 → Sign) : IntegerForm 4 :=
  let code := coarsePatternCode p
'''+lookup(entries)+'''

theorem starIntegerKappa_cast (p : Fin 10 → Sign) :
    (fun j => (starIntegerKappa p j : ℚ)) = starKappa p := by
  funext j
  fin_cases j <;> norm_num [starIntegerKappa, starKappa, ite_apply, Int.cast_ite]

end MaxCaterpillar.Frontier.StarCertificate
'''
 temp=OUT.with_suffix('.lean.tmp');temp.write_text(s);temp.replace(OUT)
if __name__=='__main__':main()
