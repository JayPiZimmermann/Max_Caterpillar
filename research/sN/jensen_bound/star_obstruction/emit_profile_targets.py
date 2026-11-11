"""Produce shared masked-sign profiles and bounded actual-C match modules."""
from pathlib import Path
import argparse,json
from certificate_arithmetic import tensor,vec,psi_coefficients
ROOT=Path(__file__).resolve().parents[4];D=Path(__file__).parent;BASE=ROOT/'MaxCaterpillar/Frontier/StarCertificate'
def sign_vec(p):return vec([{ -1:'.neg',0:'.zero',1:'.pos'}[s] for s in p])
def lookup(values,key,start=0,depth=1):
 pad='  '*depth
 if len(values)==1:return pad+values[0]
 n=len(values)//2
 return pad+f'if {key} < {start+n} then (\n'+lookup(values[:n],key,start,depth+1)+'\n'+pad+') else (\n'+lookup(values[n:],key,start+n,depth+1)+'\n'+pad+')'
def write(p,s):
 p.parent.mkdir(parents=True,exist_ok=True)
 if p.exists() and p.read_text()==s:return
 q=p.with_suffix('.lean.tmp');q.write_text(s);q.replace(p)
def records():
 d=json.load(open(D/'exact_tree_candidate.json'));profiles=[];indices={};mapping=[]
 for T in range(16):
  for leaf,l in enumerate(d['leaves']):
   p=tuple(s if (m&T)==m else 0 for m,s in enumerate(l['pattern'],1));key=(T,p)
   if key not in indices:indices[key]=len(profiles);profiles.append({'T':T,'pattern':p,'leaf':leaf})
 for r in profiles:
  opposite=tuple(-x for x in r['pattern'])
  r['canonical']=indices[(r['T'],opposite)] if opposite<r['pattern'] else indices[(r['T'],r['pattern'])]
  r['opposite']=opposite<r['pattern']
 for l in d['leaves']:
  mapping.append([indices[(T,tuple(s if (m&T)==m else 0 for m,s in enumerate(l['pattern'],1)))] for T in range(16)])
 return d,profiles,mapping

def emit_profile(j,r,c):
 T=r['T'];p=r['pattern'];psi=psi_coefficients(p,c,only_T=T)[T]
 if not any(p):
  s=f'''import MaxCaterpillar.Frontier.StarCertificate.XiZeroPattern
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile{j:04d}
def pattern : Fin 15 → Sign := {sign_vec(p)}
def psi : Fin 16 → IntegerForm 4 := fun _ => 0
theorem pattern_zero : pattern = zeroResonancePattern := by decide
theorem actual_profile (P : Fin 16) (i : Fin 4) :
    maskedPsiIntegerCoefficients {T} P pattern i = psi P i := by
  rw [pattern_zero]
  exact maskedPsiIntegerCoefficients_zeroPattern {T} P i
end MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile{j:04d}
'''
  write(BASE/'XiProfileChecks'/f'Profile{j:04d}.lean',s)
  return
 if r['opposite']:
  k=r['canonical'];ns=f'XiProfileChecks.Profile{k:04d}'
  s=f'''import MaxCaterpillar.Frontier.StarCertificate.XiProfiles
import MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile{k:04d}
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile{j:04d}
def pattern : Fin 15 → Sign := {sign_vec(p)}
def psi (P : Fin 16) (i : Fin 4) : ℤ := -{ns}.psi P i
theorem pattern_opposite : pattern = fun j => ({ns}.pattern j).opposite := by decide
theorem actual_profile (P : Fin 16) (i : Fin 4) :
    maskedPsiIntegerCoefficients {T} P pattern i = psi P i := by
  rw [pattern_opposite, maskedPsiIntegerCoefficients_opposite, {ns}.actual_profile]
  rfl
end MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile{j:04d}
'''
  write(BASE/'XiProfileChecks'/f'Profile{j:04d}.lean',s)
  return
 qvalues=['⟨'+','.join(map(str,row))+'⟩' for row in psi]
 s=f'''import MaxCaterpillar.Frontier.StarCertificate.XiCompiledEval
import MaxCaterpillar.Frontier.StarCertificate.XiKernelCheck
/-! Generated exact masked-Psi profile {j}, mask {T}. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile{j:04d}
open BigOperators

def pattern : Fin 15 → Sign := {sign_vec(p)}
def psiQuad (P : Fin 16) : IntegerQuad :=
{lookup(qvalues,'P.val')}
def psi (P : Fin 16) : IntegerForm 4 := (psiQuad P).toForm

theorem fast_check : integerQuadTableCheck
    (fun P => compiledMaskedPsiQuad {T} P pattern) psiQuad = true := by
  kernel_bool_check

theorem actual_profile (P : Fin 16) (i : Fin 4) :
    maskedPsiIntegerCoefficients {T} P pattern i = psi P i := by
  rw [← compiledMaskedPsiQuad_toForm]
  exact congrArg (fun q : IntegerQuad => q.toForm i)
    (integerQuadTableCheck_sound _ _ fast_check P)

end MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile{j:04d}
'''
 write(BASE/'XiProfileChecks'/f'Profile{j:04d}.lean',s)

def emit_leaf(j,d,profiles,mapping):
 l=d['leaves'][j];ids=mapping[j]
 catalogue=json.load(open(D/'checker_leaf_catalogue.json'))
 entry=catalogue['entries'][str(j)];geo=entry['pattern'].rsplit('.',1)[0]
 root_import='import '+entry['module']+'\n'
 pattern_value=entry['pattern'];coefficient_value=entry['coefficients']
 opposite=tuple(-s for s in l['pattern'])
 if opposite<tuple(l['pattern']):
  k=next(k for k,r in enumerate(d['leaves']) if tuple(r['pattern'])==opposite)
  ns=f'XiTargetChecks.Leaf{k:04d}'
  for row,canonical in zip(l['identities'],d['leaves'][k]['identities']):assert row==[-x for x in canonical]
  text=f'''import MaxCaterpillar.Frontier.StarCertificate.XiTargetChecks.Leaf{k:04d}
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate.XiTargetChecks.Leaf{j:04d}
def pattern : Fin 15 → Sign := {sign_vec(l['pattern'])}
def coefficients (t : Fin 80) : IntegerForm 4 :=
{lookup([tensor(row) for row in l['identities']],'t.val')}
theorem pattern_opposite : pattern = fun j => ({ns}.pattern j).opposite := by decide
theorem coefficient_check : integerTable2Check
    (fun t i => -{ns}.coefficients t i) coefficients = true := by
  kernel_bool_check
theorem actual_match : starAnovaIntegerCoefficients pattern = coefficients := by
  funext t i
  rw [pattern_opposite]
  change componentIntegerCoefficients (maskSet (pairS t)) (maskSet (pairA t))
    (fun j => ({ns}.pattern j).opposite) i = coefficients t i
  rw [componentIntegerCoefficients_opposite]
  change -(starAnovaIntegerCoefficients {ns}.pattern t i) = coefficients t i
  rw [congrFun (congrFun {ns}.actual_match t) i]
  exact integerTable2Check_sound _ _ coefficient_check t i
end MaxCaterpillar.Frontier.StarCertificate.XiTargetChecks.Leaf{j:04d}
'''
  write(BASE/'XiTargetChecks'/f'Leaf{j:04d}.lean',text)
  return
 if not any(l['pattern']):
  text=root_import+f'''import MaxCaterpillar.Frontier.StarCertificate.XiZeroPattern
import MaxCaterpillar.Frontier.StarCertificate.XiRepresentativeSound
namespace MaxCaterpillar.Frontier.StarCertificate.XiTargetChecks.Leaf{j:04d}
def pattern : Fin 15 → Sign := {pattern_value}
def coefficients : Fin 80 → IntegerForm 4 := {coefficient_value}
theorem pattern_zero : pattern = zeroResonancePattern := by decide
theorem coefficients_zero : coefficients = 0 := rfl
theorem actual_match : starAnovaIntegerCoefficients pattern = coefficients := by
  rw [pattern_zero,starAnovaIntegerCoefficients_zeroPattern]
  exact coefficients_zero.symm
theorem stratum_sound (z : Fin 4 → ℝ) (hz : actualSigns subsetForms z = pattern) : AllStarAnovaZero z :=
  starAnova_stratum_sound pattern coefficients {geo}.den{j} {geo}.lambda{j}
    {geo}.solvedNumeric{j}.2 actual_match z hz
end MaxCaterpillar.Frontier.StarCertificate.XiTargetChecks.Leaf{j:04d}
'''
  write(BASE/'XiTargetChecks'/f'Leaf{j:04d}.lean',text)
  return
 imports=root_import+'import MaxCaterpillar.Frontier.StarCertificate.XiProfiles\nimport MaxCaterpillar.Frontier.StarCertificate.XiSparseCollect\nimport MaxCaterpillar.Frontier.StarCertificate.XiRepresentativeSound\n'+''.join(f'import MaxCaterpillar.Frontier.StarCertificate.XiProfileChecks.Profile{k:04d}\n' for k in sorted(set(ids)))
 ns=lambda k:f'XiProfileChecks.Profile{k:04d}'
 text=imports+f'''
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate.XiTargetChecks.Leaf{j:04d}
open BigOperators

def pattern : Fin 15 → Sign := {pattern_value}
def psi (T : Fin 16) : Fin 16 → IntegerForm 4 :=
{lookup([ns(k)+'.psi' for k in ids],'T.val')}
def coefficients : Fin 80 → IntegerForm 4 := {coefficient_value}

'''
 for T,k in enumerate(ids):
  text+=f'theorem restriction_{T} : restrictPattern {T} pattern = {ns(k)}.pattern := by decide\n'
 text+='''
theorem psi_check (T P : Fin 16) (i : Fin 4) :
    maskedPsiIntegerCoefficients T P pattern i = psi T P i := by
  fin_cases T
'''
 for T,k in enumerate(ids):
  text+=f'''  · change maskedPsiIntegerCoefficients {T} P pattern i = {ns(k)}.psi P i
    rw [← congrFun (maskedPsiIntegerCoefficients_restrict {T} P pattern) i, restriction_{T}]
    exact {ns(k)}.actual_profile P i
'''
 text+='''
theorem collect_fast_check : integerTable2Check (sparseCollect psi) coefficients = true := by
  kernel_bool_check

theorem actual_match : starAnovaIntegerCoefficients pattern = coefficients := by
  rw [starAnovaIntegerCoefficients_of_sparse_table pattern psi psi_check]
  funext t i
  exact integerTable2Check_sound _ _ collect_fast_check t i

'''+f'''theorem stratum_sound (z : Fin 4 → ℝ) (hz : actualSigns subsetForms z = pattern) : AllStarAnovaZero z :=
  starAnova_stratum_sound pattern coefficients {geo}.den{j} {geo}.lambda{j}
    {geo}.solvedNumeric{j}.2 actual_match z hz

'''+f'end MaxCaterpillar.Frontier.StarCertificate.XiTargetChecks.Leaf{j:04d}\n'
 write(BASE/'XiTargetChecks'/f'Leaf{j:04d}.lean',text)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--profile',type=int);ap.add_argument('--leaf',type=int);ap.add_argument('--representatives',action='store_true');ap.add_argument('--all-profiles',action='store_true');ap.add_argument('--all-leaves',action='store_true');ap.add_argument('--probe-leaf',type=int,default=1);ap.add_argument('--probe-mask',type=int,default=15);a=ap.parse_args()
 if a.all_leaves:a.all_profiles=True
 d,p,m=records();c=json.load(open(D/'certificate_small_candidate.json'))
 (D/'profile_manifest.json').write_text(json.dumps({'profiles':p,'leaf_profiles':m},separators=(',',':'))+'\n')
 if a.representatives:
  reps=json.load(open(D/'orbit_manifest.json'))['representatives']
  wanted={k for j in reps if any(d['leaves'][j]['pattern']) for k in m[j]}
  wanted.update(p[j]['canonical'] for j in list(wanted))
  for j in sorted(wanted):emit_profile(j,p[j],c)
  for j in reps:emit_leaf(j,d,p,m)
  (D/'representative_profile_jobs.json').write_text(json.dumps({'profiles':sorted(wanted),'representatives':reps},indent=2)+'\n')
  print('representatives',len(reps),'profilemodules',len(wanted),'numericprofiles',sum(not p[j]['opposite'] and any(p[j]['pattern']) for j in wanted),flush=True)
 elif a.all_profiles:
  for j,r in enumerate(p):emit_profile(j,r,c)
 elif a.leaf is not None:
  wanted=set(m[a.leaf]);wanted.update(p[j]['canonical'] for j in list(wanted))
  for j in sorted(wanted):emit_profile(j,p[j],c)
 else:
  j=a.profile if a.profile is not None else m[a.probe_leaf][a.probe_mask]
  if p[j]['opposite']:emit_profile(p[j]['canonical'],p[p[j]['canonical']],c)
  emit_profile(j,p[j],c)
  print('probe',j,'mask',p[j]['T'],flush=True)
 if a.all_leaves:
  for j in range(len(d['leaves'])):emit_leaf(j,d,p,m)
 elif a.leaf is not None:emit_leaf(a.leaf,d,p,m)
 print('profiles',len(p),'numeric',sum(not r['opposite'] for r in p),flush=True)
if __name__=='__main__':main()
