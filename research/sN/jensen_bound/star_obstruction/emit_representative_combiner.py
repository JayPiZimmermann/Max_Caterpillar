"""Combine the 67 closed real-stratum certificates, in the checked orbit order."""
from pathlib import Path
import json,hashlib
ROOT=Path(__file__).resolve().parents[4];D=Path(__file__).parent
manifest=json.load(open(D/'orbit_manifest.json'));reps=manifest['representatives'];assert len(reps)==67
s='import MaxCaterpillar.Frontier.StarCertificate.XiOrbitData\n'+''.join(f'import MaxCaterpillar.Frontier.StarCertificate.XiTargetChecks.Leaf{j:04d}\n' for j in reps)
s+='''
/-! Generated from orbit_manifest.json. Every imported stratum solver has a
closed kernel-checked coefficient computation and zero-span certificate. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate.XiRepresentativeCertificates

theorem sound (r : Fin 67) (z : Fin 4 → ℝ)
    (hz : actualSigns subsetForms z = orbitRepresentativePattern r) : AllStarAnovaZero z := by
  fin_cases r
'''
for j in reps:s+=f'  · exact XiTargetChecks.Leaf{j:04d}.stratum_sound z hz\n'
s+='''
#print axioms sound
end MaxCaterpillar.Frontier.StarCertificate.XiRepresentativeCertificates
'''
p=ROOT/'MaxCaterpillar/Frontier/StarCertificate/XiRepresentativeCertificates.lean'
if not p.exists() or p.read_text()!=s:
 q=p.with_suffix('.lean.tmp');q.write_text(s);q.replace(p)
print(p)
