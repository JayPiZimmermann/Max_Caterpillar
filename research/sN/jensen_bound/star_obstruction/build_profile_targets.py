"""Build bounded, task-owned profile/representative modules in the shared pool."""
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,time
from emit_profile_targets import records
ROOT=Path(__file__).resolve().parents[4];D=Path(__file__).parent
BASE=ROOT/'MaxCaterpillar/Frontier/StarCertificate';ART=ROOT/'.lake/build/lib/MaxCaterpillar/Frontier/StarCertificate'

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--smoke',type=int);ap.add_argument('--timeout',type=int,default=60);a=ap.parse_args()
 d,p,m=records()
 if a.smoke is not None:
  leaves=[a.smoke];wanted=set(m[a.smoke]);wanted.update(p[j]['canonical'] for j in list(wanted));tag=f'smoke{a.smoke:04d}'
 else:
  jobs=json.load(open(D/'representative_profile_jobs.json'));leaves=jobs['representatives'];wanted=set(jobs['profiles']);tag='representatives'
 status_path=D/f'profile_targets_{tag}_status.json';logdir=D/'profile_target_logs';logdir.mkdir(exist_ok=True)
 status={'input_sha256':hashlib.sha256((D/'exact_tree_candidate.json').read_bytes()).hexdigest(),'status':'running','records':[],'mode':tag}
 old={}
 for previous_path in sorted(D.glob('profile_targets_*_status.json')):
  previous=json.loads(previous_path.read_text());old.update({r['module']:r for r in previous.get('records',[]) if r['exit']==0})
 def save():
  q=status_path.with_suffix('.json.tmp');q.write_text(json.dumps(status,indent=2)+'\n');q.replace(status_path)
 def build(kind,j):
  stem=(f'Profile{j:04d}' if kind=='XiProfileChecks' else f'Leaf{j:04d}');module=f'MaxCaterpillar.Frontier.StarCertificate.{kind}.{stem}'
  source=BASE/kind/(stem+'.lean');target=ART/kind/(stem+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
  sha=hashlib.sha256(source.read_bytes()).hexdigest()
  if module in old and old[module].get('source_sha256')==sha and target.exists():
   artifact_sha=hashlib.sha256(target.read_bytes()).hexdigest()
   if old[module].get('artifact_sha256',artifact_sha)==artifact_sha:
    r=dict(old[module]);r['reused']=True;r['artifact_sha256']=artifact_sha;return r
  log=logdir/(stem+'.log');timing=logdir/(stem+'.time');before=time.monotonic()
  command=['/usr/bin/time','-f','wall=%e user=%U maxrss_kib=%M','-o',str(timing),'timeout',str(a.timeout)+'s','lake','env','lean','-j1','-o',str(target),'-i',str(target.with_suffix('.ilean')),str(source)]
  pool=[sys.executable,str(ROOT/'research/sN/zulip_three/lean_small_pool.py'),'bash','-c','ulimit -s unlimited\nexec "$@"','bash']
  with log.open('w') as f:result=subprocess.run(pool+command,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
  r={'module':module,'exit':result.returncode,'elapsed_including_pool_seconds':round(time.monotonic()-before,3),'source_sha256':sha,'log':str(log.relative_to(ROOT)),'timing':timing.read_text() if timing.exists() else None}
  if result.returncode==0:r['artifact_sha256']=hashlib.sha256(target.read_bytes()).hexdigest()
  (logdir/(stem+'.exit')).write_text(str(result.returncode)+'\n');return r
 def phase(items):
  with ThreadPoolExecutor(max_workers=2) as pool:
   futures=[pool.submit(build,kind,j) for kind,j in items]
   for f in as_completed(futures):
    r=f.result();status['records'].append(r);save();print(r['module'],r['exit'],r['elapsed_including_pool_seconds'],flush=True)
    if r['exit']:
     status['status']='failed';save()
     for pending in futures:pending.cancel()
     raise SystemExit(r['exit'])
 phase([('XiProfileChecks',j) for j in sorted(wanted) if not p[j]['opposite']])
 phase([('XiProfileChecks',j) for j in sorted(wanted) if p[j]['opposite']])
 phase([('XiTargetChecks',j) for j in leaves])
 status['status']='complete';save();print('COMPLETE',len(status['records']),flush=True)
if __name__=='__main__':main()
