"""Bounded full N9 orbit/DAG inventory for the sparse signed-root score.

Separate prefix and cache; never writes the exact deficient-tree campaign.
One core, <=120s for this phase, with a durable inventory before compilation.
"""
from pathlib import Path
import json,resource,time
from dfs_review_fourier import family
from overnight_uniform_pruning_candidate_target import score
from overnight_lower_dp import Compiler
BASE=Path(__file__).with_suffix('')

def main():
    start=time.monotonic();units=family(9,'all');print('orbits',len(units),'seconds',time.monotonic()-start,flush=True);scores=[score(u)for u in units];inventory={'status':'FULL_N9_ORBIT_AND_SCORE_INVENTORY','units':units,'scores':list(map(str,scores)),'nonzero_score_columns':sum(bool(x)for x in scores),'enumeration_seconds':time.monotonic()-start};BASE.with_suffix('.json').write_text(json.dumps(inventory,indent=2)+'\n');print('score inventory saved',inventory['nonzero_score_columns'],'seconds',time.monotonic()-start,flush=True)
    dag=Compiler(9).compile(units);cache=BASE.with_suffix('.bin');dag.save(cache);inventory.update(dag_states=len(dag.starts)-1,dag_terms=len(dag.left),dag_diagnostics=dag.diagnostics,dag_bytes=cache.stat().st_size,total_seconds=time.monotonic()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss);BASE.with_suffix('.json').write_text(json.dumps(inventory,indent=2)+'\n');print({k:v for k,v in inventory.items()if k not in ('units','scores')},flush=True)
if __name__=='__main__':main()
