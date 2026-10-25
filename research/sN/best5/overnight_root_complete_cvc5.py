#!/usr/bin/env python3
"""Bounded second-solver replay of the complete-comparison K3 formula.

SAT still needs the independent whole-network verifier. UNSAT is retained
with its proof/core for subsequent independent certificate work; a solver
verdict alone is not promoted to a new lower bound.
"""
from pathlib import Path
import hashlib,json,re,resource,sys,time
sys.path.insert(0,'/tmp/overnight_fixed_cvc5')
import cvc5

def standardize(source):
    """Z3 emits unary sums; replace them by their sole operand exactly."""
    stack=[];output=[];removed=0
    for token in re.findall(r'\(|\)|[^\s()]+',re.sub(r';[^\n]*','',source)):
        if token=='(':
            stack.append([])
        elif token==')':
            row=stack.pop()
            if len(row)==2 and row[0] in ('+','*','and','or'):
                value=row[1];removed+=1
            else:value='('+' '.join(row)+')'
            (stack[-1] if stack else output).append(value)
        else:stack[-1].append(token)
    assert not stack
    return '\n'.join(output),removed

def main():
    start=time.monotonic();path=Path(sys.argv[1]).absolute()
    seconds=int(sys.argv[2]) if len(sys.argv)>2 else 300
    mode=sys.argv[3] if len(sys.argv)>3 else 'p2'
    resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3))
    solver=cvc5.Solver();solver.setLogic('QF_LRA')
    for key,value in [('produce-models','true'),('produce-unsat-cores','true'),
                      ('produce-proofs','true'),('check-proofs','true'),
                      ('tlimit-per',str(1000*seconds))]:
        solver.setOption(key,value)
    source,removed=standardize(path.read_text())
    parser=cvc5.InputParser(solver);parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6,source,str(path))
    sm=parser.getSymbolManager();commands=0
    while True:
        cmd=parser.nextCommand()
        if cmd.isNull():break
        if str(cmd).startswith('(check-sat'):continue
        cmd.invoke(solver,sm);commands+=1
    print('PARSED',commands,'ASSERTIONS',len(solver.getAssertions()),'BUDGET',seconds,flush=True)
    result=solver.checkSat();print('RESULT',result,'SECONDS',time.monotonic()-start,flush=True)
    version=solver.getVersion()
    if isinstance(version,bytes):version=version.decode()
    out=dict(status=str(result),solver_version=version,budget_seconds=seconds,
        commands=commands,assertions=len(solver.getAssertions()),unary_operations_removed=removed,
        source_smt=str(path),source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        scope='Independent solver diagnostic of the complete pair-cone formulation. No new construction or lower bound without the separate exact certificate gate.')
    prefix=Path(__file__).parent/('overnight_root_complete_cvc5_'+mode)
    if result.isSat():
        out['model']={str(t):str(solver.getValue(t)) for t in sm.getDeclaredTerms()}
    elif result.isUnsat():
        core=solver.getUnsatCore()
        out['core_size']=len(core)
        prefix.with_suffix('.core.txt').write_text('\n'.join(map(str,core))+'\n')
        proof=solver.getProof()
        out['proof_roots']=len(proof)
        # Preserve the API proof tree in its native textual form if exposed.
        try:
            parts=[solver.proofToString(p) for p in proof]
            rendered='\n'.join(p.decode() if isinstance(p,bytes) else p for p in parts)
            prefix.with_suffix('.proof.txt').write_text(rendered+'\n')
            out['proof_bytes']=len(rendered.encode())
        except (AttributeError,TypeError,RuntimeError) as error:
            out['proof_export_error']=str(error)
    else:
        out['unknown_explanation']=str(result.getUnknownExplanation())
    out['seconds']=time.monotonic()-start
    prefix.with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='model'},sort_keys=True),flush=True)

if __name__=='__main__':main()
