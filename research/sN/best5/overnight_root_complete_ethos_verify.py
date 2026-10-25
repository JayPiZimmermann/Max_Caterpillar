#!/usr/bin/env python3
"""Replay the fixed-negative-shape proof with the independent Ethos checker.

Only the standard library is needed. Pinned external checker/signature files
are cached outside the repository and verified by SHA256 before use.
"""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,tempfile,urllib.request,zipfile

HERE=Path(__file__).parent;ROOT=HERE.parents[2]

def digest(data):return hashlib.sha256(data).hexdigest()

def read_checked(path,sha):
    data=path.read_bytes();assert digest(data)==sha,str(path);return data

def fetch(path,url,sha):
    if not path.exists():
        path.parent.mkdir(parents=True,exist_ok=True)
        data=urllib.request.urlopen(url,timeout=30).read()
        assert digest(data)==sha,url
        path.write_bytes(data)
    return read_checked(path,sha)

def neutral_unary_normalization(source):
    frames=[];commands=[];count=0
    for token in re.findall(r'\(|\)|[^\s()]+',re.sub(r';[^\n]*','',source)):
        if token=='(':
            frames.append([])
        elif token==')':
            row=frames.pop()
            if len(row)==2 and row[0] in ('+','*','and','or'):
                out=row[1];count+=1
            else:out='('+' '.join(row)+')'
            (frames[-1] if frames else commands).append(out)
        else:
            assert frames
            frames[-1].append(token)
    assert not frames
    return '\n'.join(commands),count

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--cache',type=Path,default=Path(tempfile.gettempdir())/'max_caterpillar_ethos_025')
    args=parser.parse_args();cache=args.cache;cache.mkdir(parents=True,exist_ok=True)
    manifest=json.loads((HERE/'overnight_root_complete_ethos_manifest.json').read_text())
    source=read_checked(ROOT/manifest['source'],manifest['source_sha256']).decode()
    proof=read_checked(ROOT/manifest['proof'],manifest['proof_sha256']).decode().strip()
    archive=cache/'ethos.zip'
    fetch(archive,manifest['checker_url'],manifest['checker_archive_sha256'])
    checker=cache/'ethos'
    if not checker.exists():
        with zipfile.ZipFile(archive) as z:
            names=[s for s in z.namelist() if Path(s).name=='ethos']
            assert len(names)==1
            data=z.read(names[0]);assert digest(data)==manifest['checker_binary_sha256']
            checker.write_bytes(data);checker.chmod(0o755)
    read_checked(checker,manifest['checker_binary_sha256'])
    for row in manifest['signatures']:
        fetch(cache/'cpc'/row['path'],row['url'],row['sha256'])
    normalized,count=neutral_unary_normalization(source)
    assert count==111
    assert proof.startswith('(\n(declare-const') and proof.endswith(')')
    assert ':rule trust' not in proof
    # proofToString wraps its command sequence in one API list. Ethos
    # accepts that same sequence without the list's outer delimiters.
    with tempfile.TemporaryDirectory(prefix='max_ethos_replay_') as name:
        work=Path(name);ref=work/'problem.smt2';cpc=work/'proof.cpc'
        ref.write_text('(set-logic QF_LRA)\n'+normalized+'\n')
        cpc.write_text(proof[1:-1]+'\n')
        command=[str(checker),'--include='+str(cache/'cpc/Cpc.eo'),
                 '--reference='+str(ref),'--require-proof-of-false',str(cpc)]
        run=subprocess.run(command,text=True,capture_output=True,timeout=60)
        assert run.returncode==0,(run.returncode,run.stdout,run.stderr)
        assert run.stdout.strip()=='correct',(run.stdout,run.stderr)
    print('INDEPENDENT_ETHOS_FIXED_NEGATIVE_SHAPE_PROOF_PASS')

if __name__=='__main__':main()
