from pathlib import Path
import json,re
mp=Path('paper/lean-map.json');d=json.loads(mp.read_text());body=Path('paper/main.tex').read_text();decl={}
for p in list(Path('MaxCaterpillar').rglob('*.lean'))+list(Path('MaxNN').rglob('*.lean')):
 for m in re.finditer(r'^\s*(?:(?:noncomputable|private|protected)\s+)*(?:theorem|lemma|def|abbrev|structure)\s+([^\s({:\[]+)',p.read_text(),re.M):decl.setdefault(m[1],[]).append(str(p))
replacements={
'draft_countexp-admissible':('MaxCaterpillar/Count/PerUnit.lean','tie_eq_of_inter_block'),
'draft_countexp-transfer':('MaxCaterpillar/Count/PerUnit.lean','card_passes_le_cover'),
'draft_countexp-corollary':('MaxCaterpillar/Count/Main.lean','pow_le_of_choose_le'),
'forestCount':('MaxCaterpillar/Count/Main.lean','choose_le_of_unit_bound'),
'out-leaf-count':('MaxCaterpillar/Count/Main.lean','outLeaf_unified_exponential')}
for k,v in list(d.items()):
 if 'file' not in v:continue
 p=Path(v['file']);name=v['name']
 if p.exists() and re.search(r'\b(?:theorem|lemma|def|abbrev|structure)\s+'+re.escape(name)+r'(?=[\s({:\[])',p.read_text()):continue
 oldfile,oldname=v['file'],name
 if k in replacements:v['file'],v['name']=replacements[k]
 elif len(decl.get(name,[]))==1:v['file']=decl[name][0]
 else:
  assert not v.get('equations') and not v.get('steps'),(k,v)
  assert not re.search(r'\\leandecl\{'+re.escape(oldfile)+r'\}\{\d+\}\{'+re.escape(oldname)+r'\}',body),(k,v)
  del d[k];continue
 body=re.sub(r'(\\leandecl)\{'+re.escape(oldfile)+r'\}\{\d+\}\{'+re.escape(oldname)+r'\}',lambda m: '\\leandecl{'+v['file']+'}{1}{'+v['name']+'}',body)
body=body.replace('(1+3/(16(s+1)))^N','(1+1/(2s+4))^N').replace('Trees.rootedStar','BHRSY.rootedStar')
mp.write_text(json.dumps(d,indent=2)+'\n');Path('paper/main.tex').write_text(body)
