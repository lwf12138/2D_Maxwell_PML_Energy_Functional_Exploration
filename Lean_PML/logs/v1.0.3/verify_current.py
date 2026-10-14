"""核查本轮源码与实际命令；不覆盖任何 v1.0.1 历史验收。"""
from pathlib import Path
import json,hashlib,re,subprocess,datetime
root=Path.cwd();sha=lambda f:hashlib.sha256(Path(f).read_bytes()).hexdigest()
old=json.loads((root/'logs/v1.0.1/acceptance.json').read_text())
base=json.loads((root/'logs/v1.0.2/baseline_20261014T102331.json').read_text())
files=sorted(root.glob('LeanPML/**/*.lean'))+[root/'LeanPML.lean',root/'Audit.lean']
sources={str(f.relative_to(root)):sha(f) for f in files}
previous={f:sha(root/f)==h for f,h in old['formal_sources'].items() if f not in ['LeanPML.lean','Audit.lean']}
protected={f:sha(f)==h for f,h in base.items() if not f.endswith('.lean')}
# lakefile/config .lean is not used in this project; theorem files are checked above.
commands={}
for stage in ['v1.0.2','v1.0.3']:
 commands[stage]={}
 for label in ['lake_build','axioms_audit']:
  m=sorted((root/'logs'/stage).glob('*_'+label+'.json'))[-1];j=json.loads(m.read_text());assert j['exit_code']==0,j
  output=m.parent/j['output_file'];commands[stage][label]={'metadata':str(m.relative_to(root)),'log':str(output.relative_to(root)),'sha256':sha(output),'cwd':j['cwd'],'exit_code':j['exit_code']}
audit=(root/commands['v1.0.3']['axioms_audit']['log']).read_text()
lists=re.findall(r'depends on axioms:\s*\[([^]]*)\]',audit,re.S);axioms=sorted({a.strip() for s in lists for a in s.split(',') if a.strip()})
new=json.loads((root/'logs/v1.0.2/new_declarations.json').read_text());assert all("'"+n+"'" in audit for n in new)
def uncomment(text):
 out=[];i=0;d=0
 while i<len(text):
  if text.startswith('/-',i):d+=1;i+=2
  elif d and text.startswith('-/',i):d-=1;i+=2
  elif d:i+=1
  elif text.startswith('--',i):
   end=text.find('\n',i);i=len(text) if end<0 else end
  else:out.append(text[i]);i+=1
 return ''.join(out)
placeholders=[str(f) for f in files if re.search(r'\b(sorry|admit|axiom)\b',uncomment(f.read_text()))]
seen=set()
def visit(name):
 if name in seen:return
 f=root/(name.replace('.','/')+'.lean')
 if not f.exists():return
 seen.add(name)
 for c in re.findall(r'^import\s+(LeanPML(?:\.\w+)*)',f.read_text(),re.M):visit(c)
visit('LeanPML')
reachable=all(str(f.relative_to(root)).replace('/','.').removesuffix('.lean') in seen for f in files if f.name!='Audit.lean')
checks={'old_proof_files_unchanged':all(previous.values()),'protected_unchanged':all(protected.values()),'no_placeholder_tokens':not placeholders,'no_sorryAx':'sorryAx' not in audit,'standard_axioms_only':set(axioms)<={'propext','Classical.choice','Quot.sound'},'all_formal_imported':reachable,'diff_check':subprocess.run(['git','diff','--check'],capture_output=True).returncode==0}
assert all(checks.values()),checks
r={'created_at':datetime.datetime.now().isoformat(),'engineering_checks_passed':True,'mathematical_stage_status':{'v1.0.1':'partial','v1.0.2':'partial','v1.0.3':'not_complete'},'checks':checks,'sources':sources,'commands':commands,'audit_count':len(lists),'axioms':axioms,'new_audit_declarations':new,'old_sources_check':previous,'protected_check':protected,'semantic_review':'reports/weak_theorem.md; logs/v1.0.2/DeclarationTypes.lean: weak spaces contain test identities only; new Green/Poincare are proved fields; no new weak solution/main structure.'}
(root/'logs/v1.0.3/verification_before_pdf.json').write_text(json.dumps(r,ensure_ascii=False,indent=2))
print(json.dumps({k:v for k,v in r.items() if k in ['engineering_checks_passed','mathematical_stage_status','checks','audit_count','axioms']},ensure_ascii=False,indent=2))
