"""只读核验正式源码/保护文件/日志；写入本阶段验收，不改历史。"""
from pathlib import Path
import json,hashlib,re,datetime,subprocess
root=Path(__file__).resolve().parents[2]
out=root/'logs/v1.0.1'
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
base=json.loads(next(out.glob('baseline_*.json')).read_text())
old=json.loads((root/'logs/v0.5.3/overall_acceptance.json').read_text())
files=sorted(root.glob('LeanPML/**/*.lean'))+[root/'LeanPML.lean',root/'Audit.lean']
hashes={str(f.relative_to(root)):sha(f) for f in files}
protected={f:{'before':h,'after':sha(root/f),'unchanged':h==sha(root/f)} for f,h in base['protected'].items()}
oldproof={f:h==hashes.get(f) for f,h in base['formal_sources'].items() if f not in ['LeanPML.lean','Audit.lean']}
legacy_logs=[{'path':c['output'],'hash_matches':sha(root/c['output'])==c['output_sha256']} for c in old['commands']]
commands=[]
for kind in ['lake_build','axioms_audit','declaration_types','api_probe','mathlib_sobolev_types','lean_version']:
 p=sorted(out.glob('*_'+kind+'.json'))[-1];j=json.loads(p.read_text());log=out/j['output_file']
 commands.append({'kind':kind,'metadata':str(p.relative_to(root)),'output':str(log.relative_to(root)),
                  'output_sha256':sha(log),'exit_code':j['exit_code'],'command':j['command'],'cwd':j['cwd']})
audit=(root/next(c['output'] for c in commands if c['kind']=='axioms_audit')).read_text()
axiom_lists=re.findall(r'depends on axioms:\s*\[([^]]*)\]',audit,re.S)
axioms=sorted({x.strip() for xs in axiom_lists for x in xs.split(',') if x.strip()})
expected=json.loads((out/'audit_declarations.json').read_text())
new_audited={n:("'"+n+"'") in audit for n in expected}
# 只剥除 Lean 注释后检查占位 token；最终可信依据仍是实际公理审计。
def uncomment(text):
 result=[];i=0;depth=0
 while i<len(text):
  if text.startswith('/-',i): depth+=1;i+=2
  elif depth and text.startswith('-/',i):depth-=1;i+=2
  elif depth:i+=1
  elif text.startswith('--',i):
   e=text.find('\n',i);i=len(text) if e<0 else e
  else:result.append(text[i]);i+=1
 return ''.join(result)
placeholders={str(f.relative_to(root)):re.findall(r'\b(?:sorry|admit|axiom)\b',uncomment(f.read_text())) for f in files}
placeholders={f:x for f,x in placeholders.items() if x}
seen=set()
def visit(module):
 if module in seen:return
 p=root/(module.replace('.','/')+'.lean')
 if not p.exists():return
 seen.add(module)
 for child in re.findall(r'^import\s+(LeanPML(?:\.\w+)*)',p.read_text(),re.M):visit(child)
visit('LeanPML')
newmods=['LeanPML.Analysis.WeightedL2Operators','LeanPML.Rectangle.WeakSpaces','LeanPML.Examples.WeakSpaces']
checks={'all_commands_exit_zero':all(c['exit_code']==0 for c in commands),'all_new_audit_queries_present':all(new_audited.values()),
 'standard_axioms_only':set(axioms)<={'propext','Classical.choice','Quot.sound'},'no_sorryAx':'sorryAx' not in audit,
 'no_formal_placeholder_tokens':not placeholders,'previous_proof_files_unchanged':all(oldproof.values()),
 'protected_files_unchanged':all(x['unchanged'] for x in protected.values()),'historical_build_audit_logs_intact':all(x['hash_matches'] for x in legacy_logs),
 'all_new_modules_reachable':all(m in seen for m in newmods),'git_diff_check':subprocess.run(['git','diff','--check'],cwd=root,capture_output=True).returncode==0,
 'smooth_report_unchanged':sha(root/'reports/smooth_theorem.md')==base['documents']['reports/smooth_theorem.md']}
assert all(checks.values()),checks
r={'stage':'v1.0.1','time':datetime.datetime.now().astimezone().isoformat(),
   'status':'partial','verified_construction_subtasks':'passed',
   'reason_not_whole_stage_complete':'一般旧光滑零迹函数进入新 H₀¹ 图范数闭包的逼近连接尚未完成；不声称完整弱 PDE 范围。',
   'completed':['fixed mathlib API/type/source audit','true weak partial/divergence test identities and uniqueness','closed complete H1/Hdiv graphs and graph norm equivalence','H01 closure construction and nonzero compact smooth member','smooth H1/Hdiv and restricted operator bridges','reuse of degenerate WeightedL2 embedding/completeness/zero-region/AE facts','exact physical image and bounded coefficient multiplication'],
   'not_implemented':['all smooth zero-trace fields into H01 closure','weak trace kernel identification','weak Green/Poincare','W1-infinity weak coefficient product/slice theory','weighted regularity propagation','lift gauge uniqueness','weak PDE main theorem'],
   'commands':commands,'checks':checks,'axioms':axioms,'axiom_output_count':len(axiom_lists),'new_and_reused_audit_queries':new_audited,
   'formal_sources':hashes,'formal_source_count':len(hashes),'previous_proof_files':oldproof,'protected':protected,'historical_logs':legacy_logs,
   'new_modules':newmods,'formal_placeholder_tokens':placeholders,
   'mathlib_commit':subprocess.check_output(['git','-C','.lake/packages/mathlib','rev-parse','HEAD'],cwd=root,text=True).strip(),
   'documents':{f:sha(root/f) for f in ['README.md','PROGRESS.md','docs/theorem_inventory.md','docs/claim_ledger.md','logs/v1.0.1/stage_record.md']},
   'type_review':{'TestFunction':'actual smooth field, compact support, support inside full rectangle only',
     'weak_graphs':'L2 coordinates constrained by all C_c-infinity test identities; no general Green/trace/energy assumptions',
     'zeroBoundaryGraph':'closure of span of actual compact smooth graphs; no claimed weak trace kernel theorem',
     'weightedMul':'measurability and uniform bound on multiplier m, not on energy weight w',
     'v05':'all prior proof bodies and strong regularity hypotheses unchanged'},
   'failure_logs':[str(p.relative_to(root)) for p in out.glob('*.json') if (lambda j: isinstance(j,dict) and j.get('command') and j.get('exit_code') not in [None,0])(json.loads(p.read_text()))]}
(out/'acceptance.json').write_text(json.dumps(r,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':r['status'],'verified_construction_subtasks':r['verified_construction_subtasks'],'checks':checks,'formal_sources':len(hashes),'audit_output_count':len(axiom_lists),'axioms':axioms,'failure_log_count':len(r['failure_logs'])},ensure_ascii=False,indent=2))
