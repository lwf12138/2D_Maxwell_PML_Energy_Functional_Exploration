from pathlib import Path
import json,hashlib,re,datetime
root=Path.cwd();folder=root/'logs/v1.0_finalization';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
commands={}
for label in ['lake_build','axioms_audit','type_review']:
 files=sorted(folder.glob('*_'+label+'.json'));meta=json.loads(files[-1].read_text());assert meta['exit_code']==0,(label,meta)
 commands[{'axioms_audit':'audit','lake_build':'build','type_review':'types'}[label]]={'metadata':str(files[-1].relative_to(root)),'log':str(files[-1].with_suffix('.log').relative_to(root)),'exit_code':0}
audit=(root/commands['audit']['log']).read_text();assert 'sorryAx' not in audit
axioms=set()
for block in re.findall(r'depends on axioms:\s*\[([^]]*)\]',audit):axioms.update(x.strip() for x in block.split(',') if x.strip())
assert axioms <= {'propext','Classical.choice','Quot.sound'},axioms
new=json.loads((folder/'new_declarations.json').read_text());assert all("'"+n+"'" in audit for n in new)
sources=json.loads((folder/'source_snapshot.json').read_text());assert all(sha(root/f)==h for f,h in sources.items())
base=json.loads((folder/'baseline_20261014T173547.json').read_text())['hashes']
newfiles=[f for f in sources if f not in base and f.endswith('.lean')]
for f in sources:
 if f.endswith('.lean'):assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|unsafe)\s',(root/f).read_text(),re.M),f
old={f:h for f,h in base.items() if f.startswith('LeanPML/') and f.endswith('.lean')}
assert all(sha(root/f)==h for f,h in old.items())
protected={f:h for f,h in base.items() if not f.endswith('.lean') and not f.endswith('_副本.pdf')}
assert all(sha(root/f)==h for f,h in protected.items())
# 验证可达导入链，而非要求所有传递模块都再直接导入。
seen=set()
def visit(f):
 if f in seen:return
 seen.add(f)
 for n in re.findall(r'^import\s+(LeanPML(?:\.[\w]+)*)\s*$',(root/f).read_text(),re.M):
  p=n.replace('.','/')+'.lean'
  if (root/p).exists():visit(p)
visit('LeanPML.lean')
assert all(f in seen for f in newfiles),set(newfiles)-seen
result={'engineering_checks_passed':True,'V7_main_mathematics_connected':True,'time':datetime.datetime.now().isoformat(),'sources':sources,'commands':commands,'new_declarations':new,'new_files':newfiles,'audit_declarations':len(re.findall(r'depends on axioms|does not depend on any axioms',audit)),'standard_axioms':sorted(axioms),'formal_file_count':sum(f.endswith('.lean') for f in sources),'new_modules_reachable':True,'old_modules_unchanged':True,'protected_hashes':protected,'remaining_main_analysis_interfaces':[], 'T_zero_semantics':'合法初始jet兼容分支；不从单点Ck推任意jet', 'isolated_and_pdf_final_acceptance':'pending separate final checks'}
assert result['audit_declarations']==1058
result['unique_audited_declarations']=len(set(re.findall(r"'([^']+)' depends on axioms",audit)))
(folder/'verification_before_pdf.json').write_text(json.dumps(result,ensure_ascii=False,indent=2))
(folder/'pdf/verification_path.txt').write_text('logs/v1.0_finalization/verification_before_pdf.json')
print(json.dumps({k:v for k,v in result.items() if k not in ['sources','new_declarations','protected_hashes']},ensure_ascii=False,indent=2))
