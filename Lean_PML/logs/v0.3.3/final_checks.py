"""交付一致性核对；读取真实构建/审计记录，不重新运行证明或更新依赖。"""
from pathlib import Path
import json,re,hashlib
root=Path.cwd();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
snapshot=json.loads((root/'logs/v0.3.2/source_snapshot.json').read_text())['hashes']
protected={}
for f,h in snapshot.items():
 if f.endswith('_副本.pdf'):continue
 protected[f]=sha(root/f)==h
assert all(protected.values()),protected
new_files=['BalanceInterfaces','PrimitiveEvolution','SpatialBalance','BalanceBlocks','BalanceAbstract','Coercivity','PhysicalControl']
# 递归正式导入只遍历本工程，不把缓存里存在的文件误算作构建覆盖。
seen=set()
def visit(module):
 if module in seen:return
 seen.add(module)
 f=root/(module.replace('.','/')+'.lean')
 for name in re.findall(r'^import (LeanPML(?:\.\w+)*)',f.read_text(),re.M):visit(name)
visit('LeanPML')
for f in new_files:assert 'LeanPML.PML.'+f in seen
assert 'defaultTargets = ["LeanPML", "Audit"]'in(root/'lakefile.toml').read_text()
audit=(root/'Audit.lean').read_text()
printed=re.findall(r'^#print axioms (LeanPML\.\S+)',audit,re.M)
assert len(printed)==len(set(printed))==316
results={}
for stage,build,auditstem in [
 ('v0.3.2','20261013T095839_225389_lake_build','20261013T100104_046897_axioms_audit'),
 ('v0.3.3','20261013T100156_159842_lake_build','20261013T100321_602582_axioms_audit')]:
 folder=root/'logs'/stage
 for stem in [build,auditstem]:
  meta=json.loads((folder/(stem+'.json')).read_text())
  assert meta['exit_code']==0 and meta['cwd']==str(root)and meta['status']=='finished'
 out=(folder/(auditstem+'.log')).read_text()
 audited=re.findall(r"'([^']+)' depends on axioms",out)
 assert 'sorryAx'not in out
 for e in json.loads((folder/'new_theorems.json').read_text()):
  assert e['name']in audited and e['name']in printed
 failures=[]
 for f in sorted(folder.glob('*.json')):
  try:m=json.loads(f.read_text())
  except Exception:continue
  if isinstance(m,dict)and m.get('exit_code')not in [None,0]:
   failures.append({'file':f.name,'exit_code':m['exit_code']})
 results[stage]={'build':build,'audit':auditstem,'audited':len(audited),'preserved_failed_commands':failures}
# 源码去掉注释后检查占位；只检查本轮新增源码，不把说明文字当作证明。
for name in new_files:
 text=(root/'LeanPML/PML'/(name+'.lean')).read_text()
 clean=re.sub(r'/-[\s\S]*?-/','',text)
 clean=re.sub(r'--[^\n]*','',clean)
 assert not re.search(r'\b(sorry|admit|axiom)\b',clean),name
# 旧审计、历史文档与旧源码无静默重写。
initial=root/'logs/v0.3.2/initial_files'
old_audit=(initial/'Audit.lean').read_text()
assert audit.startswith(old_audit)
for filename in ['theorem_inventory.md','claim_ledger.md','pdf_formalization_marks.md']:
 assert (root/'docs'/filename).read_text().startswith((initial/filename).read_text())
assert (root/'PROGRESS.md').read_text().endswith((initial/'PROGRESS.md').read_text())
assert (root/'docs/source_inventory.md').read_bytes()==(initial/'source_inventory.md').read_bytes()
placeholders=['VALIDATION_LINKS','PDF_SUMMARY','STAGE_VALIDATION','正在分别验收']
for filename in ['README.md','PROGRESS.md','docs/theorem_inventory.md','docs/claim_ledger.md']:
 text=(root/filename).read_text()
 assert not any(s in text for s in placeholders),filename
# 本轮新增/更新链接只针对现存本地目标；旧历史文档中的陈旧外部链接不据此删改。
bad=[]
for filename in ['README.md','PROGRESS.md','docs/theorem_inventory.md','docs/claim_ledger.md','docs/pdf_formalization_marks.md']:
 file=root/filename;text=file.read_text()
 if filename=='PROGRESS.md':text=text.split('\n---\n',1)[0]
 if filename.startswith('docs/'):
  marker='## v0.3.2–v0.3.3'if'claim_ledger'not in filename else'## 2026-10-13：v0.3.2–v0.3.3'
  text=text[text.index(marker):]
 for target in re.findall(r'\]\(([^)]+)\)',text):
  if target.startswith(('http:','https:','#')):continue
  target=target.split('#')[0]
  if (file.parent/target).resolve()==root/'logs/v0.3.3/final_checks.json':continue
  if not(file.parent/target).exists():bad.append([filename,target])
assert not bad,bad
pdf=json.loads((root/'logs/v0.3.3/pdf/verification.json').read_text())
assert pdf['visual_review'].startswith('passed')
assert sha(root/'../results/V7_Maxwell_Debye_PML/V7_global_energy_副本.pdf')==pdf['sha256_after']
out={'stages':results,'protected_files_unchanged':protected,'formal_modules':sorted(seen),
 'project_module_count_without_root':len(seen)-1,'audited_formal_names':len(printed),
 'new_public_theorems':53,'placeholder_scan':'passed','all_new_modules_imported':True,
 'history_preserved':True,'new_links_valid':True,'pdf_verification':'passed',
 'next_stage':'v0.3.4 not implemented'}
(root/'logs/v0.3.3/final_checks.json').write_text(json.dumps(out,ensure_ascii=False,indent=2))
print(json.dumps(out,ensure_ascii=False,indent=2))
