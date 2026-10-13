from pathlib import Path
import re,json,hashlib
root=Path.cwd();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
accept=json.loads((root/'logs/v0.4.4/acceptance.json').read_text())
for name,digest in accept['sources'].items():assert sha(root/name)==digest,name
for stage in ['v0.4.1','v0.4.2','v0.4.3','v0.4.4']:
 a=json.loads((root/'logs'/stage/'acceptance.json').read_text());assert a['status']=='passed'
 for key in ['build','audit']:
  m=json.loads((root/a[key]).with_suffix('.json').read_text());assert m['exit_code']==0 and m['status']=='finished'
 for f,d in a['sources'].items():assert sha(root/f)==d,(stage,f)
audit=(root/'Audit.lean').read_text();auditnames=set(re.findall(r'^#print axioms (LeanPML\S+)' ,audit,re.M))
newfiles=[root/f for f in accept['source_scan_files']];missing=[];theorems=[]
for f in newfiles:
 for name in re.findall(r'^theorem (\S+)',f.read_text(),re.M):
  name=name.rstrip(':'); matches=[n for n in auditnames if n.endswith('.'+name)]
  if not matches:missing.append((str(f.relative_to(root)),name))
  theorems.append({'file':str(f.relative_to(root)),'name':name,'audit_matches':matches})
assert not missing,missing
# 所有正式证明文件都在默认入口的传递导入链。
reachable=set()
def visit(f):
 if f in reachable:return
 reachable.add(f)
 for name in re.findall(r'^import (LeanPML\S*)',f.read_text(),re.M):
  target=root/(name.replace('.','/')+'.lean');assert target.exists(),target;visit(target)
visit(root/'LeanPML.lean')
assert set(newfiles)<=reachable
snap=json.loads((root/'logs/v0.4.1/source_snapshot.json').read_text())['hashes'];stable={};changed={}
allowed={'README.md','PROGRESS.md','LeanPML.lean','Audit.lean','docs/source_inventory.md','docs/theorem_inventory.md','docs/claim_ledger.md','docs/pdf_formalization_marks.md','../results/V7_Maxwell_Debye_PML/V7_global_energy_副本.pdf'}
for f,old in snap.items():
 now=sha(root/f);(stable if now==old else changed)[f]={'before':old,'after':now}
assert set(changed)<=allowed,set(changed)-allowed
report=json.loads((root/'logs/v0.4.4/source_verification.json').read_text());report.update(unchanged_count=len(stable),unchanged=stable,authorized_changed=changed);(root/'logs/v0.4.4/source_verification.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
plan=json.loads((root/'logs/v0.4.4/pdf/annotation_plan.json').read_text());pdfresult=json.loads((root/'logs/v0.4.4/pdf/annotation_result.json').read_text());assert sha(Path(plan['target']))==pdfresult['sha256_after'];assert pdfresult['visual_review'].startswith('passed')
for e in plan['entries']:
 for n in e['theorems']:assert n in auditnames,n
 for f,h in e['source_hashes'].items():assert sha(root/f)==h,f
# 阅读文档中的本地链接全部定位，不检查未实现计划名或历史链接。
for file in ['README.md','PROGRESS.md']:
 s=(root/file).read_text()
 if file=='PROGRESS.md':s=s.split('\n---\n')[0]
 for target in re.findall(r'\]\(([^)]+)\)',s):
  if target.startswith(('http','#')):continue
  assert (root/target).exists(),(file,target)
assert not(root/'LeanPML/PML/MainSmoothRectangle.lean').exists()
(root/'logs/v0.4.4/all_new_theorems.json').write_text(json.dumps(theorems,ensure_ascii=False,indent=2)+'\n')
result={'all_four_stages_passed':True,'audited_declarations':len(auditnames),'new_theorems':len(theorems),'new_formal_files':len(newfiles),'all_new_theorems_audited':True,'all_files_in_default_import_chain':True,'protected_sources_and_locks_and_old_proofs_unchanged':True,'pdf_structure_and_visual_passed':True,'no_v0.5_implementation':True}
(root/'logs/v0.4.4/final_consistency.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n');print(json.dumps(result,ensure_ascii=False,indent=2))
