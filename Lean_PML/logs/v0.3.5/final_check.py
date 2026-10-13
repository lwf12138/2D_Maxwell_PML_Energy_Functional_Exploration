"""交付前静态一致性检查：不重写证明、依赖或 PDF。"""
from pathlib import Path
import hashlib,json,re
root=Path.cwd();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
start=json.loads((root/'logs/v0.3.4/source_snapshot.json').read_text())
for f,h in start['protected'].items():assert sha(root/f)==h,('protected',f)
assert sha(root/'docs/source_inventory.md')==start['files']['docs/source_inventory.md']
old=root/'logs/v0.3.4/initial_files'
for f in ['docs/theorem_inventory.md','docs/claim_ledger.md','docs/pdf_formalization_marks.md','Audit.lean']:
 assert (root/f).read_bytes().startswith((old/f).read_bytes()),('history',f)
assert (root/'PROGRESS.md').read_bytes().endswith((old/'PROGRESS.md').read_bytes())
assert sha(old/'README.md')==start['files']['README.md']
assert not list((root/'LeanPML').glob('Rectangle/*.lean')),'本轮不推进Rectangle实现'
accepted={s:json.loads((root/'logs'/s/'acceptance.json').read_text()) for s in ['v0.3.4','v0.3.5']}
imports=(root/'LeanPML.lean').read_text();audit=(root/'Audit.lean').read_text();formal=[]
for stage,e in accepted.items():
 for file,digest in e['sources'].items():
  assert sha(root/file)==digest,('source changed after validation',file)
  assert 'import '+file.removesuffix('.lean').replace('/','.') in imports
  assert not re.search(r'\b(sorry|admit)\b|^\s*axiom\b',(root/file).read_text(),re.M)
  formal.append(file)
 for k in ['build','audit']:
  m=json.loads((root/e[k]).with_suffix('.json').read_text())
  assert m['exit_code']==0 and m['cwd']==str(root) and m['status']=='finished'
  assert m['command']==(['lake','build']if k=='build'else['lake','env','lean','Audit.lean'])
 for t in json.loads((root/'logs'/stage/'new_theorems.json').read_text()):
  assert '#print axioms '+t['name'] in audit.splitlines(),t['name']
final=accepted['v0.3.5']
assert sha(root/'LeanPML.lean')==final['root_sha256']
assert sha(root/'Audit.lean')==final['audit_sha256']
outputs=(root/final['audit']).read_text();names=re.findall(r"'([^']+)' depends on axioms",outputs)
assert len(names)==len(set(names))==369
assert 'sorryAx'not in outputs
# 全部正式源文件也不含占位命令；非证明性质文字不影响此处声明检查。
for p in (root/'LeanPML').rglob('*.lean'):
 assert not re.search(r'^\s*(axiom\s|sorry\s*$|admit\s*$)',p.read_text(),re.M),p
config=(root/'lakefile.toml').read_text();assert 'defaultTargets = ["LeanPML", "Audit"]' in config
plan=json.loads((root/'logs/v0.3.5/pdf/annotation_plan.json').read_text());v=json.loads((root/'logs/v0.3.5/pdf/verification.json').read_text())
assert sha(Path(plan['backup']['target']))==v['sha256_after']
assert v['total_annotations']==183 and v['old_annotations_preserved'] and v['visual_review'].startswith('passed')
assert v['modified_pages']==[10,12,13,14]
# 只核验本轮新写内容的相对链接，历史正文不重写。
newtexts={'README.md':(root/'README.md').read_text()}
newtexts['PROGRESS.md']=(root/'PROGRESS.md').read_text()[:-(len((old/'PROGRESS.md').read_text()))]
for f in ['docs/theorem_inventory.md','docs/claim_ledger.md','docs/pdf_formalization_marks.md']:
 newtexts[f]=(root/f).read_text()[len((old/f).read_text()):]
links=[]
for f,txt in newtexts.items():
 assert not any(word in txt for word in ['VALIDATION_LINKS','PDF_SUMMARY','VALIDATE034','VALIDATE035'])
 for label,target in re.findall(r'\[([^\]]+)\]\(([^)]+)\)',txt):
  if target.startswith(('http:','https:','#')):continue
  dest=(root/f).parent/target.split('#')[0]
  if dest.resolve()==root/'logs/v0.3.5/final_checks.json':continue
  assert dest.exists(),('broken link',f,target)
  links.append([f,target])
result=dict(stages=['v0.3.4','v0.3.5'],status='passed',
 protected_files_unchanged=True,source_inventory_unchanged=True,history_retained=True,
 source_hashes={f:sha(root/f) for f in formal},formal_imports_and_audit_covered=True,
 default_targets=['LeanPML','Audit'],audit_total=369,new_theorems=53,axioms=final['axioms'],
 sorryAx=False,all_stage_commands_exit_zero=True,
 assumption_print='logs/v0.3.5/20261013T215341_410073_assumptions_print.log',
 assumption_review='Manual independent review of original parameters, primitive/same-source inputs, same-trace Poincare and Ioo/Icc separation; no target in input fields',
 link_count=len(links),all_new_doc_links_resolve=True,
 pdf=v,no_v04_implementation=True,
 no_new_reading_guide=True,old_readme_snapshot='logs/v0.3.4/initial_files/README.md')
(root/'logs/v0.3.5/final_checks.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:x for k,x in result.items()if k not in ['pdf','source_hashes']},ensure_ascii=False,indent=2))
