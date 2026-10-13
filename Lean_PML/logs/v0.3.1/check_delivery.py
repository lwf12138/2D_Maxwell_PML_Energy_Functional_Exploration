"""v0.3.1 最终交付核对；不写 Lean/PDF，只保存验收数据。"""
from pathlib import Path
import hashlib,json,re
root=Path.cwd()
folder=root/'logs/v0.3.1'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
initial=json.loads((folder/'initial_hashes.json').read_text())
protected=['lean-toolchain','lakefile.toml','lake-manifest.json','ROADMAP_lean_PML_revised.md',
 'docs/model_contract.md','docs/scope.md','docs/source_inventory.md']
for f in protected:
 assert sha(root/f)==initial[f],('protected changed',f)
pdf_inputs=json.loads((folder/'pdf/input_hashes.json').read_text())
for f,h in pdf_inputs.items():
 if not f.endswith('_副本.pdf'):assert sha(Path(f))==h, f
build='20261013T002136_137117_lake_build'
audit='20261013T002105_759533_axioms_audit'
for stem in [build,audit]:
 m=json.loads((folder/(stem+'.json')).read_text())
 assert m['exit_code']==0 and m['status']=='finished'
 assert m['cwd']==str(root)
text=(folder/(audit+'.log')).read_text()
audited=set(re.findall(r"^'([^']+)' (?:depends on axioms|does not depend on any axioms)",text,re.M))
assert len(audited)==263, len(audited)
assert 'sorryAx' not in text
all_axioms=set()
for match in re.findall(r"axioms: \[([^\]]*)\]",text):
 all_axioms.update(x.strip() for x in match.split(',') if x.strip())
assert all_axioms <= {'propext','Classical.choice','Quot.sound'},all_axioms
new=json.loads((folder/'new_theorems.json').read_text())
assert len(new)==109
assert {x['name'] for x in new} <= audited
old_audit=(folder/'initial_files/Audit.lean').read_text()
old_names=set(re.findall(r'^#print axioms (LeanPML\.[^\s]+)',old_audit,re.M))
assert len(old_names)==154 and old_names <= audited
modules=set()
def visit(module):
 if module in modules:return
 modules.add(module)
 p=root/(module.replace('.','/')+'.lean')
 assert p.exists(),p
 for dep in re.findall(r'^import (LeanPML(?:\.[^\s]+)?)',p.read_text(),re.M):visit(dep)
visit('LeanPML')
for entry in new:
 assert entry['file'][:-5].replace('/','.') in modules,entry
for f in root.glob('LeanPML/**/*.lean'):
 s=f.read_text()
 s=re.sub(r'/-[\s\S]*?-/', '',s)
 s=re.sub(r'--[^\n]*','',s)
 assert not re.search(r'\b(sorry|admit|axiom)\b',s),f
for f in set(e['file'] for e in new):
 stem=Path(f).with_suffix('')
 olean=root/'.lake/build/lib/lean'/stem.with_suffix('.olean')
 assert olean.exists(),olean
old_progress=(folder/'initial_files/PROGRESS.md').read_text()
assert (root/'PROGRESS.md').read_text().endswith(old_progress)
old_inventory=(folder/'initial_files/docs/theorem_inventory.md').read_text()
assert (root/'docs/theorem_inventory.md').read_text().startswith(old_inventory)
old_ledger=(folder/'initial_files/docs/pdf_formalization_marks.md').read_text()
ledger=(root/'docs/pdf_formalization_marks.md').read_text()
assert '\n'.join(old_ledger.splitlines()[1:]) in ledger
assert 'v0.3.1' in ledger
pdf=json.loads((folder/'pdf/verification.json').read_text())
assert pdf['page_count']==18 and pdf['modified_pages']==[8,9,11,12]
assert pdf['old_annotations']==141 and pdf['total_annotations']==150
assert pdf['old_annotations_preserved'] and pdf['protected_files_unchanged']
assert pdf['visual_review'].startswith('passed')
assert sha(Path(next(f for f in pdf_inputs if f.endswith('_副本.pdf'))))==pdf['sha256_after']
# 只核对本轮新增/重写说明中的本地链接；历史记录不因旧失效链接被改写。
missing_links=[]
for fn,s in [('README.md',(root/'README.md').read_text()),
 ('PROGRESS.md',(root/'PROGRESS.md').read_text()[:-len(old_progress)]),
 ('docs/theorem_inventory.md',(root/'docs/theorem_inventory.md').read_text()[len(old_inventory):])]:
 for target in re.findall(r'\[[^\]]+\]\(([^)]+)\)',s):
  if target.startswith(('http:','https:','#')):continue
  target=target.split('#')[0]
  if target and not (root/fn).parent.joinpath(target).exists():missing_links.append([fn,target])
assert not missing_links,missing_links
report=dict(stage='v0.3.1',status='passed',formal_modules=len(modules)-1,
 new_theorems=len(new),old_theorems=len(old_names),audited_theorems=len(audited),
 standard_axioms=sorted(all_axioms),build=build,audit=audit,protected_unchanged=protected,
 source_hashes={f:sha(root/f) for f in sorted(set(x['file'] for x in new))},
 pdf_pages=18,pdf_modified_pages=pdf['modified_pages'],pdf_sha256=pdf['sha256_after'],
 old_pdf_annotations_preserved=141,total_pdf_annotations=150,
 history_preserved=True,new_document_links_valid=True,no_placeholders=True)
(folder/'final_checks.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(report,ensure_ascii=False,indent=2))
