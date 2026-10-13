"""从本轮已通过构建和审计建立 PDF 证据计划；不编辑目标。
使用：python build_mark_plan.py BUILD_STEM AUDIT_STEM
先创建 proof_entries.json：entries 为逐条已核验声明，notes 为仅定义/范围说明。
"""
from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import hashlib,json,re,shutil,sys
from pypdf import PdfReader
root=Path.cwd();folder=root/'logs/v0.3.1/pdf'
if len(sys.argv)!=3:
 raise SystemExit('需要本轮 build 与 audit 的完整文件 stem')
build,audit=sys.argv[1:]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for stem in [build,audit]:
 metadata=json.loads((root/'logs/v0.3.1'/(stem+'.json')).read_text())
 assert metadata['exit_code']==0 and metadata['status']=='finished',stem
 assert metadata['cwd']==str(root)
audit_text=(root/'logs/v0.3.1'/(audit+'.log')).read_text()
assert 'sorryAx' not in audit_text
audited=set(re.findall(r"'([^']+)' depends on axioms",audit_text))
assert audited
draft=json.loads((folder/'proof_entries.json').read_text())
for entry in draft['entries']:
 for name in entry['theorems']:
  assert name in audited,(entry['id'],name,'未在本轮审计输出中')
 assert entry.get('new_tick') is not None
 assert not entry['new_tick'] or entry['theorems']
 entry.update(source_sha256=sha(root/entry['module']),
              build_log='logs/v0.3.1/'+build+'.log',audit_log='logs/v0.3.1/'+audit+'.log')
old_count=0
for stage in ['v0.2.3','v0.2.4']:
 old=json.loads((root/'logs'/stage/'pdf/annotation_plan.json').read_text())
 for e in old['entries']:
  for name in e['theorems']:
   assert name in audited,('旧标注定理未在新审计',name)
  old_count+=1
target=root.parent/'results/V7_Maxwell_Debye_PML/V7_global_energy_副本.pdf'
original_hashes=json.loads((folder/'input_hashes.json').read_text())
assert sha(target)==original_hashes[str(target)],'目标在读取后改变，须重新核对'
protected={name:digest for name,digest in original_hashes.items()if name!=str(target)}
for name,digest in protected.items():
 assert sha(Path(name))==digest,('受保护文件发生变更',name)
reader=PdfReader(target)
assert len(reader.pages)==18
if (folder/'backup.json').exists():
 backup=json.loads((folder/'backup.json').read_text())
 assert backup['sha256_before']==sha(target)==sha(Path(backup['backup']))
else:
 timestamp=datetime.now(ZoneInfo('Asia/Shanghai')).strftime('%Y%m%dT%H%M%S')
 output=folder/('before_v0.3.1_'+timestamp+'.pdf')
 assert not output.exists()
 shutil.copy2(target,output)
 backup=dict(target=str(target),backup=str(output),sha256_before=sha(target),
             bytes_before=target.stat().st_size)
 (folder/'backup.json').write_text(json.dumps(backup,ensure_ascii=False,indent=2)+'\n')
plan=dict(stage='v0.3.1',page_count=18,backup=backup,build=build,audit=audit,
 entries=draft['entries'],notes=draft['notes'],
 font='/System/Library/Fonts/Supplemental/Arial Unicode.ttf',
 modified_pages=sorted({e['page']for e in draft['entries']if e['new_tick']}|{n['page']for n in draft['notes']}),
 protected_hashes=protected,current_audited_theorems=len(audited),
 old_mark_entries_rechecked=old_count,
 old_annotations_preserved_count=sum(len(list(p['/Annots']))if '/Annots'in p else 0 for p in reader.pages))
assert not (folder/'annotation_plan.json').exists(),'正式计划已存在，须人工审阅后另建修订，禁止静默覆盖'
(folder/'annotation_plan.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:v for k,v in plan.items()if k not in ['entries','notes','protected_hashes']},ensure_ascii=False,indent=2))
