from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import hashlib,json,re,shutil
from pypdf import PdfReader
import pdfplumber
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
root=Path.cwd();folder=root/'logs/v0.3.3/pdf'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
build='20261013T100156_159842_lake_build';audit='20261013T100321_602582_axioms_audit'
for stem in [build,audit]:
 m=json.loads((root/'logs/v0.3.3'/(stem+'.json')).read_text())
 assert m['exit_code']==0 and m['status']=='finished'
txt=(root/'logs/v0.3.3'/(audit+'.log')).read_text()
assert 'sorryAx' not in txt
audited=set(re.findall(r"'([^']+)' depends on axioms",txt))
assert len(audited)==316
draft=json.loads((folder/'proof_entries.json').read_text())
for e in draft['entries']:
 assert set(e['theorems'])<=audited
 e.update(source_sha256=sha(root/e['module']),build_log='logs/v0.3.3/'+build+'.log',audit_log='logs/v0.3.3/'+audit+'.log')
old_count=0
for stage in ['v0.2.3','v0.2.4','v0.3.1']:
 old=json.loads((root/'logs'/stage/'pdf/annotation_plan.json').read_text())
 for e in old['entries']:
  assert set(e['theorems'])<=audited,(stage,e['id'])
  old_count+=1
initial=json.loads((root/'logs/v0.3.2/source_snapshot.json').read_text())['hashes']
target=(root/'../results/V7_Maxwell_Debye_PML/V7_global_energy_副本.pdf').resolve()
for file,digest in initial.items():
 assert sha(root/file)==digest,('入场后受保护文件变化',file)
if (folder/'backup.json').exists():
 backup=json.loads((folder/'backup.json').read_text())
 assert sha(Path(backup['backup']))==backup['sha256_before']==sha(target)
else:
 name='before_v0.3.2-v0.3.3_'+datetime.now(ZoneInfo('Asia/Shanghai')).strftime('%Y%m%dT%H%M%S')+'.pdf'
 dest=folder/name
 assert not dest.exists()
 shutil.copy2(target,dest)
 backup={'target':str(target),'backup':str(dest),'sha256_before':sha(target),'bytes_before':target.stat().st_size}
 (folder/'backup.json').write_text(json.dumps(backup,ensure_ascii=False,indent=2))
reader=PdfReader(target)
plan=dict(stage='v0.3.2–v0.3.3',page_count=len(reader.pages),backup=backup,build=build,audit=audit,
 entries=draft['entries'],notes=draft['notes'],font='/System/Library/Fonts/Supplemental/Arial Unicode.ttf',
 modified_pages=[10,11,12,13],protected_hashes={str((root/f).resolve()):h for f,h in initial.items()if not f.endswith('_副本.pdf')},
 current_audited_theorems=len(audited),old_mark_entries_rechecked=old_count,
 old_annotations_preserved_count=sum(len(list(p['/Annots']))if'/Annots'in p else 0 for p in reader.pages))
# 定位预检不修改 PDF。采用实际字形宽度，并核对旧文本、页边与新标记相互遮挡。
pdfmetrics.registerFont(TTFont('QAChinese',plan['font']))
boxes=[];errors=[]
for e in plan['entries']:
 d=dict(e['draw']);d.update(id=e['id'],page=e['page'],tick=True);boxes.append(d)
for n in plan['notes']:
 d=dict(n);d.update(tick=False);boxes.append(d)
with pdfplumber.open(target)as pdf:
 for d in boxes:
  fs=d['font_size'];tx=d['x']+(15 if d['tick']else 0)
  width=max(pdfmetrics.stringWidth(s,'QAChinese',fs)for s in d['lines'])
  box=[d['x']-1,d['top']-2,tx+width+1,d['top']+fs+(len(d['lines'])-1)*(fs+2.2)+2]
  d['rect_top']=box;x0,y0,x1,y1=box
  assert 0<=x0<x1<595.28 and 0<=y0<y1<841.89,d
  chars=[c['text']for c in pdf.pages[d['page']-1].chars if c['text'].strip()and c['x0']<x1 and c['x1']>x0 and c['top']<y1 and c['bottom']>y0]
  if chars:errors.append({'id':d['id'],'overlap':chars,'box':box})
for i,a in enumerate(boxes):
 for b in boxes[i+1:]:
  if a['page']!=b['page']:continue
  x0,y0,x1,y1=a['rect_top'];u0,v0,u1,v1=b['rect_top']
  if x0<u1 and x1>u0 and y0<v1 and y1>v0:errors.append({'new_overlap':[a['id'],b['id']]})
(folder/'coordinate_preflight.json').write_text(json.dumps({'boxes':boxes,'errors':errors},ensure_ascii=False,indent=2))
assert not errors,errors
assert not(folder/'annotation_plan.json').exists(),'计划已存在，禁止静默覆盖'
(folder/'annotation_plan.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2))
print(json.dumps({'page_count':len(reader.pages),'old_annotations':plan['old_annotations_preserved_count'],'new_ticks':len(plan['entries']),'notes':len(plan['notes']),'old_entries_rechecked':old_count,'preflight':'passed','backup':backup},ensure_ascii=False,indent=2))
