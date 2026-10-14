"""追加已核验弱分析范围；稳定ID阻止重复，保留原文和所有旧批注。"""
from pathlib import Path
from datetime import datetime
from collections import Counter
import json,hashlib,io,os,shutil
from pypdf import PdfReader,PdfWriter
from pypdf.generic import DictionaryObject,NameObject,ArrayObject,NumberObject,FloatObject,TextStringObject,RectangleObject
from reportlab.pdfgen import canvas
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
import pdfplumber
root=Path.cwd();folder=root/'logs/v1.0_completion/pdf';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
verified=json.loads((root/(folder/'verification_path.txt').read_text().strip()).read_text());assert verified['engineering_checks_passed']
for f,h in verified['sources'].items():assert sha(root/f)==h,f
source=json.loads((folder/'inspection.json').read_text());target=Path(source['target']);reader=PdfReader(target)
def anns(p):return list(p['/Annots']) if '/Annots' in p else []
entries=json.loads((folder/'entries.json').read_text())
ids={'LeanPML.v1.0.completion.'+e['id'] for e in entries}
found={str(a.get_object().get('/NM','')) for p in reader.pages for a in anns(p)}
if ids<=found:print('稳定ID已存在，未重复叠加。');raise SystemExit(0)
assert not ids&found,'部分标记已存在，须审查'
assert sha(target)==source['sha256'],'PDF自检查后发生变化'
assert len(reader.pages)==source['page_count']
audit=(root/verified['commands']['audit']['log']).read_text()
for e in entries:
 for n in e['theorems']:assert "'"+n+"'" in audit,n
font='/System/Library/Fonts/Supplemental/Arial Unicode.ttf';pdfmetrics.registerFont(TTFont('WeakChinese',font,subfontIndex=0))
for e in entries:
 size=e['font_size'];x=e['x']+(15 if e['tick'] else 0)
 width=max(pdfmetrics.stringWidth(l,'WeakChinese',size) for l in e['lines'])
 e['rect_top']=[e['x']-1,e['top']-2,x+width+1,e['top']+size+(len(e['lines'])-1)*(size+2.2)+2]
 e['build_audit']=verified['commands'];e['source_hashes']={f:sha(root/f) for f in e['modules']}
 assert all(ord(c) in pdfmetrics.getFont('WeakChinese').face.charToGlyph for l in e['lines'] for c in l)
def overlaps(a,b):return a[0]<b[2] and a[2]>b[0] and a[1]<b[3] and a[3]>b[1]
with pdfplumber.open(target) as pdf:
 for e in entries:
  p=pdf.pages[e['page']-1];r=e['rect_top'];assert 0<r[0]<r[2]<p.width and 0<r[1]<r[3]<p.height
  collisions=[c['text'] for c in p.chars if c['text'].strip() and overlaps(r,[c['x0'],c['top'],c['x1'],c['bottom']])]
  assert not collisions,(e['id'],collisions)
  for a in anns(reader.pages[e['page']-1]):
   x0,y0,x1,y1=map(float,a.get_object().get('/Rect',[0,0,0,0]));assert not overlaps(r,[x0,p.height-y1,x1,p.height-y0]),(e['id'],'old annotation')
stamp=datetime.now().astimezone().strftime('%Y%m%dT%H%M%S_%f%z');backup=folder/('V7_global_energy_副本_before_v1.0_completion_'+stamp+'.pdf');assert not backup.exists();shutil.copy2(target,backup)
(folder/'backup.json').write_text(json.dumps(dict(path=str(backup),sha256=sha(backup),timestamp=stamp),ensure_ascii=False,indent=2))
(folder/'annotation_plan.json').write_text(json.dumps(dict(entries=entries,font=font,input_sha256=sha(backup)),ensure_ascii=False,indent=2))
writer=PdfWriter();writer.clone_document_from_reader(reader)
for e in entries:
 page=writer.pages[e['page']-1];w=float(page.mediabox.width);h=float(page.mediabox.height)
 stream=io.BytesIO();can=canvas.Canvas(stream,pagesize=(w,h),pageCompression=1)
 can.setFillColorRGB(.84,.08,.10);can.setStrokeColorRGB(.84,.08,.10);x=e['x'];top=e['top'];size=e['font_size']
 if e['tick']:
  path=can.beginPath();path.moveTo(x,h-top-4);path.lineTo(x+4,h-top-7);path.lineTo(x+11,h-top-1)
  can.setLineWidth(1.55);can.setLineCap(1);can.setLineJoin(1);can.drawPath(path);x+=15
 can.setFont('WeakChinese',size)
 for i,line in enumerate(e['lines']):can.drawString(x,h-top-size-i*(size+2.2),line)
 can.save();stream.seek(0);page.merge_page(PdfReader(stream).pages[0])
 x0,y0,x1,y1=e['rect_top'];content=e['formula']+'\n'+e['scope']+'\n'+'\n'.join(e['theorems'])+'\n'+json.dumps(e['build_audit'],ensure_ascii=False)
 a=DictionaryObject({NameObject('/Type'):NameObject('/Annot'),NameObject('/Subtype'):NameObject('/Square'),NameObject('/Rect'):RectangleObject([x0,h-y1,x1,h-y0]),NameObject('/BS'):DictionaryObject({NameObject('/W'):NumberObject(0)}),NameObject('/Border'):ArrayObject([NumberObject(0)]*3),NameObject('/C'):ArrayObject([FloatObject(.84),FloatObject(.08),FloatObject(.10)]),NameObject('/T'):TextStringObject('LeanPML v1.0 收尾：准确限定范围'),NameObject('/Contents'):TextStringObject(content),NameObject('/NM'):TextStringObject('LeanPML.v1.0.completion.'+e['id']),NameObject('/F'):NumberObject(4)})
 writer.add_annotation(e['page']-1,a)
candidate=folder/'candidate.pdf'
with candidate.open('wb') as f:writer.write(f)
after=PdfReader(candidate)
def sig(a):
 o=a.get_object();return tuple(str(o.get(k)) for k in ['/Subtype','/Rect','/Contents','/T','/F','/NM'])
assert len(after.pages)==len(reader.pages)
for i,(before,page) in enumerate(zip(reader.pages,after.pages),1):
 assert list(before.mediabox)==list(page.mediabox) and list(before.cropbox)==list(page.cropbox)
 assert (page.extract_text() or '').startswith(before.extract_text() or ''),i
 assert Counter(map(sig,anns(before)))<=Counter(map(sig,anns(page))),i
os.replace(candidate,target)
report=dict(pages=len(after.pages),modified_pages=sorted({e['page'] for e in entries}),before_sha256=sha(backup),after_sha256=sha(target),old_annotations=source['annotations'],new_annotations=sum(len(anns(p)) for p in after.pages),added_ticks=sum(e['tick'] for e in entries),added_notes=sum(not e['tick'] for e in entries),original_text_preserved=True,old_annotations_preserved=True,overlap_check='passed',visual_review='pending',entries=entries)
(folder/'annotation_result.json').write_text(json.dumps(report,ensure_ascii=False,indent=2));print(json.dumps({k:v for k,v in report.items() if k!='entries'},ensure_ascii=False,indent=2))
