"""只为指定副本增加v0.4已核验范围；备份/哈希/稳定ID/结构检查确保保留历史。"""
from pathlib import Path
from datetime import datetime
from collections import Counter
import hashlib,json,io,os,shutil
from pypdf import PdfReader,PdfWriter
from pypdf.generic import DictionaryObject,NameObject,ArrayObject,NumberObject,FloatObject,TextStringObject,RectangleObject
from reportlab.pdfgen import canvas
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
import pdfplumber
root=Path.cwd(); folder=root/'logs/v0.4.4/pdf';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
plan=json.loads((folder/'layout_suggestions.json').read_text()); target=Path(plan['target'])
accept=json.loads((root/'logs/v0.4.4/acceptance.json').read_text());assert accept['status']=='passed'
for kind in ['build','audit']:
 meta=json.loads((root/accept[kind]).with_suffix('.json').read_text());assert meta['exit_code']==0 and meta['status']=='finished'
for f,digest in accept['sources'].items(): assert sha(root/f)==digest,f
for e in plan['entries']:e.pop('status',None)
plan['entries'][7]['theorems'][0]='LeanPML.Rectangle.hasDerivAt_toL2_of_pointwise'
modules=[['PML/Equivalence'],['PML/OriginalSystem','Rectangle/HistoryL2'],['PML/Equivalence'],['PML/Equivalence'],['PML/Equivalence'],['Rectangle/Poincare'],['PML/Equivalence'],['Rectangle/L2Paths','PML/WeightedCalculus'],['PML/WeightedCalculus'],['Rectangle/Green','Rectangle/BoundaryTime']]
audittext=(root/accept['audit']).read_text()
for e,ms in zip(plan['entries'],modules):
 e['modules']=['LeanPML/'+m+'.lean' for m in ms]
 e['source_hashes']={f:sha(root/f) for f in e['modules']}
 e['build_log']=accept['build'];e['audit_log']=accept['audit']
 for n in e['theorems']: assert "'"+n+"'" in audittext,(e['id'],n)
plan['entries'][9]['scope']='真实全矩形四边公式，右−左+上−下；u₀零迹+PEC推出u迹，内部真实求导推出E_t迹。另要求闭端点E_t迹时，T=0须初始导数迹。弱H₀¹–H(div) Green未证明。'
plan['editable']=True;plan['font']='/System/Library/Fonts/Supplemental/Arial Unicode.ttf'
plan['build']=accept['build'];plan['audit']=accept['audit'];plan['source_hashes']=accept['sources']
plan['modified_pages']=sorted(set(e['page'] for e in plan['entries']+plan['notes']))
def annotations(p): return list(p['/Annots']) if '/Annots' in p else []
reader=PdfReader(target)
ids={'LeanPML.v0.4.'+e['id'] for e in plan['entries']+plan['notes']}
found={str(a.get_object().get('/NM','')) for p in reader.pages for a in annotations(p)}
if ids<=found:
 print('同一v0.4稳定ID已存在，未重复叠加。');raise SystemExit(0)
assert not(ids&found),'存在部分同ID标注，需人工检查'
assert sha(target)==plan['input_sha256'],'目标发生外部修改，停止保护用户批注'
assert len(reader.pages)==18
assert sum(len(annotations(p)) for p in reader.pages)==183
stamp=datetime.now().astimezone().strftime('%Y%m%dT%H%M%S_%f%z')
backup=folder/('V7_global_energy_副本_before_v0.4_'+stamp+'.pdf');assert not backup.exists();shutil.copy2(target,backup)
plan['backup']={'target':str(target),'backup':str(backup),'sha256_before':sha(backup),'timestamp':stamp}
(folder/'backup.json').write_text(json.dumps(plan['backup'],ensure_ascii=False,indent=2)+'\n')
(folder/'annotation_plan.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2)+'\n')
plan_hash=sha(folder/'annotation_plan.json')
pdfmetrics.registerFont(TTFont('LeanPMLChinese',plan['font'],subfontIndex=0))
draws=[]
for e in plan['entries']+plan['notes']:
 d=dict(e['draw']);d.update(id=e['id'],page=e['page'],tick=e['kind']=='tick')
 d['scope']=e.get('formula','范围图例')+'\n'+e.get('scope','\n'.join(d['lines']))+'\n'+'\n'.join(e.get('theorems',[]))+'\n证据：\n'+accept['build']+'\n'+accept['audit']
 size=d['font_size'];xtext=d['x']+(15 if d['tick'] else 0)
 width=max(pdfmetrics.stringWidth(line,'LeanPMLChinese',size) for line in d['lines'])
 d['rect_top']=[d['x']-1,d['top']-2,xtext+width+1,d['top']+size+(len(d['lines'])-1)*(size+2.2)+2]
 w,h=map(float,reader.pages[d['page']-1].mediabox[2:]);x0,y0,x1,y1=d['rect_top']
 assert 0<=x0<x1<w and 0<=y0<y1<h,(d['id'],d['rect_top'])
 assert all(ord(c) in pdfmetrics.getFont('LeanPMLChinese').face.charToGlyph for line in d['lines'] for c in line)
 draws.append(d)
def overlaps(a,b):return a[0]<b[2] and a[2]>b[0] and a[1]<b[3] and a[3]>b[1]
with pdfplumber.open(backup) as pdf:
 for d in draws:
  page=pdf.pages[d['page']-1];rect=d['rect_top']
  assert not [c['text'] for c in page.chars if c['text'].strip() and overlaps(rect,[c['x0'],c['top'],c['x1'],c['bottom']])],('text',d['id'])
  ph=float(reader.pages[d['page']-1].mediabox.height)
  for a in annotations(reader.pages[d['page']-1]):
   box=list(map(float,a.get_object().get('/Rect',[0,0,0,0])));ar=[box[0],ph-box[3],box[2],ph-box[1]]
   assert not overlaps(rect,ar),('old annotation',d['id'],ar)
for i,a in enumerate(draws):
 for b in draws[i+1:]:assert a['page']!=b['page'] or not overlaps(a['rect_top'],b['rect_top']),(a['id'],b['id'])
writer=PdfWriter();writer.clone_document_from_reader(reader)
for n in plan['modified_pages']:
 page=writer.pages[n-1];w=float(page.mediabox.width);h=float(page.mediabox.height)
 stream=io.BytesIO();can=canvas.Canvas(stream,pagesize=(w,h),pageCompression=1)
 can.setFillColorRGB(.84,.08,.10);can.setStrokeColorRGB(.84,.08,.10)
 for d in [d for d in draws if d['page']==n]:
  x=d['x'];top=d['top'];size=d['font_size']
  if d['tick']:
   line=can.beginPath();line.moveTo(x,h-top-6);line.lineTo(x+4,h-top-10);line.lineTo(x+11,h-top-1)
   can.setLineWidth(1.55);can.setLineCap(1);can.setLineJoin(1);can.drawPath(line);x+=15
  can.setFont('LeanPMLChinese',size)
  for i,text in enumerate(d['lines']):can.drawString(x,h-top-size-i*(size+2.2),text)
 can.save();stream.seek(0);page.merge_page(PdfReader(stream).pages[0])
 for d in [d for d in draws if d['page']==n]:
  x0,y0,x1,y1=d['rect_top'];annotation=DictionaryObject({NameObject('/Type'):NameObject('/Annot'),NameObject('/Subtype'):NameObject('/Square'),NameObject('/Rect'):RectangleObject([x0,h-y1,x1,h-y0]),NameObject('/BS'):DictionaryObject({NameObject('/W'):NumberObject(0)}),NameObject('/Border'):ArrayObject([NumberObject(0)]*3),NameObject('/C'):ArrayObject([FloatObject(.84),FloatObject(.08),FloatObject(.10)]),NameObject('/T'):TextStringObject('LeanPML v0.4 已验证范围' if d['tick'] else 'LeanPML v0.4 范围说明'),NameObject('/Contents'):TextStringObject(d['scope']),NameObject('/NM'):TextStringObject('LeanPML.v0.4.'+d['id']),NameObject('/F'):NumberObject(4)})
  writer.add_annotation(n-1,annotation)
writer.add_metadata({'/LeanPMLV04MarkPlanSHA256':plan_hash,'/LeanPMLV04Evidence':accept['build']+'; '+accept['audit']})
candidate=folder/'annotated_v0.4_candidate.pdf'
with candidate.open('wb') as f:writer.write(f)
after=PdfReader(candidate);assert len(after.pages)==18
def signature(a):
 o=a.get_object();return tuple(str(o.get(k)) for k in ['/Subtype','/Rect','/Contents','/T','/F','/NM'])
for n,(old,new) in enumerate(zip(reader.pages,after.pages),1):
 assert list(old.mediabox)==list(new.mediabox) and list(old.cropbox)==list(new.cropbox),n
 assert (new.extract_text() or '').startswith(old.extract_text() or ''),('text changed',n)
 assert Counter(map(signature,annotations(old)))<=Counter(map(signature,annotations(new))),('old comments',n)
os.replace(candidate,target)
report={'pages':18,'old_annotations':183,'added_annotations':len(draws),'added_red_ticks':sum(d['tick'] for d in draws),'annotations_after':sum(len(annotations(p)) for p in after.pages),'modified_pages':plan['modified_pages'],'original_text_preserved':True,'old_annotations_preserved':True,'text_and_annotation_overlap':0,'sha256_before':sha(backup),'sha256_after':sha(target),'plan_sha256':plan_hash,'draws':draws,'visual_review':'pending'}
(folder/'annotation_result.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='draws'},ensure_ascii=False,indent=2))
