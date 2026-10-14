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
root=Path.cwd();folder=root/'logs/v1.0.3/pdf';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
verified=json.loads((root/'logs/v1.0.3/verification_before_pdf.json').read_text());assert verified['engineering_checks_passed']
for f,h in verified['sources'].items():assert sha(root/f)==h,f
source=json.loads((folder/'inspection.json').read_text());target=Path(source['target']);reader=PdfReader(target)
def anns(p):return list(p['/Annots']) if '/Annots' in p else []
entries=[
 dict(id='weak-poincare-conservative',page=7,printed_page=7,formula='(5.1) 的保守常数子结论',tick=False,x=68,top=520,font_size=7,
 lines=['v1.0.2：弱 H₀¹ Poincaré 已证，C_P=2Lx；保守常数，非原式精确 π 常数。'],
 theorems=['LeanPML.Rectangle.weak_poincare','LeanPML.Rectangle.weakPoincareDomain'],
 modules=['LeanPML/Rectangle/WeakPoincare.lean'],scope='在紧支光滑图闭包定义的 H₀¹ 上推广保守常数。一般旧光滑零迹场进入闭包的逼近仍缺；不标原精确公式完成。'),
 dict(id='memory-pointwise-scope',page=8,printed_page=8,formula='(5.7) 点上的真实时间积分子结论',tick=False,x=68,top=780,font_size=7,
 lines=['v1.0.2 (5.7)：点上真实 ODE/时间积分版已证；弱场连接及 (5.8) 加权传播未完成。'],
 theorems=['LeanPML.PML.auxiliary_memory_formula'],modules=['LeanPML/PML/AuxiliaryMemory.lean'],
 scope='实际实值时间函数闭区间连续、内部 HasDerivAt，推出变常数公式；梯度输入尚未与弱场识别，不标加权传播完成。'),
 dict(id='weak-green-zero-trace',page=11,printed_page=11,formula='(7.5) 零迹弱 Green',tick=True,x=68,top=490,font_size=7,
 lines=['v1.0.2 (7.5)：H₀¹ × H(div) 弱零迹 Green；通量无额外边界条件。',
        'H₀¹ 为紧支光滑图闭包；非零迹理论、弱 PML 主定理仍未完成。'],
 theorems=['LeanPML.Rectangle.weak_green','LeanPML.Rectangle.weakGreenDomain'],
 modules=['LeanPML/Rectangle/WeakGreen.lean'],scope='真实弱散度测试配对经线性张成及图范数闭包推广；已填入旧受限空间接口。无一般 Green 输入，无 Λ·n=0；不是最终弱原系统定理。')]
ids={'LeanPML.v1.0.partial.'+e['id'] for e in entries}
found={str(a.get_object().get('/NM','')) for p in reader.pages for a in anns(p)}
if ids<=found:print('稳定ID已存在，未重复叠加。');raise SystemExit(0)
assert not ids&found,'部分标记已存在，须审查'
assert sha(target)==source['sha256'],'PDF自检查后发生变化'
assert len(reader.pages)==source['page_count']
audit=(root/verified['commands']['v1.0.3']['axioms_audit']['log']).read_text()
for e in entries:
 for n in e['theorems']:assert "'"+n+"'" in audit,n
font='/System/Library/Fonts/Supplemental/Arial Unicode.ttf';pdfmetrics.registerFont(TTFont('WeakChinese',font,subfontIndex=0))
for e in entries:
 size=e['font_size'];x=e['x']+(15 if e['tick'] else 0)
 width=max(pdfmetrics.stringWidth(l,'WeakChinese',size) for l in e['lines'])
 e['rect_top']=[e['x']-1,e['top']-2,x+width+1,e['top']+size+(len(e['lines'])-1)*(size+2.2)+2]
 e['build_audit']=verified['commands']['v1.0.3'];e['source_hashes']={f:sha(root/f) for f in e['modules']}
 assert all(ord(c) in pdfmetrics.getFont('WeakChinese').face.charToGlyph for l in e['lines'] for c in l)
def overlaps(a,b):return a[0]<b[2] and a[2]>b[0] and a[1]<b[3] and a[3]>b[1]
with pdfplumber.open(target) as pdf:
 for e in entries:
  p=pdf.pages[e['page']-1];r=e['rect_top'];assert 0<r[0]<r[2]<p.width and 0<r[1]<r[3]<p.height
  collisions=[c['text'] for c in p.chars if c['text'].strip() and overlaps(r,[c['x0'],c['top'],c['x1'],c['bottom']])]
  assert not collisions,(e['id'],collisions)
  for a in anns(reader.pages[e['page']-1]):
   x0,y0,x1,y1=map(float,a.get_object().get('/Rect',[0,0,0,0]));assert not overlaps(r,[x0,p.height-y1,x1,p.height-y0]),(e['id'],'old annotation')
stamp=datetime.now().astimezone().strftime('%Y%m%dT%H%M%S_%f%z');backup=folder/('V7_global_energy_副本_before_v1.0_partial_'+stamp+'.pdf');assert not backup.exists();shutil.copy2(target,backup)
(folder/'backup.json').write_text(json.dumps(dict(path=str(backup),sha256=sha(backup),timestamp=stamp),ensure_ascii=False,indent=2))
(folder/'annotation_plan.json').write_text(json.dumps(dict(entries=entries,font=font,input_sha256=sha(backup)),ensure_ascii=False,indent=2))
writer=PdfWriter();writer.clone_document_from_reader(reader)
for e in entries:
 page=writer.pages[e['page']-1];w=float(page.mediabox.width);h=float(page.mediabox.height)
 stream=io.BytesIO();can=canvas.Canvas(stream,pagesize=(w,h),pageCompression=1)
 can.setFillColorRGB(.84,.08,.10);can.setStrokeColorRGB(.84,.08,.10);x=e['x'];top=e['top'];size=e['font_size']
 if e['tick']:
  path=can.beginPath();path.moveTo(x,h-top-6);path.lineTo(x+4,h-top-10);path.lineTo(x+11,h-top-1)
  can.setLineWidth(1.55);can.setLineCap(1);can.setLineJoin(1);can.drawPath(path);x+=15
 can.setFont('WeakChinese',size)
 for i,line in enumerate(e['lines']):can.drawString(x,h-top-size-i*(size+2.2),line)
 can.save();stream.seek(0);page.merge_page(PdfReader(stream).pages[0])
 x0,y0,x1,y1=e['rect_top'];content=e['formula']+'\n'+e['scope']+'\n'+'\n'.join(e['theorems'])+'\n'+json.dumps(e['build_audit'],ensure_ascii=False)
 a=DictionaryObject({NameObject('/Type'):NameObject('/Annot'),NameObject('/Subtype'):NameObject('/Square'),NameObject('/Rect'):RectangleObject([x0,h-y1,x1,h-y0]),NameObject('/BS'):DictionaryObject({NameObject('/W'):NumberObject(0)}),NameObject('/Border'):ArrayObject([NumberObject(0)]*3),NameObject('/C'):ArrayObject([FloatObject(.84),FloatObject(.08),FloatObject(.10)]),NameObject('/T'):TextStringObject('LeanPML v1.0 弱分析子结论'),NameObject('/Contents'):TextStringObject(content),NameObject('/NM'):TextStringObject('LeanPML.v1.0.partial.'+e['id']),NameObject('/F'):NumberObject(4)})
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
report=dict(pages=len(after.pages),modified_pages=[7,8,11],before_sha256=sha(backup),after_sha256=sha(target),old_annotations=source['annotations'],new_annotations=sum(len(anns(p)) for p in after.pages),added_ticks=1,added_notes=2,original_text_preserved=True,old_annotations_preserved=True,overlap_check='passed',visual_review='pending',entries=entries)
(folder/'annotation_result.json').write_text(json.dumps(report,ensure_ascii=False,indent=2));print(json.dumps({k:v for k,v in report.items() if k!='entries'},ensure_ascii=False,indent=2))
