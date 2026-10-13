from pathlib import Path
import json
import pdfplumber
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
p=Path.cwd();folder=p/'logs/v0.3.5/pdf';draft=json.loads((folder/'layout_draft.json').read_text())
pdfmetrics.registerFont(TTFont('QAChinese','/System/Library/Fonts/Supplemental/Arial Unicode.ttf'))
boxes=[];errors=[]
for e in draft['entries']:
 d=dict(e['draw']);d.update(id=e['id'],page=e['page'],tick=True);boxes.append(d)
for n in draft['notes']:
 d=dict(n);d.update(tick=False);boxes.append(d)
with pdfplumber.open(p/'../results/V7_Maxwell_Debye_PML/V7_global_energy_副本.pdf')as pdf:
 for d in boxes:
  fs=d['font_size'];tx=d['x']+(15 if d['tick']else 0)
  width=max(pdfmetrics.stringWidth(s,'QAChinese',fs)for s in d['lines'])
  box=[d['x']-1,d['top']-2,tx+width+1,d['top']+fs+(len(d['lines'])-1)*(fs+2.2)+2]
  d['rect_top']=box;x0,y0,x1,y1=box
  if not(0<=x0<x1<595.28 and 0<=y0<y1<841.89):errors.append({'id':d['id'],'outside':box})
  chars=[c['text']for c in pdf.pages[d['page']-1].chars if c['text'].strip()and c['x0']<x1 and c['x1']>x0 and c['top']<y1 and c['bottom']>y0]
  if chars:errors.append({'id':d['id'],'overlap':chars,'box':box})
for i,a in enumerate(boxes):
 for b in boxes[i+1:]:
  if a['page']!=b['page']:continue
  x0,y0,x1,y1=a['rect_top'];u0,v0,u1,v1=b['rect_top']
  if x0<u1 and x1>u0 and y0<v1 and y1>v0:errors.append({'new_overlap':[a['id'],b['id']]})
(folder/'coordinate_preflight.json').write_text(json.dumps({'boxes':boxes,'errors':errors},ensure_ascii=False,indent=2))
print(json.dumps({'errors':errors,'entries':len(draft['entries']),'notes':len(draft['notes'])},ensure_ascii=False,indent=2));assert not errors
