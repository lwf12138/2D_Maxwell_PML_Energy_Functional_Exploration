from pathlib import Path
import json
import pdfplumber
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
root=Path.cwd();folder=root/'logs/v0.3.1/pdf'
draft=json.loads((folder/'proof_entries.json').read_text())
pdfmetrics.registerFont(TTFont('LeanPMLChinese','/System/Library/Fonts/Supplemental/Arial Unicode.ttf',subfontIndex=0))
target=root.parent/'results/V7_Maxwell_Debye_PML/V7_global_energy_副本.pdf'
draws=[]
for e in draft['entries']:
 if e['new_tick']:
  d=dict(e['draw']);d.update(id=e['id'],page=e['page'],tick=True);draws.append(d)
for n in draft['notes']:
 d=dict(n);d.update(tick=False);draws.append(d)
with pdfplumber.open(target) as pdf:
 for d in draws:
  size=d['font_size'];leading=size+2.2;tx=d['x']+15 if d['tick'] else d['x']
  width=max(pdfmetrics.stringWidth(s,'LeanPMLChinese',size)for s in d['lines'])
  rect=[d['x']-1,d['top']-2,tx+width+1,d['top']+size+(len(d['lines'])-1)*leading+2]
  x0,y0,x1,y1=rect
  overlap=[c['text'] for c in pdf.pages[d['page']-1].chars if c['x0']<x1 and c['x1']>x0 and c['top']<y1 and c['bottom']>y0 and c['text'].strip()]
  d.update(rect_top=rect,overlap=overlap)
  print(d['id'],rect,overlap)
(folder/'coordinate_preflight.json').write_text(json.dumps(draws,ensure_ascii=False,indent=2)+'\n')
assert not any(d['overlap']for d in draws)
