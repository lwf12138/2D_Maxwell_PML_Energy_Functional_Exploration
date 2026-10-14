from pathlib import Path
from pypdf import PdfReader
import pdfplumber,json,hashlib
p=Path.cwd();pdf=p.parent/'results/V7_Maxwell_Debye_PML/V7_global_energy_副本.pdf';r=PdfReader(pdf)
def ann(pg): return list(pg['/Annots']) if '/Annots' in pg else []
result={'target':str(pdf),'sha256':hashlib.sha256(pdf.read_bytes()).hexdigest(),'page_count':len(r.pages),'annotations':sum(len(ann(pg)) for pg in r.pages),'pages':[]}
with pdfplumber.open(pdf) as d:
 for i,pg in enumerate(d.pages):
  txt=pg.extract_text() or ''
  if any(k in txt for k in ['(5.1)','(5.7)','(7.5)']):
   result['pages'].append({'page':i+1,'width':pg.width,'height':pg.height,'text':txt,'chars':pg.chars,'words':pg.extract_words(),'annotations':[dict(rect=list(map(float,a.get_object().get('/Rect',[0,0,0,0]))),text=str(a.get_object().get('/Contents',''))) for a in ann(r.pages[i])]})
(p/'logs/v1.0.3/pdf/inspection.json').write_text(json.dumps(result,ensure_ascii=False,indent=2,default=str));print({k:v for k,v in result.items() if k!='pages'})
for pg in result['pages']:print(pg['page'],pg['width'],pg['height'],pg['text'][:230])
