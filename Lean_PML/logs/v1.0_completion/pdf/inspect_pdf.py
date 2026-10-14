from pathlib import Path
from pypdf import PdfReader
import pdfplumber,json,hashlib
p=Path('../results/V7_Maxwell_Debye_PML/V7_global_energy_副本.pdf').resolve();r=PdfReader(p)
def anns(page):return list(page['/Annots']) if '/Annots' in page else []
d={'target':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'page_count':len(r.pages),'annotations':sum(len(anns(x)) for x in r.pages)}
Path('logs/v1.0_completion/pdf/inspection.json').write_text(json.dumps(d,ensure_ascii=False,indent=2))
with pdfplumber.open(p) as doc:
 out=[]
 for i,page in enumerate(doc.pages,1):
  text=page.extract_text() or ''
  if any(n in text for n in ['(5.1)','(5.7)','(6.6)','(6.7)','(10.1)']):
   print(i,text[:100],text[-80:]);out.append({'page':i,'text':text,'chars':[{'text':c['text'],'x0':c['x0'],'x1':c['x1'],'top':c['top'],'bottom':c['bottom']} for c in page.chars], 'annotations':[dict(rect=list(a.get_object().get('/Rect',[])),contents=str(a.get_object().get('/Contents',''))) for a in anns(r.pages[i-1])]})
 Path('logs/v1.0_completion/pdf/page_positions.json').write_text(json.dumps(out,ensure_ascii=False,indent=2))
print(d)
