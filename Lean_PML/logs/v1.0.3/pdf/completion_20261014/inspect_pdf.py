from pathlib import Path
import json,hashlib
from pypdf import PdfReader
import pdfplumber
root=Path.cwd();folder=root/'logs/v1.0.3/pdf/completion_20261014';folder.mkdir(parents=True,exist_ok=True)
p=root.parent/'results/V7_Maxwell_Debye_PML/V7_global_energy_副本.pdf';r=PdfReader(p)
report={'target':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'page_count':len(r.pages),'annotations':sum(len(pg['/Annots']) if '/Annots' in pg else 0 for pg in r.pages),'pages':[]}
with pdfplumber.open(p) as pdf:
 for i,page in enumerate(pdf.pages,1):
  text=page.extract_text() or '';(folder/f'page_{i:02}.txt').write_text(text)
  anns=[a.get_object() for a in (r.pages[i-1]['/Annots'] if '/Annots' in r.pages[i-1] else [])]
  report['pages'].append({'page':i,'width':page.width,'height':page.height,'text':text,'annotations':[{'rect':list(map(float,a.get('/Rect',[0]*4))),'text':str(a.get('/Contents','')),'id':str(a.get('/NM',''))} for a in anns]})
(folder/'inspection.json').write_text(json.dumps(report,ensure_ascii=False,indent=2))
for q in report['pages']:
 if any(s in q['text'] for s in ['5.3','(6.7)','(6.8)','(6.9)','(6.10)','(2.4)','11.3']):
  print(q['page'],q['width'],q['height']);print(q['text'][-1800:])
