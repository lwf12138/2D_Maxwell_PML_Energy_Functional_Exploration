from pathlib import Path
import json,hashlib
from pypdf import PdfReader
import pdfplumber
r=Path.cwd();target=(r/'../results/V7_Maxwell_Debye_PML/V7_global_energy_副本.pdf').resolve();pdf=PdfReader(target)
record={'target':str(target),'sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'pages':len(pdf.pages),'annotations':sum((len(p['/Annots']) if '/Annots' in p else 0) for p in pdf.pages),'locations':[]}
with pdfplumber.open(target) as doc:
 for i,p in enumerate(doc.pages,1):
  text=p.extract_text() or ''
  for phrase in ['(2.1)','(2.6)','(5.1)','(5.3)','(6.6)','(10.1)','(10.2)']:
   if phrase in text:
    record['locations'].append({'page':i,'formula':phrase,'matches':[{k:m[k] for k in ['text','x0','top','x1','bottom']} for m in p.search(phrase,regex=False)]})
Path('logs/v0.4_alignment/pdf/before_inspection.json').write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n');print(json.dumps(record,ensure_ascii=False,indent=2))
