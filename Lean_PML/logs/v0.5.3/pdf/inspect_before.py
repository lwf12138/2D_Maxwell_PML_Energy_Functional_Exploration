from pathlib import Path
import json,hashlib
from pypdf import PdfReader
import pdfplumber
root=Path.cwd();folder=root/'logs/v0.5.3/pdf';target=(root/'../results/V7_Maxwell_Debye_PML/V7_global_energy_副本.pdf').resolve()
r=PdfReader(target)
record={'target':str(target),'sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'pages':len(r.pages),'annotations':sum(len(p['/Annots']) if '/Annots' in p else 0 for p in r.pages),'locations':[]}
with pdfplumber.open(target) as d:
 for n,p in enumerate(d.pages,1):
  for term in ['(6.7)','(6.8)','(6.9)','(6.10)','(7.5)','(7.6)','(7.7)','(7.8)','(9.5)','(9.6)','(9.7)','2.2','5.2','10','11.3']:
   hits=p.search(term,regex=False)
   if hits:record['locations'].append({'page':n,'term':term,'hits':[{k:m[k] for k in ['text','x0','x1','top','bottom']} for m in hits]})
(folder/'before_inspection.json').write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'pages':record['pages'],'annotations':record['annotations'],'sha256':record['sha256'],'formula_pages':[(e['term'],e['page']) for e in record['locations'] if e['term'].startswith('(')]},ensure_ascii=False,indent=2))
