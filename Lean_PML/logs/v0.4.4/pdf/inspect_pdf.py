from pathlib import Path
import json,hashlib
from pypdf import PdfReader
import pdfplumber
p=Path.cwd();folder=p/'logs/v0.4.4/pdf';target=(p/'../results/V7_Maxwell_Debye_PML/V7_global_energy_副本.pdf').resolve()
r=PdfReader(target);anns=lambda page:list(page['/Annots'])if'/Annots'in page else []
report={'target':str(target),'sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'pages':len(r.pages),'annotations':[]}
for i,page in enumerate(r.pages,1):
 for a in anns(page):
  obj=a.get_object();report['annotations'].append({'page':i,**{k:str(obj.get(k,''))for k in ['/NM','/Subtype','/Rect','/Contents']}})
(folder/'read_only_inspection.json').write_text(json.dumps(report,ensure_ascii=False,indent=2))
with pdfplumber.open(target)as pdf:
 for number in range(1, len(pdf.pages)+1):
  page=pdf.pages[number-1]
  (folder/f'page-{number}-text.txt').write_text(page.extract_text(layout=True))
  (folder/f'page-{number}-chars.json').write_text(json.dumps([{k:c[k]for k in ['text','x0','x1','top','bottom']}for c in page.chars],ensure_ascii=False))
print(json.dumps({'pages':report['pages'],'annotations':len(report['annotations']),'sha256':report['sha256']},indent=2))
