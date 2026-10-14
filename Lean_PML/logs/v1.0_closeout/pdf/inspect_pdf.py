from pathlib import Path
import pdfplumber,json,hashlib
from pypdf import PdfReader
p=Path('../results/V7_Maxwell_Debye_PML/V7_global_energy_副本.pdf');r=PdfReader(p)
def anns(q):return list(q['/Annots']) if '/Annots' in q else []
d={'target':str(p.resolve()),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'page_count':len(r.pages),'annotations':sum(len(anns(q)) for q in r.pages)}
folder=Path('logs/v1.0_closeout/pdf');(folder/'inspection.json').write_text(json.dumps(d,ensure_ascii=False,indent=2))
with pdfplumber.open(p) as pdf:
 for i,q in enumerate(pdf.pages,1):
  text=q.extract_text() or ''
  (folder/f'page_{i}_text.txt').write_text(text)
  if i in [4,8,9,10,12,13,14]:print(i,q.width,q.height,text[:100],text[-150:])
print(d)
