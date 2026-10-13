from pathlib import Path
import json,hashlib,subprocess
from pypdf import PdfReader
import pdfplumber
root=Path.cwd();folder=root/'logs/v0.3.1/pdf'
target=root.parent/'results/V7_Maxwell_Debye_PML/V7_global_energy_副本.pdf'
reader=PdfReader(target)
def annots(p):
 return list(p['/Annots']) if '/Annots' in p else []
rows=[]
for i,page in enumerate(reader.pages,1):
 rows.append(dict(page=i,mediabox=list(map(float,page.mediabox)),annotation_count=len(annots(page)),annotations=[{k:str(a.get_object().get(k,'')) for k in ('/Subtype','/Rect','/Contents','/T','/NM')}for a in annots(page)]))
for i in [8,9,10,11,12]:
 (folder/f'before_page_{i:02d}.txt').write_text(reader.pages[i-1].extract_text()or'')
out=dict(sha256=hashlib.sha256(target.read_bytes()).hexdigest(),page_count=len(reader.pages),annotation_count=sum(len(annots(p))for p in reader.pages),pages=rows,metadata={k:str(v) for k,v in (reader.metadata or {}).items()})
(folder/'read_only_inspection.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
with pdfplumber.open(target) as pdf:
 for i in [8,9,10,11,12]:
  page=pdf.pages[i-1]
  (folder/f'page_{i:02d}_chars.json').write_text(json.dumps([{k:c[k] for k in ('text','x0','top','x1','bottom')}for c in page.chars],ensure_ascii=False,indent=2))
  cmd=['/Users/wcli/.cache/codex-runtimes/codex-primary-runtime/dependencies/bin/override/pdftoppm','-f',str(i),'-l',str(i),'-scale-to','1800','-png','-singlefile',str(target),str(folder/f'before-{i:02d}')]
  print('渲染：',json.dumps(cmd,ensure_ascii=False),flush=True);subprocess.run(cmd,check=True)
print(json.dumps({k:v for k,v in out.items() if k not in ('pages','metadata')},ensure_ascii=False))
