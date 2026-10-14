from pathlib import Path
import pdfplumber,json
from pypdf import PdfReader
root=Path.cwd();folder=root/'logs/v1.0.3/pdf/completion_20261014';data=json.loads((folder/'inspection.json').read_text());p=Path(data['target']);r=PdfReader(p)
def overlap(a,b):return a[0]<b[2] and a[2]>b[0] and a[1]<b[3] and a[3]>b[1]
with pdfplumber.open(p) as pdf:
 for n in [4,8,9,10,11,14,16]:
  page=pdf.pages[n-1];boxes=[[c['x0']-1,c['top']-1,c['x1']+1,c['bottom']+1] for c in page.chars if c['text'].strip()]
  for a in data['pages'][n-1]['annotations']:
   x0,y0,x1,y1=a['rect'];boxes.append([x0,page.height-y1,x1,page.height-y0])
  spaces=[]
  for width,height in [(480,20),(480,10),(170,24),(75,40)]:
   found=[]
   for y in range(42,807,2):
    for x in ([40] if width>=400 else [12,40,340,500] if width<=75 else [40,340]):
     rect=[x,y,x+width,y+height]
     if rect[2]<584 and all(not overlap(rect,b) for b in boxes):found.append((x,y))
   # compact ranges at fixed x
   print(n,width,height,found[:8],found[-8:])
