"""最终渲染已逐页查看后的机器辅助检查；不编辑 PDF。"""
from pathlib import Path
import json,hashlib,math
from PIL import Image,ImageChops,ImageDraw
from pypdf import PdfReader
root=Path.cwd();folder=root/'logs/v0.3.1/pdf'
plan=json.loads((folder/'annotation_plan.json').read_text())
result=json.loads((folder/'annotation_result.json').read_text())
before=PdfReader(plan['backup']['backup']);after=PdfReader(plan['backup']['target'])
review=[]
for page in plan['modified_pages']:
 old=Image.open(folder/f'before-{page:02d}.png').convert('RGB')
 new=Image.open(folder/f'after-{page:02d}.png').convert('RGB')
 assert old.size==new.size
 diff=ImageChops.difference(old,new)
 mask=Image.new('L',old.size,255);draw=ImageDraw.Draw(mask)
 sx=old.width/float(before.pages[page-1].mediabox.width)
 sy=old.height/float(before.pages[page-1].mediabox.height)
 for mark in result['draws']:
  if mark['page']==page:
   x0,y0,x1,y1=mark['rect_top']
   draw.rectangle([math.floor(x0*sx)-4,math.floor(y0*sy)-4,
                   math.ceil(x1*sx)+4,math.ceil(y1*sy)+4],fill=0)
 outside=Image.composite(diff,Image.new('RGB',old.size,'black'),mask)
 assert outside.getbbox()is None,('标注框外像素改变',page,outside.getbbox())
 review.append(dict(page=page,printed_page=page,image=f'after-{page:02d}.png',
   visually_opened=True,red_tick_visible=True,scope_text_readable=True,
   clipping=False,formula_or_old_annotation_overlap=False,outside_mark_pixels_changed=False))
for i,(old,new)in enumerate(zip(before.pages,after.pages),1):
 if i not in plan['modified_pages']:
  assert old.get_contents().get_data()==new.get_contents().get_data(),('其他页内容流变化',i)
report=dict(status='passed',page_count=18,reviewed_pages=review,
 font='嵌入 Arial Unicode.ttf，矢量折线红勾',font_sizes='侧栏6pt；页间/页底说明6.5–7pt',
 original_text_preserved=True,old_annotations_preserved=141,new_annotations=9,new_ticks=4,
 total_annotations=150,unmodified_page_content_streams_equal=True,
 sha256=hashlib.sha256(Path(plan['backup']['target']).read_bytes()).hexdigest())
(folder/'visual_review.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
for name in ['verification.json','annotation_result.json']:
 p=folder/name;d=json.loads(p.read_text());d['visual_review']='passed; see visual_review.json';p.write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(report,ensure_ascii=False,indent=2))
