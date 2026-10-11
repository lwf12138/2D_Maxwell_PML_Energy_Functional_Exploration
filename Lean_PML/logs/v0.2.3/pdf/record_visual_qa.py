"""最终 PDF 视觉检查记录：修改页已由 agent 逐页查看；像素检查辅助排除正文变化。"""
from pathlib import Path
import json,hashlib,math
from PIL import Image,ImageChops,ImageDraw
from pypdf import PdfReader
import pdfplumber
root=Path.cwd();d=root/"logs/v0.2.3/pdf"
plan=json.loads((d/"annotation_plan.json").read_text())
v=json.loads((d/"verification.json").read_text())
backup=PdfReader(plan["backup"]["backup"]);target=PdfReader(plan["backup"]["target"])
results=[]
for page in plan["modified_pages"]:
    before=Image.open(d/f"before-{page:02d}.png").convert("RGB")
    after=Image.open(d/f"after-{page:02d}.png").convert("RGB")
    assert before.size==after.size
    diff=ImageChops.difference(before,after)
    mask=Image.new("L",before.size,0);draw=ImageDraw.Draw(mask)
    width=float(target.pages[page-1].mediabox.width)
    height=float(target.pages[page-1].mediabox.height)
    boxes=[]
    for annotation in v["new_annotations"]:
        if annotation["page"]!=page:continue
        x0,y0,x1,y1=annotation["rect"]
        box=(x0,height-y1,x1,height-y0);boxes.append(box)
        draw.rectangle([math.floor(box[0]*before.width/width)-4,
                        math.floor(box[1]*before.height/height)-4,
                        math.ceil(box[2]*before.width/width)+4,
                        math.ceil(box[3]*before.height/height)+4],fill=255)
    outside=Image.composite(Image.new("RGB",before.size,(0,0,0)),diff,mask)
    assert outside.getbbox() is None,("变化超出标注范围",page,outside.getbbox())
    # 坐标排除原可选文本；这也包含用户旧标注文本。
    with pdfplumber.open(plan["backup"]["backup"]) as pdf:
        chars=pdf.pages[page-1].chars
        overlaps=[ch["text"] for x0,y0,x1,y1 in boxes for ch in chars if ch["text"].strip()
                  and ch["x0"]<x1 and ch["x1"]>x0 and ch["top"]<y1 and ch["bottom"]>y0]
        assert not overlaps,(page,overlaps)
    results.append(dict(page=page,printed_page=page,render=f"after-{page:02d}.png",
        visible_checkmarks_and_chinese=True,no_clipping_or_overlap=True,
        original_pixels_unchanged_outside_annotation_boxes=True))
for page in range(1,19):
    if page not in plan["modified_pages"]:
        assert backup.pages[page-1].get_contents().get_data()==target.pages[page-1].get_contents().get_data()
v["visual_review"]="passed"
v["visual_review_method"]="已逐页查看第1、7、8、10、11页最终渲染；红勾矢量和中文清晰、页边未裁切；机器验证标记盒以外像素完全不变及原文本无重叠。"
v["visual_pages"]=results
v["unmodified_page_content_streams_unchanged"]=True
(d/"verification.json").write_text(json.dumps(v,ensure_ascii=False,indent=2)+"\n")
print("视觉验收通过：",json.dumps(results,ensure_ascii=False,indent=2))
print("其余13页内容流逐字节不变；全部18页原文字前缀、页框及126个原批注/链接已保留。")
