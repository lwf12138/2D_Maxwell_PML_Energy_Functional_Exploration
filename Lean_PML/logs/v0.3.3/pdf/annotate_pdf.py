"""添加 v0.3.3 矢量红勾与可选中文说明；只写指定 PDF 副本。
从已保存备份叠加，验证当前哈希后原子替换；同一计划重跑直接跳过，避免重复标记。
"""
from pathlib import Path
import io,json,hashlib,os
from collections import Counter
from pypdf import PdfReader,PdfWriter
from pypdf.generic import DictionaryObject,NameObject,ArrayObject,NumberObject,FloatObject,TextStringObject,RectangleObject
import pdfplumber
from reportlab.pdfgen import canvas
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
def annots(page):
    return list(page["/Annots"]) if "/Annots" in page else []
root=Path.cwd(); folder=root/"logs/v0.3.3/pdf"
plan_path=folder/"annotation_plan.json"
plan=json.loads(plan_path.read_text())
plan_hash=hashlib.sha256(plan_path.read_bytes()).hexdigest()
target=Path(plan["backup"]["target"]); backup=Path(plan["backup"]["backup"])
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for stem in (plan["build"],plan["audit"]):
    meta=json.loads((root/"logs/v0.3.3"/(stem+".json")).read_text())
    assert meta["exit_code"]==0 and meta["status"]=="finished"
for entry in plan["entries"]:
    assert sha(root/entry["module"])==entry["source_sha256"],entry["module"]
current=PdfReader(target)
if (current.metadata or {}).get("/LeanPMLV033MarkPlanSHA256")==plan_hash:
    expected={"LeanPML.v0.3.3."+e["id"] for e in plan["entries"] if e["new_tick"]}
    expected|={"LeanPML.v0.3.3."+n["id"] for n in plan["notes"]}
    found={str(a.get_object().get("/NM","")) for p in current.pages for a in annots(p)}
    assert expected<=found
    print("当前 PDF 已包含完全相同的计划和稳定标记 ID；未重复叠加。")
    raise SystemExit(0)
assert sha(target)==plan["backup"]["sha256_before"],"目标已发生外部变化；停止以保护后续批注"
assert sha(backup)==plan["backup"]["sha256_before"]
reader=PdfReader(backup)
assert len(reader.pages)==18
pdfmetrics.registerFont(TTFont("LeanPMLChinese",plan["font"],subfontIndex=0))
draws=[]
for e in plan["entries"]:
    if e["new_tick"]:
        d=dict(e["draw"]);d.update(id=e["id"],page=e["page"],tick=True,
            scope=e["location"]+"\n"+e["scope"]+"\n待完成："+e["missing"]+
            "\n\n"+"\n".join(e["theorems"])+"\n\n当前证据：\n"+e["build_log"]+"\n"+e["audit_log"])
        draws.append(d)
for note in plan["notes"]:
    d=dict(note);d.update(tick=False,scope="\n".join(note["lines"]))
    if "entry" in note:
        entry=next(e for e in plan["entries"] if e["id"]==note["entry"])
        d["scope"]+="\n原标记保留。限定范围："+entry["scope"]+"\n待完成："+entry["missing"]
    draws.append(d)
# 所有范围盒使用页面顶端坐标，实际写入时转换为 PDF 的底部坐标。
for d in draws:
    size=d["font_size"];leading=size+2.2;tx=d["x"]+15 if d["tick"] else d["x"]
    width=max(pdfmetrics.stringWidth(s,"LeanPMLChinese",size) for s in d["lines"])
    d["rect_top"]=[d["x"]-1,d["top"]-2,tx+width+1,d["top"]+size+(len(d["lines"])-1)*leading+2]
    w,h=map(float,reader.pages[d["page"]-1].mediabox[2:])
    x0,y0,x1,y1=d["rect_top"]
    assert 0<=x0<x1<w and 0<=y0<y1<h,(d["id"],d["rect_top"])
    assert all(ord(c) in pdfmetrics.getFont("LeanPMLChinese").face.charToGlyph for line in d["lines"] for c in line)
# 先证明标注矩形没有遮住原可选文本（包含已有标注文字）。
with pdfplumber.open(backup) as pdf:
    for d in draws:
        x0,y0,x1,y1=d["rect_top"]
        overlap=[c["text"] for c in pdf.pages[d["page"]-1].chars
                 if c["x0"]<x1 and c["x1"]>x0 and c["top"]<y1 and c["bottom"]>y0
                 and c["text"].strip()]
        assert not overlap,(d["id"],"覆盖已有文字",overlap)
writer=PdfWriter()
writer.clone_document_from_reader(reader)
for number in plan["modified_pages"]:
    page=writer.pages[number-1];w=float(page.mediabox.width);h=float(page.mediabox.height)
    stream=io.BytesIO()
    can=canvas.Canvas(stream,pagesize=(w,h),pageCompression=1)
    can.setFillColorRGB(.84,.08,.10);can.setStrokeColorRGB(.84,.08,.10)
    for d in [d for d in draws if d["page"]==number]:
        size=d["font_size"];x=d["x"];top=d["top"]
        if d["tick"]:
            # 矢量两段折线，不依赖勾号字体。
            path=can.beginPath();path.moveTo(x,h-top-6)
            path.lineTo(x+4,h-top-10);path.lineTo(x+11,h-top-1)
            can.setLineWidth(1.55);can.setLineCap(1);can.setLineJoin(1);can.drawPath(path)
            x+=15
        can.setFont("LeanPMLChinese",size)
        for i,line in enumerate(d["lines"]):
            can.drawString(x,h-top-size-i*(size+2.2),line)
    can.save();stream.seek(0)
    page.merge_page(PdfReader(stream).pages[0])
    for d in [d for d in draws if d["page"]==number]:
        x0,y0,x1,y1=d["rect_top"]
        annot=DictionaryObject({
            NameObject("/Type"):NameObject("/Annot"),NameObject("/Subtype"):NameObject("/Square"),
            NameObject("/Rect"):RectangleObject([x0,h-y1,x1,h-y0]),
            NameObject("/BS"):DictionaryObject({NameObject("/W"):NumberObject(0)}),
            NameObject("/Border"):ArrayObject([NumberObject(0)]*3),
            NameObject("/C"):ArrayObject([FloatObject(.84),FloatObject(.08),FloatObject(.10)]),
            NameObject("/T"):TextStringObject("LeanPML v0.3.3 已验证范围" if d["tick"] else "LeanPML v0.3.3 范围说明"),
            NameObject("/Contents"):TextStringObject(d["scope"]),
            NameObject("/NM"):TextStringObject("LeanPML.v0.3.3."+d["id"]),
            NameObject("/F"):NumberObject(4)})
        writer.add_annotation(number-1,annot)
writer.add_metadata({"/LeanPMLV033MarkPlanSHA256":plan_hash,
                     "/LeanPMLV033Evidence":plan["build"]+"; "+plan["audit"]})
tmp=folder/"annotated_v0.3.3_candidate.pdf"
with tmp.open("wb") as file: writer.write(file)
after=PdfReader(tmp)
assert len(after.pages)==len(reader.pages)==18
def old_annotation_signature(a):
    obj=a.get_object()
    return (str(obj.get("/Subtype")),str(obj.get("/Rect")),str(obj.get("/Contents")),
            str(obj.get("/T")),str(obj.get("/F")))
for i,(old,new) in enumerate(zip(reader.pages,after.pages),1):
    assert list(old.mediabox)==list(new.mediabox) and list(old.cropbox)==list(new.cropbox),i
    assert (new.extract_text() or "").startswith(old.extract_text() or ""),("原文本变化",i)
    originals=Counter(old_annotation_signature(a) for a in annots(old))
    final=Counter(old_annotation_signature(a) for a in annots(new))
    assert originals<=final,("原批注丢失",i)
os.replace(tmp,target)
report=dict(pages=18,old_annotations=sum(len(p["/Annots"]) if "/Annots" in p else 0 for p in reader.pages),
    new_annotations=len(draws),new_red_ticks=sum(e["new_tick"] for e in plan["entries"]),modified_pages=plan["modified_pages"],
    unchanged_original_text_prefix=True,old_annotations_preserved=True,
    old_text_overlap_count=0,sha256_before=sha(backup),sha256_after=sha(target),
    plan_sha256=plan_hash,draws=draws,visual_review="pending")
(folder/"annotation_result.json").write_text(json.dumps(report,ensure_ascii=False,indent=2)+"\n")
print(json.dumps({k:v for k,v in report.items() if k!="draws"},ensure_ascii=False,indent=2))
print("目标副本已重新打开验证；下一步必须渲染全部修改页并逐页检查。")
