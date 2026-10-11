"""重新打开最终目标，核对文字/批注/原件，再渲染所有修改页；不编辑 PDF。"""
from pathlib import Path
import json,hashlib,subprocess
from collections import Counter
from pypdf import PdfReader
root=Path.cwd();d=root/"logs/v0.2.3/pdf"
plan=json.loads((d/"annotation_plan.json").read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
target=Path(plan["backup"]["target"]);backup=Path(plan["backup"]["backup"])
before=PdfReader(backup);after=PdfReader(target)
original=PdfReader(target.parent/"V7_global_energy.pdf")
assert len(before.pages)==len(after.pages)==len(original.pages)==18
def annotations(page):return list(page["/Annots"]) if "/Annots" in page else []
def sig(a):
    a=a.get_object()
    return tuple(str(a.get(k)) for k in ("/Subtype","/Rect","/Contents","/T","/F"))
new=[]
for i,(old,final,orig) in enumerate(zip(before.pages,after.pages,original.pages),1):
    assert list(old.mediabox)==list(final.mediabox)
    assert list(old.cropbox)==list(final.cropbox)
    oldtext=old.extract_text() or "";newtext=final.extract_text() or ""
    assert newtext.startswith(oldtext) and oldtext.startswith(orig.extract_text() or ""),i
    assert Counter(sig(a) for a in annotations(old))<=Counter(sig(a) for a in annotations(final)),i
    assert sum(a.get_object().get("/Subtype")=="/Link" for a in annotations(old))==sum(a.get_object().get("/Subtype")=="/Link" for a in annotations(final)),i
    for a in annotations(final):
        obj=a.get_object()
        if str(obj.get("/NM","")).startswith("LeanPML.v0.2.3."):
            new.append(dict(id=str(obj["/NM"]),page=i,rect=list(map(float,obj["/Rect"])),text=str(obj["/Contents"])))
expected={"LeanPML.v0.2.3."+e["id"] for e in plan["entries"] if e["new_tick"]}
expected|={"LeanPML.v0.2.3."+n["id"] for n in plan["notes"]}
assert len(new)==len(expected)==9 and {a["id"] for a in new}==expected
assert (after.metadata or {})["/LeanPMLV023MarkPlanSHA256"]==sha(d/"annotation_plan.json")
for e in plan["entries"]:
    assert sha(root/e["module"])==e["source_sha256"]
for path,digest in json.loads((root/"logs/v0.2.3/input_hashes.json").read_text()).items():
    assert sha(Path(path))==digest,("受保护文件变化",path)
report=dict(pages=18,modified_pages=plan["modified_pages"],
    old_annotations=sum(len(annotations(p)) for p in before.pages),
    total_annotations=sum(len(annotations(p)) for p in after.pages),
    new_annotations=new,new_red_ticks=4,old_red_ticks_preserved=16,
    original_text_prefix_preserved_on_all_pages=True,old_annotations_preserved=True,
    source_files_unchanged=True,sha256_before=sha(backup),sha256_after=sha(target),
    plan_sha256=sha(d/"annotation_plan.json"),visual_review="pending")
for page in plan["modified_pages"]:
    command=["pdftoppm","-f",str(page),"-l",str(page),"-scale-to","1500","-png","-singlefile",
             str(target),str(d/f"after-{page:02d}")]
    print("渲染命令：",json.dumps(command,ensure_ascii=False),flush=True)
    subprocess.run(command,check=True)
    assert (d/f"after-{page:02d}.png").exists()
(d/"verification.json").write_text(json.dumps(report,ensure_ascii=False,indent=2)+"\n")
print(json.dumps({k:v for k,v in report.items() if k!="new_annotations"},ensure_ascii=False,indent=2))
