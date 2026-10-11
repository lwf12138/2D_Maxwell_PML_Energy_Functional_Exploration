"""v0.2.3 最终交付核对：已有来源和历史不变，构建/审计/文档/PDF 证据一致。"""
from pathlib import Path
import hashlib,json,re,subprocess
from pypdf import PdfReader
root=Path.cwd();stage=root/"logs/v0.2.3"
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
protected=json.loads((stage/"input_hashes.json").read_text())
changed=[name for name,digest in protected.items() if sha(Path(name))!=digest]
assert not changed,changed
print(f"{len(protected)} 项来源、旧源码、历史日志、配置与旧 PDF 备份字节未变。")
old_progress=(stage/"before_PROGRESS.md").read_text()
assert (root/"PROGRESS.md").read_text().endswith(old_progress)
assert (root/"Audit.lean").read_bytes().startswith((stage/"before_Audit.lean").read_bytes())
print("旧 PROGRESS 全文与旧 Audit 109 条审计原样保留。")
def strip_comments(text):
    out=[];i=0;depth=0
    while i<len(text):
        if text[i:i+2]=="/-":depth+=1;i+=2
        elif depth and text[i:i+2]=="-/":depth-=1;i+=2
        elif depth:i+=1
        elif text[i:i+2]=="--":
            end=text.find("\n",i);i=len(text) if end<0 else end
        else:out.append(text[i]);i+=1
    assert depth==0
    return "".join(out)
modules=sorted((root/"LeanPML").rglob("*.lean"))
assert len(modules)==11
formal=modules+[root/"LeanPML.lean",root/"Audit.lean"]
all_theorems=[]
for p in modules:
    code=strip_comments(p.read_text())
    ns=re.search(r"^namespace (\S+)",code,re.M).group(1)
    all_theorems.extend(ns+"."+name for name in re.findall(r"^theorem (\w+)",code,re.M))
for p in formal:
    assert not re.search(r"\b(sorry|admit|axiom|sorryAx)\b",strip_comments(p.read_text())),p
    artifact=root/".lake/build/lib/lean"/p.relative_to(root).with_suffix(".olean")
    assert artifact.exists(),artifact
    assert artifact.stat().st_mtime>=p.stat().st_mtime,p
imports=re.findall(r"^import (LeanPML\.\S+)",(root/"LeanPML.lean").read_text(),re.M)
assert set(imports)=={str(p.relative_to(root).with_suffix("")).replace("/",".") for p in modules}
audit_names=re.findall(r"^#print axioms (\S+)",strip_comments((root/"Audit.lean").read_text()),re.M)
assert len(audit_names)==len(set(audit_names))==134
assert set(audit_names)==set(all_theorems)
targets=json.loads(re.search(r"^defaultTargets\s*=\s*(\[.*\])",(root/"lakefile.toml").read_text(),re.M).group(1))
assert set(targets)=={"LeanPML","Audit"}
print("11 个模块与两个入口构建产物均新于源码；134 条正式定理完整进入默认构建和审计。")
print("正式源码没有 sorry、admit、自定义 axiom 或 sorryAx。")
build_stem="20261010T232910_472603_lake_build_retry"
audit_stem="20261010T232931_121820_axioms_audit_retry"
for stem in [build_stem,audit_stem]:
    meta=json.loads((stage/(stem+".json")).read_text())
    assert meta["exit_code"]==0 and meta["status"]=="finished" and meta["cwd"]==str(root)
build=(stage/(build_stem+".log")).read_text()
assert "Build completed successfully (2122 jobs)." in build
assert "warning:" not in build and "error:" not in build
entries=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",(stage/(audit_stem+".log")).read_text())
assert len(entries)==134 and {e[0] for e in entries}==set(audit_names)
axioms={a.strip() for _,ax in entries for a in ax.split(",") if a.strip()}
assert axioms=={"propext","Classical.choice","Quot.sound"}
print("默认构建与独立审计均退出0，无最终编译警告；仅依赖标准 propext、Classical.choice、Quot.sound。")
spatial=root/"LeanPML/PML/LocalSpatial.lean";code=strip_comments(spatial.read_text())
assert len(re.findall(r"^(?:noncomputable )?def ",code,re.M))==6
assert len(re.findall(r"^theorem ",code,re.M))==25
fragment=(stage/"spatial_examples_fragment.txt").read_text()
assert fragment in spatial.read_text()
for name in ["spatial_weight_balance","spatial_rate_identity","hasDerivAt_spatialAuxiliary",
             "energyWeightX_swap","spatialEnergy2D_eq_sum","spatialDissipation2D_of_sum_zero"]:
    assert len(re.findall(r"\b"+name+r"\b",code))>=2,name
assert "energyWeightY c p r" in code
assert not (root/"LeanPML/PML/Obstructions/SingleLayer.lean").exists()
assert not (root/"docs/single_layer_failure.md").exists()
print("新增6定义、25定理；代数辅助有真实调用者，四区域和两条非零路径进入正式源码；未实现v0.2.4。")
manifest=json.loads((root/"lake-manifest.json").read_text())
assert len(manifest["packages"])==9
for package in manifest["packages"]:
    actual=subprocess.check_output(["git","-C",str(root/".lake/packages"/package["name"]),"rev-parse","HEAD"],text=True).strip()
    assert actual==package["rev"],package["name"]
assert (root/"lean-toolchain").read_text().strip()=="leanprover/lean4:v4.31.0"
assert next(p for p in manifest["packages"] if p["name"]=="mathlib")["rev"]=="fabf563a7c95a166b8d7b6efca11c8b4dc9d911f"
print("固定工具链与9个依赖解析提交均未变。")
documents=[root/"README.md",root/"PROGRESS.md",root/"docs/v0.2.3_reading_guide.md",root/"docs/pdf_formalization_marks.md"]
for p in documents:
    text=p.read_text()
    if p.name=="PROGRESS.md":text=text[:-len(old_progress)]
    assert "\ufffd" not in text,p
    without_code=re.sub(r"(?ms)^~~~.*?^~~~\s*$","",text)
    assert len(re.findall(r"(?<!\\)\$\$",without_code))%2==0,p
    assert len(re.findall(r"(?<!\\)\$",without_code))%2==0,p
    prose=re.sub(r"\$\$.*?\$\$","",without_code,flags=re.S)
    prose=re.sub(r"\$[^\n$]*\$","",prose)
    for target in re.findall(r"\]\(([^)]+)\)",prose):
        target=target.strip("<>")
        if "://" in target or target.startswith("#"):continue
        filepart=re.sub(r":\d+$","",target.split("#")[0])
        assert (p.parent/filepart).exists(),(p.name,target)
print("README、当前进度、阅读指南、PDF账本：本地链接、UTF-8及数学分隔检查通过。")
guide=root/"docs/v0.2.3_reading_guide.md";source_rows=0
for line in guide.read_text().splitlines():
    if "| [" not in line or "../.lake/" not in line:continue
    name=line.split("|")[1].strip().strip(chr(96))
    target=re.search(r"\]\(([^)]+)\)",line).group(1)
    path,number=target.rsplit(":",1)
    actual=(guide.parent/path).read_text().splitlines()[int(number)-1]
    assert name.split(".")[-1] in actual,(name,actual)
    source_rows+=1
assert source_rows==12,source_rows
extension=json.loads(Path("/Users/wcli/.vscode/extensions/leanprover.lean4-0.0.237/package.json").read_text())
commands=extension["contributes"]["commands"]
assert len([c for c in commands if "Display Goal" in c.get("title","") or "Restart File" in c.get("title","")])==2
print("指南的12项mathlib名称/源码行及本机InfoView、Restart File命令均已核对。")
plan=json.loads((stage/"pdf/annotation_plan.json").read_text())
verification=json.loads((stage/"pdf/verification.json").read_text())
target=Path(plan["backup"]["target"])
assert sha(target)==verification["sha256_after"]
assert sha(Path(plan["backup"]["backup"]))==plan["backup"]["sha256_before"]
assert verification["visual_review"]=="passed" and verification["modified_pages"]==[1,7,8,10,11]
assert verification["pages"]==18 and verification["old_annotations"]==126 and verification["total_annotations"]==135
reader=PdfReader(target)
assert len(reader.pages)==18
new_ids=[str(a.get_object().get("/NM","")) for p in reader.pages for a in (p["/Annots"] if "/Annots" in p else []) if str(a.get_object().get("/NM","")).startswith("LeanPML.v0.2.3.")]
assert len(new_ids)==len(set(new_ids))==9
ledger=(root/"docs/pdf_formalization_marks.md").read_text()
assert len(plan["entries"])==20 and sum(e["new_tick"] for e in plan["entries"])==4
for e in plan["entries"]:
    assert e["id"] in ledger and all(n in ledger and n in audit_names for n in e["theorems"]),e["id"]
    assert sha(root/e["module"])==e["source_sha256"]
for page in plan["modified_pages"]:
    assert (stage/f"pdf/after-{page:02d}.png").exists()
print("PDF与账本、源码及当前审计逐项对应：保留16旧勾，新增4个有限范围红勾和5处说明；5个修改页视觉检查通过。")
artifacts=formal+documents[:1]+documents[2:]+[root/"lean-toolchain",root/"lakefile.toml",root/"lake-manifest.json",root/"scripts/run_logged.py",target,
    stage/"pdf/annotation_plan.json",stage/"pdf/verification.json"]
(stage/"verified_artifact_hashes.json").write_text(json.dumps({str(p.relative_to(root)) if p.is_relative_to(root) else str(p):sha(p) for p in artifacts},ensure_ascii=False,indent=2)+"\n")
print("交付源码、文档、配置、PDF与证据哈希已保存；PROGRESS最后完成登记不计入哈希。")
