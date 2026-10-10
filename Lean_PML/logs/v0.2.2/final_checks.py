"""v0.2.2 交付核对；不修改受保护来源，只写本阶段验收哈希。"""
from pathlib import Path
import hashlib,json,re,subprocess

root=Path.cwd()
stage=root/"logs/v0.2.2"
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
protected=json.loads((stage/"input_hashes.json").read_text())
changed=[name for name,digest in protected.items() if sha(Path(name))!=digest]
assert not changed, changed
print(f"受保护的来源、旧代码、历史日志及配置：{len(protected)} 项字节未变。")
old_progress=(stage/"before_PROGRESS.md").read_text()
progress=(root/"PROGRESS.md").read_text()
assert progress.endswith(old_progress)
assert (root/"Audit.lean").read_bytes().startswith((stage/"before_Audit.lean").read_bytes())
print("旧 PROGRESS 全文和旧 Audit 审计保持原样。")

def strip_comments(text):
    out=[];i=0;depth=0
    while i<len(text):
        if text[i:i+2]=="/-": depth+=1;i+=2
        elif depth and text[i:i+2]=="-/": depth-=1;i+=2
        elif depth: i+=1
        elif text[i:i+2]=="--":
            end=text.find("\n",i);i=len(text) if end<0 else end
        else: out.append(text[i]);i+=1
    assert depth==0
    return "".join(out)

modules=sorted((root/"LeanPML").rglob("*.lean"))
assert len(modules)==10
formal=modules+[root/"LeanPML.lean",root/"Audit.lean"]
all_theorems=[]
for p in modules:
    code=strip_comments(p.read_text())
    namespace=re.search(r"^namespace (\S+)",code,re.M).group(1)
    all_theorems.extend(namespace+"."+name for name in re.findall(r"^theorem (\w+)",code,re.M))
for p in formal:
    code=strip_comments(p.read_text())
    assert not re.search(r"\b(sorry|admit|axiom|sorryAx)\b",code),p
    artifact=root/".lake/build/lib/lean"/p.relative_to(root).with_suffix(".olean")
    assert artifact.exists(),artifact
imports=re.findall(r"^import (LeanPML\.\S+)",(root/"LeanPML.lean").read_text(),re.M)
assert set(imports)=={str(p.relative_to(root).with_suffix("")).replace("/",".") for p in modules}
audit_names=re.findall(r"^#print axioms (\S+)",strip_comments((root/"Audit.lean").read_text()),re.M)
assert len(audit_names)==len(set(audit_names))==109
assert set(audit_names)==set(all_theorems)
config={"defaultTargets":json.loads(re.search(r"^defaultTargets\s*=\s*(\[.*\])", (root/"lakefile.toml").read_text(),re.M).group(1))}
assert set(config["defaultTargets"])=={"LeanPML","Audit"}
print("10 个正式模块及两个入口均有 olean；109 条正式定理逐项进入公理审计。")
print("正式源码无 sorry/admit/custom axiom；默认目标为 LeanPML、Audit。")

build_stem="20261010T185648_883655_lake_build"
audit_stem="20261010T185707_307274_axioms_audit"
for stem in [build_stem,audit_stem]:
    meta=json.loads((stage/(stem+".json")).read_text())
    assert meta["exit_code"]==0 and meta["status"]=="finished"
    assert meta["cwd"]==str(root)
build=(stage/(build_stem+".log")).read_text()
assert "Build completed successfully (2121 jobs)." in build
assert "warning:" not in build and "error:" not in build
audit=(stage/(audit_stem+".log")).read_text()
entries=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",audit)
assert len(entries)==109 and {x[0] for x in entries}==set(audit_names)
used_axioms={a.strip() for _,axioms in entries for a in axioms.split(",") if a.strip()}
assert used_axioms=={"propext","Classical.choice","Quot.sound"},used_axioms
assert "sorryAx" not in audit
print("实际默认构建/独立审计均退出 0；无编译警告；标准公理依赖："+", ".join(sorted(used_axioms)))

new_paths=[root/"LeanPML/PML/LocalElectric.lean",root/"LeanPML/PML/LocalDebye.lean"]
new_defs=sum(len(re.findall(r"^noncomputable def ",p.read_text(),re.M)) for p in new_paths)
new_thms=sum(len(re.findall(r"^theorem ",p.read_text(),re.M)) for p in new_paths)
assert (new_defs,new_thms)==(9,18)
debye=(root/"LeanPML/PML/LocalDebye.lean").read_text()
fragment=(stage/"coeff_bounds_fragment.txt").read_text()
assert fragment in debye
for name,code in [
    ("electric_rate_identity",new_paths[0].read_text()),
    ("polar_rate_algebra",debye),
    ("polarQuadratic_eq_reduced",debye),
    ("polar_coefficients_bounds_of_local_conditions",debye),
]:
    assert len(re.findall(r"\b"+name+r"\b",strip_comments(code)))>=2,name
assert not (root/"LeanPML/PML/LocalSpatial.lean").exists()
print("新增 9 个定义、18 条定理；系数片段完整进入正式模块，代数辅助有调用者；未建 v0.2.3 模块。")

manifest=json.loads((root/"lake-manifest.json").read_text())
assert len(manifest["packages"])==9
for package in manifest["packages"]:
    repo=root/".lake/packages"/package["name"]
    head=subprocess.check_output(["git","-C",str(repo),"rev-parse","HEAD"],text=True).strip()
    assert head==package["rev"],package["name"]
mathlib=next(p for p in manifest["packages"] if p["name"]=="mathlib")
assert mathlib["rev"]=="fabf563a7c95a166b8d7b6efca11c8b4dc9d911f"
assert (root/"lean-toolchain").read_text().strip()=="leanprover/lean4:v4.31.0"
print("9 个依赖检出提交均与 manifest 一致；Lean/mathlib 固定版本未变。")

documents=[root/"README.md",root/"PROGRESS.md",root/"docs/v0.2.2_reading_guide.md"]
for p in documents:
    text=p.read_text()
    if p.name=="PROGRESS.md":text=text[:-len(old_progress)]
    assert "\ufffd" not in text,p
    assert len(re.findall(r"(?<!\\)\$\$",text))%2==0,p
    # 移除 fenced code 和显示数学后，行内美元分隔必须成对。
    without_code=re.sub(r"(?ms)^~~~.*?^~~~\s*$","",text)
    assert len(re.findall(r"(?<!\\)\$",without_code))%2==0,p
    for target in re.findall(r"\]\(([^)]+)\)",text):
        target=target.strip("<>")
        if "://" in target or target.startswith("#"):continue
        file_part=target.split("#")[0]
        file_part=re.sub(r":\d+$","",file_part)
        assert (p.parent/file_part).exists(),(p.name,target)
print("新增文档的本地链接、数学分隔与 UTF-8 内容检查通过。")
guide=root/"docs/v0.2.2_reading_guide.md"
source_rows=0
for line in guide.read_text().splitlines():
    if "| [" not in line or "../.lake/" not in line:continue
    name=line.split("|")[1].strip()
    target=re.search(r"\]\(([^)]+)\)",line).group(1)
    filepath,number=target.rsplit(":",1)
    actual=(guide.parent/filepath).read_text().splitlines()[int(number)-1]
    assert name.split(".")[-1] in actual,(name,actual)
    source_rows+=1
assert source_rows==19
print("指南列出的 19 个 mathlib 声明名称及准确源码行均已核对。")


# 本机 VS Code Lean 扩展确有文档所列的两个命令。
extension=json.loads(Path("/Users/wcli/.vscode/extensions/leanprover.lean4-0.0.237/package.json").read_text())
commands=extension["contributes"]["commands"]
chosen=[c for c in commands if "Display Goal" in c.get("title","") or "Restart File" in c.get("title","")]
assert len(chosen)==2,chosen
print("VS Code 命令核验："+json.dumps(chosen,ensure_ascii=False))
artifacts=formal+[root/"README.md",root/"docs/v0.2.2_reading_guide.md",
                  root/"lean-toolchain",root/"lakefile.toml",root/"lake-manifest.json",
                  root/"scripts/run_logged.py"]
(stage/"verified_artifact_hashes.json").write_text(json.dumps(
    {str(p.relative_to(root)):sha(p) for p in artifacts},ensure_ascii=False,indent=2)+"\n")
print("已保存已验证交付文件哈希；PROGRESS 最终验收登记不纳入此表。")
