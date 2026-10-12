
"""在真实构建/审计成功后，建立 v0.2.4 标注证据、独占备份和定位计划。"""
from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import hashlib,json,re,shutil
from pypdf import PdfReader
root=Path.cwd();d=root/"logs/v0.2.4/pdf"
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
build="20261011T231924_138774_lake_build"
audit="20261011T231954_467990_axioms_audit"
for stem in [build,audit]:
 meta=json.loads((root/"logs/v0.2.4"/(stem+".json")).read_text())
 assert meta["exit_code"]==0 and meta["status"]=="finished"
audit_text=(root/"logs/v0.2.4"/(audit+".log")).read_text()
audited={name:set(a.strip() for a in deps.split(",") if a.strip()) for name,deps in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",audit_text)}
assert len(audited)==154 and all(v<= {"propext","Classical.choice","Quot.sound"} for v in audited.values())
assert "sorryAx" not in audit_text
legacy=json.loads((root/"logs/v0.2.3/pdf/annotation_plan.json").read_text())
for e in legacy["entries"]:
 assert set(e["theorems"])<=audited.keys(),("旧勾无当前审计",e["id"])
old_inspection=json.loads((d/"read_only_inspection.json").read_text())
target=Path(old_inspection["target"])
assert sha(target)==old_inspection["hashes"][str(target)]
if (d/"backup.json").exists():
 backup_record=json.loads((d/"backup.json").read_text())
 backup=Path(backup_record["backup"])
 assert sha(backup)==sha(target)==backup_record["sha256_before"]
else:
 stamp=datetime.now(ZoneInfo("Asia/Shanghai")).strftime("%Y%m%dT%H%M%S")
 backup=d/f"before_v0.2.4_{stamp}.pdf"
 assert not backup.exists()
 with backup.open("xb") as f: f.write(target.read_bytes())
 backup_record={"target":str(target),"backup":str(backup),"sha256_before":sha(target),"bytes_before":target.stat().st_size}
 (d/"backup.json").write_text(json.dumps(backup_record,ensure_ascii=False,indent=2)+"\n")
source="LeanPML/PML/Obstructions/SingleLayer.lean"; prefix="LeanPML.PML.Obstructions."
root_import=(root/"LeanPML.lean").read_text()
assert "import LeanPML.PML.Obstructions.SingleLayer" in root_import
module_text=(root/source).read_text();audit_source=(root/"Audit.lean").read_text()
data=[
("initial-compatibility", "§11.1 未编号初值行：仅对应初始兼容关系", "点态代数",
 ["initial_compatibility"],
 "u₀=0、P₀=κξ、q₀=−τκξ、原辅助量与φ₀为零，ξ非零处p=r=0时，五个初始不变量的数值为零。只标兼容的代数核验，初值选择本身不算证明。",
 "磁不变量的时间保持、真实梯度/提升、完整兼容函数空间成员资格仍待完成。",
 {"x":535,"top":654,"font_size":6.0,"lines":["初始兼容","已核验","仅点态数值"]}),
("initial-density", "§11.1 未编号负耗散公式：点态初值密度", "点态代数",
 ["initialDissipation_eq","initialDissipation_nonpos","initialDissipation_neg"],
 "三个旧块直接组合，κ≠0及ξ≠0处p=r=0推出D_initial(ξ)=−μc(ε+κ)ξ²；材料及c正性推出非正，ξ≠0时严格负。",
 "不是一条已存在的完整PDE解；完整空间能量律、初始解存在性未完成。",
 {"x":535,"top":703,"font_size":6.0,"lines":["点态初值代数","材料正性"]}),
("initial-integral", "§11.1 未编号负耗散公式：实际特殊初值积分", "实际积分",
 ["initialDissipation_integral","initialDissipation_integral_neg","initialDissipation_rectangle_integral"],
 "实际测度m和函数f,p,r，平方可积与几乎处处支撑条件推出密度可积及∫D_initial=−μc(ε+κ)∫f²；包含全开矩形的二维Lebesgue限制测度入口。严格负额外要求∫f²>0。",
 "尚未形式化非零光滑紧支撑函数的正L²范数、Lp等价类范数接口；不是一般时间积分求导、PDE能量律或解存在。",
 {"x":8,"top":703,"font_size":6.0,"lines":["初值积分计算","须平方可积","严格负须正积分"]}),
("second-layer-components", "§11.1 λ_t(0)=∇f 和 S₁(0)=c‖∇f‖²：仅分量接口与其积分", "真实局部时间；分量代数；实际分量积分",
 ["hasDerivAt_initial_flux","secondLayerSpatialInitial_zero","secondLayerSpatialInitial_eq","secondLayerSpatialInitial_integral"],
 "真实HasDerivAt辅助演化在h₀=l₀=0时给l′(0)=V；复用零吸收空间耗散得c(gx²+gy²)。分量的独立支撑条件与平方可积性给实际分量积分c(∫gx²+∫gy²)。",
 "V、gx、gy与真实∂ᵢf的梯度对应、混合微分交换、梯度支撑性质、Poincaré和两层闭合未完成。",
 {"x":535,"top":745,"font_size":6.0,"lines":["分量及其积分","梯度接口","待完成"]}),
]
entries=[]
for id,location,kind,names,scope,missing,draw in data:
 full=[prefix+n for n in names]
 for name in full:
  assert name in audited
  assert "#print axioms "+name in audit_source
  assert re.search(r"\btheorem\s+"+re.escape(name.removeprefix(prefix))+r"\b",module_text)
 entries.append(dict(id=id,page=15,printed_page=15,location=location,type=kind,module=source,theorems=full,
     definitions=[],scope=scope,missing=missing,new_tick=True,draw=draw,source_sha256=sha(root/source),
     build_log=f"logs/v0.2.4/{build}.log",audit_log=f"logs/v0.2.4/{audit}.log"))
notes=[
{"id":"cross-reference","page":15,"x":535,"top":618,"font_size":6.0,
 "lines":["导数关系见","(7.6)；(7.7)","是耗散表达式"]},
{"id":"scope","page":15,"x":68,"top":810,"font_size":7.0,
 "lines":["v0.2.4：红勾仅指初值代数、实际初值积分及分量版；完整 PDE 能量律与解存在性待完成。",
          "真实局部时间求导已有证明；正文的完整空间能量初始增长仍是条件性解释。"]}
]
protected={path:digest for path,digest in old_inspection["hashes"].items() if path!=str(target)}
plan=dict(stage="v0.2.4",page_count=18,backup=backup_record,build=build,audit=audit,entries=entries,notes=notes,
 font="/System/Library/Fonts/Supplemental/Arial Unicode.ttf",modified_pages=[15],protected_hashes=protected,
 current_audited_theorems=len(audited),old_mark_entries_rechecked=len(legacy["entries"]),
 old_annotations_preserved_count=sum(len(p["/Annots"]) if "/Annots" in p else 0 for p in PdfReader(target).pages))
(d/"annotation_plan.json").write_text(json.dumps(plan,ensure_ascii=False,indent=2)+"\n")
print(json.dumps({"backup":backup_record,"current_audited_theorems":len(audited),
                  "old_mark_entries_rechecked":len(legacy["entries"]),"new_ticks":len(entries)},ensure_ascii=False,indent=2))
