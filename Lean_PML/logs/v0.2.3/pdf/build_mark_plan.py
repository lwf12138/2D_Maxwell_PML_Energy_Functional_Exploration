"""v0.2.3 标注证据表：从当前源码和本次真实审计核对，不编辑 PDF。"""
from pathlib import Path
import json,re,hashlib
root=Path.cwd()
base=root/"logs/v0.2.3"
pdfdir=base/"pdf"
build="20261010T232910_472603_lake_build_retry"
audit="20261010T232931_121820_axioms_audit_retry"
for stem in (build,audit):
    meta=json.loads((base/(stem+".json")).read_text())
    assert meta["exit_code"]==0 and meta["status"]=="finished"
audit_text=(base/(audit+".log")).read_text()
audited=set(re.findall(r"'([^']+)' depends on axioms:",audit_text))
assert len(audited)==134 and "sorryAx" not in audit_text
snapshot=json.loads((pdfdir/"before_inspection.json").read_text())
pages=snapshot["V7_global_energy_副本.pdf"]["pages"]
labels=[
("(2.4) 的 CD","局部时间","CD；局部时间","时间积分提升、实际场正则性及另外两个磁不变量"),
("(2.4) 的 CZ1、CZ2","局部时间","CZ1/CZ2；局部时间","磁辅助 Cx、Cy；不是五个不变量全部完成"),
("(2.5) 中 Z1、Z2 两项","局部时间","Z1/Z2；初值保持","Qx、Qy 重构及完整双向 PDE 等价"),
("(5.2) 定义后的 A、K、c* 正性","代数；定义不计证明","参数代数；正性已证","CP 仅为给定正参数；矩形 Poincaré (5.1)"),
("(5.3) 邻旁的阈值等价子结论","假设；派生代数","阈值等价；实数条件","(5.3) 本身是输入；尚无 L∞ 场和空间幅度模型"),
("(5.4) 全部系数界","代数","全部系数界；固定点","从点值界提升到实际空间场"),
("(5.5) 分支定义与零区值","定义；派生代数","权重分支；含零吸收","定义本身不是待证结论；(5.6) 加权空间"),
("(5.5) 后 w≥3/2 和可能无界","代数","下界/无界；系数性质","下界限 a>0；加权空间构造及嵌入"),
("(7.2) 后耗散权重有界子结论","代数","仅系数界；非空间积分","全积分 (7.2) 和空间时间链式法则"),
("(7.3)","局部时间；代数","局部时间；真实求导","实际场、μ 因子、空间积分；De 未证非负"),
("(7.4) 前未编号移位约束","局部时间","兼容求导；邻域关系","场层兼容、微分与积分的接口"),
("(7.4)","局部时间；代数","局部时间；真实求导","实际场、μ 因子、空间积分；DD 未证非负"),
("(8.1)","代数","约束消元；代数已证","Q 到 FD 仍除 2κ；完整能量正定性"),
("(8.2)","代数","四组系数界；全部已证","空间范数估计和后续正定性"),
("(9.2) 前 θ 分支及 0≤θ≤1、和为1","代数；定义不计证明","分配权重；分支已证","J 空间积分与 (9.3)、(9.5)"),
("(9.6) 后文字中的 KS²≤1/16","代数","KS²≤1/16；代数已证","完整 (9.6) 空间估计与耗散分配"),
]
entries=[]
for page_num,page in enumerate(pages,1):
    for annotation in page["annotations"]:
        if annotation.get("/Subtype")!="/Square": continue
        text=annotation["/Contents"]
        i=len(entries)
        loc,typ,visible,missing=labels[i]
        module=re.search(r"模块：([^\n]+)",text).group(1)
        names=re.search(r"声明：([^\n]+)",text).group(1).split("; ")
        source=(root/module).read_text()
        theorems=[];definitions=[]
        for name in names:
            fqn="LeanPML.PML."+name
            if re.search(r"^theorem "+re.escape(name)+r"\b",source,re.M):
                assert fqn in audited,fqn
                theorems.append(fqn)
            else:
                assert re.search(r"^(?:noncomputable )?def "+re.escape(name)+r"\b",source,re.M),name
                definitions.append(fqn)
        assert "import "+module[:-5].replace("/",".") in (root/"LeanPML.lean").read_text()
        entries.append(dict(id=f"old-{i+1:02d}",page=page_num,printed_page=page_num,
            location=loc,type=typ,module=module,theorems=theorems,definitions=definitions,
            scope=text.split("\n\n")[0],missing=missing,
            new_tick=False,old_tick_preserved=True,visible_text=visible,
            old_annotation=annotation))
assert len(entries)==16
def new(id,page,location,scope,missing,names,lines,x,top):
    entries.append(dict(id=id,page=page,printed_page=page,location=location,
        type="局部时间" if id!="spatial-pointwise" else "代数；点态",
        module="LeanPML/PML/LocalSpatial.lean",
        theorems=["LeanPML.PML."+n for n in names],definitions=[],
        scope=scope,missing=missing,new_tick=True,old_tick_preserved=False,
        visible_text="✓ "+"；".join(lines),draw=dict(x=x,top=top,lines=lines,font_size=6.0)))
new("zero-preservation",8,"§5.2：在 Z 上 φ_t=0，因此 φ₀=0 保持（未编号）",
    "固定点两个时间函数闭区间连续，内部真实辅助演化；非负吸收且 a=0，从初始 l(0)=h(0) 推出整段 l=h，包括 T=0。",
    "不是 (5.7) 一般积分解公式、五个不变量整体、加权正则性或 PDE 提升。",
    ["zeroSpatial_compatibility_preserved"],["时间保持","须初值 f=0","空间接口待证"],535,474)
new("spatial-positive",10,"(7.1) 的正吸收分支",
    "a>0 下权重平衡、数值恒等式，以及真实时间 h'=V、l'=V+σⱼh−σᵢl 推出的 Fsp 求导；包含两个方向。",
    "h 与真实空间梯度、混合导数交换、可测可积、空间积分、Green/PEC 未实现。",
    ["spatial_weight_balance","spatial_rate_identity","hasDerivAt_spatialAuxiliary",
     "hasDerivAt_spatialEnergy_pos","hasDerivAt_spatialEnergy2D"],
    ["局部时间版","空间接口待证","积分待完成"],535,687)
new("spatial-zero",10,"(7.1) 后零吸收区未编号二维公式",
    "h 的实际时间导数给出 h²/2 和双分量平方和的导数；接回分支能量时明确需要 l=h，保留 c(hx²+hy²)。",
    "p=r=0 不自动给出兼容；完整 PDE 中零辅助量来源、实际梯度及空间积分仍待兑现。",
    ["hasDerivAt_zeroSpatialComponent","hasDerivAt_zeroSpatial2D",
     "hasDerivAt_spatialEnergy_zero","zeroSpatial_compatibility_preserved"],
    ["局部时间版","零区须兼容","空间接口待证"],535,758)
new("spatial-pointwise",11,"(7.2) 被积式的点态非负与独立零区密度（不是整式）",
    "0≤p,r≤S≤c/4、c>0 下，两个方向的分支密度非负；零区精确为 c(hx²+hy²)。",
    "该勾只指被积子表达式；没有完成 (7.2) 积分算子、可积性、加权路径求导或全域能量恒等式。",
    ["spatialDissipation_nonneg","spatialDissipation2D_nonneg",
     "spatialDissipation2D_of_sum_zero"],
    ["点态非负","空间积分","待完成"],8,97)
for e in entries:
    assert set(e["theorems"])<=audited,e["id"]
    e["build_log"]=f"logs/v0.2.3/{build}.log"
    e["audit_log"]=f"logs/v0.2.3/{audit}.log"
    e["source_sha256"]=hashlib.sha256((root/e["module"]).read_bytes()).hexdigest()
notes=[
dict(id="legend",page=1,x=68,top=64,font_size=8,lines=[
"v0.2.3 标注图例：红勾只对应旁注中的已验证结论。",
"代数：实数恒等式与系数界；局部时间：真实时间函数的求导与保持。",
"空间/PDE：场、积分与边界接口仍待完成；定义和假设不计证明。"]),
dict(id="clarify-threshold",page=7,x=8,top=688,font_size=6,lines=["(5.3) 为输入","旧勾仅指","阈值等价"],entry="old-05"),
dict(id="clarify-weight-definition",page=8,x=8,top=110,font_size=6,lines=["(5.5) 为定义","旧勾仅指","零分支计算"],entry="old-07"),
dict(id="electric-space-pending",page=11,x=550,top=298,font_size=5.8,lines=["积分待完成"],entry="old-10"),
dict(id="polar-space-pending",page=11,x=550,top=426,font_size=5.8,lines=["积分待完成"],entry="old-12"),
]
plan=dict(stage="v0.2.3",page_count=18,backup=json.loads((pdfdir/"backup.json").read_text()),
    build=build,audit=audit,entries=entries,notes=notes,
    font="/System/Library/Fonts/Supplemental/Arial Unicode.ttf",
    modified_pages=sorted({e["page"] for e in entries if e["new_tick"]}|{n["page"] for n in notes}))
(pdfdir/"annotation_plan.json").write_text(json.dumps(plan,ensure_ascii=False,indent=2)+"\n")
print("证据核对：134 条当前审计；16 项旧标记保留并重新核验；4 项新红勾；5 项补充图例/限定。")
print("拟修改页（实际页序与印刷页码相同）：",plan["modified_pages"])
