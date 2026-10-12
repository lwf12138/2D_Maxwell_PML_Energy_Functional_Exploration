
"""依据已渲染PDF与实际证据，追加v0.2.4账本。"""
from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import json
root=Path.cwd();d=root/"logs/v0.2.4/pdf"
plan=json.loads((d/"annotation_plan.json").read_text())
verification=json.loads((d/"verification.json").read_text())
assert (d/"after-15.png").exists()
visual={"reviewed_at":datetime.now(ZoneInfo("Asia/Shanghai")).isoformat(),
 "reviewed_images":["logs/v0.2.4/pdf/after-15.png"],"modified_pages":[15],"render_scale_to":1800,
 "method":"逐页打开最终1800px渲染图进行视觉检查；本轮只修改第15页。",
 "findings":{"four_vector_ticks_visible":True,"six_point_side_notes_legible":True,
 "seven_point_bottom_scope_notes_legible":True,"no_clipping":True,"no_text_or_formula_obscured":True,
 "old_layout_and_page_number_preserved":True,"mark_scope_matches_plan":True},"result":"通过"}
(d/"visual_review.json").write_text(json.dumps(visual,ensure_ascii=False,indent=2)+"\n")
verification["visual_review"]="passed: after-15.png已逐页查看，四勾、范围文字及页码无裁切遮挡"
(d/"verification.json").write_text(json.dumps(verification,ensure_ascii=False,indent=2)+"\n")
sections=[]
for e in plan["entries"]:
 names="、".join("¤"+x+"¤" for x in e["theorems"])
 sections.append("\n".join([
 "### v0.2.4 / "+e["id"],"",
 "- PDF 页码：实际第 **15** 页；印刷页码 **15**。",
 "- 定位："+e["location"]+"；均为 §11.1 的未编号内容。",
 "- 验证类别：**"+e["type"]+"**。",
 "- Lean 文件：[SingleLayer.lean](../"+e["module"]+")。",
 "- 完整定理名："+names+"。",
 "- 已验证范围："+e["scope"],
 "- 未完成接口："+e["missing"],
 "- 本轮新增红勾：**✓ "+"；".join(e["draw"]["lines"])+"**。",
 "- 证据：**B24 + A24**；上述声明均在正式导入链和本次审计输出中。",""]))
section="""## v0.2.4 新增记录：§11.1 初值计算（2026-10-11）

本节是当前追加记录；下方 v0.2.3 及后续注释修订记录全部保留为历史。v0.2.4 仅修改实际/印刷第 **15** 页，不重画旧红勾。

### 当前证据与版本

- **B24**：[正式构建](../logs/v0.2.4/BUILD.log)／[命令、目录、退出码](../logs/v0.2.4/BUILD.json)，退出 0。
- **A24**：[独立公理审计](../logs/v0.2.4/AUDIT.log)／[命令、目录、退出码](../logs/v0.2.4/AUDIT.json)，退出 0。
- 全工程 154 条定理均在本次审计中；仅有标准 ¤propext¤、¤Classical.choice¤、¤Quot.sound¤。无 ¤sorryAx¤ 或自定义证明占位公理。
- [本轮机器证据计划](../logs/v0.2.4/pdf/annotation_plan.json)核对新模块正式导入、完整定理名、源码哈希及审计。还逐项确认旧计划全部 20 项标注所引用定理仍出现在本次审计中，不重复添加旧勾。
- [来源只读核对](../logs/v0.2.4/pdf/source_review.md)与[哈希/页码/原批注快照](../logs/v0.2.4/pdf/read_only_inspection.json)：V7 MD/TEX/原 PDF、已接受模型合同未变。路线图在进入本轮前仅将 v0.2.3 四项勾选；v0.2.4/v0.3.1 数学任务未改，本轮未写路线图。
- §11.1 首段“精确导数见 (7.7)”的交叉引用不准确：**(7.6) 是能量导数关系，(7.7) 是耗散表达式**。本轮仅增加旁注提醒，原文保留。§11.1 负耗散式没有编号，未误标为 §11.2 的 (11.1)。

### 新增红勾的范围

ENTRIES

### 本轮只登记、不打完成红勾的内容

- §11.1 的初值选择是输入；旁边“初始兼容已核验”只指从这些数据推出的五个初始数值关系，不代表存在满足全 PDE/边界/正则性的解。
- (6.2)、(7.7)：¤singleLayerEnergy¤、¤singleLayerDissipation¤ 直接组合既有三个局部块；这里只登记定义对应，不为定义录入打“已证明”勾。
- ¤LeanPML.PML.Obstructions.initial_derivative_values¤ 是原方程初值的代数化简；¤hasDerivAt_initial_fields_zero¤ 从真实导数证据得到 E、P 的初始零导数。原磁旋度/提升/空间迹的兑现仍不在这一包装定理中。
- ¤LeanPML.PML.Obstructions.hasDerivAt_initial_localEnergy¤ 与 ¤initial_localEnergy_rate_pos¤ 已证明真实**局部时间密度**的初始导数及正号。PDF 正文的 $\\mathcal F_c[U_0]'(0)>0$ 指完整空间能量，故这里**不打完整 PDE 求导完成勾**；页底注明它仍依赖完整能量律及解存在/正则性接口。
- ¤singleLayerEnergy_initial¤ 的特殊初值能量代数值已核验；未因此证明一般正定性或单调性。
- 未给 (6.7)–(6.10)、(7.5)–(7.8)、(9.5)–(9.7) 的完整结论添加完成勾。Poincaré、一般加权路径积分求导、Green/PEC、两层闭合仍待完成。
- 旧图例描述截至 v0.2.3 的空间接口状态；本页新增说明明确区分已经完成的**特殊初值积分**与尚未完成的**一般 PDE 空间能量律**，不改写旧用户批注。

### 备份、编辑和视觉验收

- 新建[修改前副本](../logs/v0.2.4/pdf/BACKUP)，不覆盖任何旧阶段备份；[备份哈希记录](../logs/v0.2.4/pdf/backup.json)。
- 修改前 SHA-256：¤0735771fa5d38adc70a74f21be3c109b490d1c91587414f874ac0c2d049409be¤。
- 修改后 SHA-256：¤AFTERHASH¤。
- [定位与证据脚本](../logs/v0.2.4/pdf/build_mark_plan.py)、[矢量标注脚本](../logs/v0.2.4/pdf/annotate_pdf.py)、[保留性与渲染脚本](../logs/v0.2.4/pdf/verify_pdf.py)均保留。稳定标记 ID 和计划哈希防止重跑重复叠加。
- [编辑日志](../logs/v0.2.4/20261011T232336_537816_pdf_annotate.log)、[重新打开/渲染日志](../logs/v0.2.4/20261011T232342_713491_pdf_verify_render.log)均退出 0；[机器验收](../logs/v0.2.4/pdf/verification.json)、[视觉验收](../logs/v0.2.4/pdf/visual_review.json)。
- 18 页及原始页面尺寸/页序不变；全部原文可选文本和 135 项原批注保留。本次新增 **4 个矢量红勾与 2 个范围说明**，总批注 141 项。
- 已重新打开最终 PDF，并渲染本轮全部修改页（第 15 页）逐页检查。侧栏 6pt 和页底 7pt 中文可见，勾号清晰，没有裁切、覆盖公式/编号/正文或旧批注。
- 准备脚本第一次因 pypdf 将 ¤/Annots¤ 返回间接对象而失败，目标 PDF 尚未编辑；修复读取方式后成功。保留[原失败](../logs/v0.2.4/20261011T232305_726240_pdf_evidence_plan.log)与[成功重试](../logs/v0.2.4/20261011T232326_564193_pdf_evidence_plan_retry.log)，同一新备份经哈希确认后复用，未覆盖。

---

## 以下为 v0.2.3 历史记录

"""
section=section.replace("BUILD",plan["build"]).replace("AUDIT",plan["audit"]).replace("ENTRIES","\n".join(sections))
section=section.replace("BACKUP",Path(plan["backup"]["backup"]).name).replace("AFTERHASH",verification["sha256_after"])
section=section.replace("¤",chr(96))
ledger=root/"docs/pdf_formalization_marks.md";old=ledger.read_text()
assert "## v0.2.4 新增记录" not in old
old=old.replace("# PDF 形式化标注账本（截至 v0.2.3）","# PDF 形式化标注账本（截至 v0.2.4）",1)
assert "## 来源与保护" in old
ledger.write_text(old.replace("## 来源与保护",section+"## 来源与保护",1))
print(json.dumps({"visual_review":visual["result"],"ledger":str(ledger),"sha256_after":verification["sha256_after"],
 "page_count":18,"modified_pages":[15],"new_red_ticks":4,"old_annotations_preserved":135},ensure_ascii=False,indent=2))
