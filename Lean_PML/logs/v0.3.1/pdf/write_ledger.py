"""追加 v0.3.1 已验证范围，不覆盖前阶段账本或记录。"""
from pathlib import Path
import json,hashlib
root=Path.cwd();folder=root/'logs/v0.3.1/pdf'
plan=json.loads((folder/'annotation_plan.json').read_text())
qa=json.loads((folder/'visual_review.json').read_text())
assert qa['status']=='passed'
target=root/'docs/pdf_formalization_marks.md'
previous=target.read_text()
assert '## v0.3.1 新增记录' not in previous
backup=folder/'before_pdf_formalization_marks.md'
with backup.open('x')as f:f.write(previous)
build=plan['build'];audit=plan['audit']
lines=[
'# PDF 形式化标注账本（截至 v0.3.1）','',
'用途：把红勾连接到实际可编译定理、当前审计及准确范围。定义录入不算证明；真实空间积分/内积求导仍不等于 PDE 能量律。','',
'## v0.3.1 新增记录：实际 L²、加权表示与积分求导（2026-10-13）','',
'本节为追加记录；下面 v0.2.4、v0.2.3 及注释修订历史全部保留。本轮只修改实际/印刷第 **8、9、11、12 页**，新增 **4 个矢量红勾和 5 个定义/范围说明**。','',
'### 当前证据与来源版本','',
f'- **B31**：[正式构建](../logs/v0.3.1/{build}.log)／[命令、目录、退出码](../logs/v0.3.1/{build}.json)，退出 0。',
f'- **A31**：[独立公理审计](../logs/v0.3.1/{audit}.log)／[命令、目录、退出码](../logs/v0.3.1/{audit}.json)，退出 0。',
'- 本次审计 263 条定理（旧 154 条、新 109 条），无 sorryAx，仅标准 propext、Classical.choice、Quot.sound。主要新定理已在正式导入链中。',
'- [机器证据计划](../logs/v0.3.1/pdf/annotation_plan.json)逐项核对新勾定理的完整名称、源文件哈希和本次审计；同时重新核对旧 24 项标注的全部定理仍在本次审计中。',
'- [来源核对](../logs/v0.3.1/pdf/source_review.md)、[源文件哈希](../logs/v0.3.1/pdf/input_hashes.json)、[页码和旧批注快照](../logs/v0.3.1/pdf/read_only_inspection.json)：V7 MD/TEX/原 PDF、模型合同、工具链与依赖锁定均未变。',
'- 路线图进入本轮前只把 v0.2.4 四项改为已勾选；v0.3.1–v0.3.3 文字未改，见[差异记录](../logs/v0.3.1/pdf/roadmap_preexisting_diff.patch)。没有用历史勾选代替本轮构建。',
'- §11.1 的既有交叉引用疑点保留：(7.6) 是能量导数关系，(7.7) 是耗散定义。本轮未修改原文。','',
'### 四个新红勾',''
]
for e in plan['entries']:
 if not e['new_tick']:continue
 lines += [
  '#### v0.3.1 / '+e['id'],'',
  f'- 页码：实际第 **{e["page"]}** 页；印刷页码 **{e["printed_page"]}**。',
  '- 定位：'+e['location']+'。',
  '- 类别：**'+e['type']+'**。',
  f'- Lean 文件：[{Path(e["module"]).name}](../{e["module"]})。',
  '- 完整定理名：'+'、'.join('¤'+n+'¤'for n in e['theorems'])+'。',
  '- 实际假设和结论：'+e['scope'],
  '- 未完成接口：'+e['missing'],
  '- PDF 旁注：**✓ '+'；'.join(e['draw']['lines'])+'**。',
  '- 证据：**B31 + A31**。',''
 ]
lines += [
'### 实际空间、定义说明与未完成部分','',
'- [WeightedL2.lean](../LeanPML/Analysis/WeightedL2.lean) 中 ¤LeanPML.Analysis.weightedSubspace_isClosed¤、¤weighted_completeSpace¤ 已证明平方根坐标空间为闭子空间并完备；¤physicalL2_injective¤、¤physicalL2_weightedOfFunction¤、¤weightedOfFunction_congr¤ 处理双向恢复和代表元独立；¤weighted_norm_sq_eq_integral¤、¤weighted_inner_eq_integral¤ 给出实际加权积分表示。它们均在 A31 中；本勾没有假设 w 本质有界。',
'- [SpatialCoefficients.lean](../LeanPML/PML/SpatialCoefficients.lean) 用实际可测 p/r 和原始幅度条件构造系数；分离入口保留 p(x)、r(y)，a.e. 入口选择等价的良好代表。ν 可以取整个开矩形限制测度，未缩域。',
'- 第 8 页 (5.5)–(5.6) 增加实际加权表示说明，**定义本身不打完成勾**。新增嵌入勾与已有“下界/无界；系数性质”勾分别对应分析和点态代数。',
'- 第 9 页页底说明 (6.2)–(6.5) 已有实际 L²/积分定义。¤FieldState¤ 的 V 是速度坐标；¤StateHasDerivAt¤ 绑定各分量真实导数，¤SameSourcePath¤ 连接同一来源的两层；内部的导数层时间关系另经邻域等式推出。空间域/弱梯度/零迹仍是显式 Conditional 接口。',
'- (6.4) 的 ¤energy7¤ 和 (6.5) 的 ¤graphSquare7¤ 使用 ¤scaleK¤ 与同源路径。¤graphSquare¤ 仍是图范数平方候选，未证明其零分离或能量双边估计。',
'- 第 11 页 (7.7) 只标“实际积分定义；符号未定”。¤fieldDissipationDensity_integrable¤、¤fieldDissipation_eq_integral¤ 已连接旧三个块和实际积分，但 D_c 不被声明非负。',
'- 第 12 页 (7.8) 只标“左式实际定义；右式能量律仍待完成”。¤twoLayerDissipation_integrable¤、¤twoLayerDissipation_eq_integral¤ 保证定义合法；¤dissipation7¤ 用同源 first.R/second.R 表示 P_t/P_tt，未证明 D₇ 非负或 E₇′=−D₇。',
'- 第 11 页旧“空间积分待完成”“仅系数界；非空间积分”批注完整保留；页底新增 v0.3.1 限定，说明新勾覆盖实际分量积分和范数路径求导，旧勾保留历史范围。没有把新证明扩大为 primitive/Green 组合后的恒等式。',
'- **不打完成勾：** (6.7)–(6.10)、(7.5)–(7.8) 的完整能量律、(9.5)–(9.7)、具体梯度/零迹/Green/Poincaré、完整 PDE 对应、解存在唯一性。T10、T11、T12、T15、T17、T18 仍按已实现子结论逐项登记，不整体标记完成。',
'',
'### 备份、编辑、视觉验收与可重复性','',
f'- 新建[修改前副本](../logs/v0.3.1/pdf/{Path(plan["backup"]["backup"]).name})；[备份信息](../logs/v0.3.1/pdf/backup.json)。旧阶段及用户原有备份未覆盖。',
f'- 修改前 SHA-256：¤{plan["backup"]["sha256_before"]}¤。',
f'- 修改后 SHA-256：¤{qa["sha256"]}¤。',
'- [标注证据脚本](../logs/v0.3.1/pdf/build_mark_plan.py)、[矢量编辑脚本](../logs/v0.3.1/pdf/annotate_pdf.py)、[重新打开/渲染脚本](../logs/v0.3.1/pdf/verify_pdf.py)和[视觉/像素核验脚本](../logs/v0.3.1/pdf/record_visual_qa.py)保留；稳定标记 ID 与计划哈希防止重复叠加。',
'- [编辑日志](../logs/v0.3.1/20261013T002336_826429_pdf_annotate.log)、[重新打开及渲染日志](../logs/v0.3.1/20261013T002342_329628_pdf_verify_render.log)、[视觉验收日志](../logs/v0.3.1/20261013T002436_189341_pdf_visual_qa.log)均退出 0；[机器验收](../logs/v0.3.1/pdf/verification.json)、[逐页视觉记录](../logs/v0.3.1/pdf/visual_review.json)。',
'- 18 页、页面尺寸与页序不变；原文可选文本保留，141 项旧批注/链接全部保留；新增 9 项后总计 150 项。',
'- 已打开并逐页检查全部修改页 8、9、11、12。侧栏 6pt、说明 6.5–7pt 的嵌入中文和矢量勾清晰；没有裁切或遮挡正文、公式、编号、页码及旧批注。标记框之外渲染像素完全相同；其余 14 页内容流字节相同。',
'- 只读准备曾因脚本名 inspect.py 遮蔽标准库而失败，改名后成功；定位预检曾发现第 11 页页底说明碰页码，在编辑前下移修复。两类失败和成功日志均保留，未把未运行或失败命令登记为通过。',
'','---','',
]
text='\n'.join(lines).replace('¤','¤')+'\n'+previous
text=text.replace('¤',chr(96))
target.write_text(text)
print('已追加 v0.3.1 账本；此前完整原文保存在同一文件下方及 before_pdf_formalization_marks.md。')
print('账本 SHA-256:',hashlib.sha256(target.read_bytes()).hexdigest())
