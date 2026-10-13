from pathlib import Path
import json
root=Path.cwd();folder=root/'logs/v0.3.3/pdf'
plan=json.loads((folder/'annotation_plan.json').read_text())
text="""

## v0.3.2–v0.3.3：条件性能量律、图范数及重构控制（2026-10-13）

本节追加当前范围，保留上述历史和全部用户批注。当前指定副本为 18 页，原 150 项批注全部保留，新增 12 个带范围红勾、6 条说明，共 168 项批注。修改页实际页序与印刷页码均为 10、11、12、13。

构建与独立公理审计分别完成：

- v0.3.2：[构建](../logs/v0.3.2/20261013T095839_225389_lake_build.log)／[审计](../logs/v0.3.2/20261013T100104_046897_axioms_audit.log)，均退出 0，288 条公理输出。
- v0.3.3：[构建](../logs/v0.3.3/20261013T100156_159842_lake_build.log)／[审计](../logs/v0.3.3/20261013T100321_602582_axioms_audit.log)，均退出 0，316 条公理输出，包含全部旧声明与本轮 53 条新增正式定理。
- 仅标准 propext、Classical.choice、Quot.sound；无 sorryAx、自定义占位公理。28 项既有标注账目中的定理全部再次与当前审计核对。
- [来源版本复核](../logs/v0.3.3/pdf/source_review.md)记录 V7 原文、模型合同、锁文件未变及路线图入场差异。原始 md/tex/pdf 未修改。

标注中“条件性空间”表示实际 L²/加权空间上的定理已经证明，但一般 Green、迹、Poincaré 与时间交换仍需在具体矩形上兑现。定义和输入接口本身不打完成勾。

"""
for e in plan['entries']:
 text+=f"### {e['id']}：{e['location']}\n\n"
 text+=f"- PDF 实际页序 **{e['page']}**，印刷页码 **{e['printed_page']}**。\n"
 text+=f"- 类型：{e['type']}。本轮新增红勾：**是**；可见限定文字：“{' / '.join(e['draw']['lines'])}”。\n"
 text+=f"- 源码：[{Path(e['module']).name}](../{e['module']})。\n"
 text+="- 完整定理名："+'、'.join('`'+n+'`'for n in e['theorems'])+"。\n"
 text+=f"- 准确已证范围：{e['scope']}\n- 未完成接口：{e['missing']}\n"
 text+=f"- 当前证据：[最终构建](../{e['build_log']})、[独立审计](../{e['audit_log']})；源码 SHA-256 `{e['source_sha256']}`。\n\n"
text+="""
### 只作说明而不打证明勾

- 第 11 页 (7.5)：“Green 接口／具体矩形证明待完成”；一般接口输入不记为已证明具体 Green。
- 第 10–13 页顶部新增当前范围说明。第 11 页“积分待完成”、第 12 页“右式能量律仍待完成”等旧文字原样保留，顶部明确它们属于历史范围；当前新增勾只覆盖条件性定理。
- 第 13 页 §8.2：原文严格 `< B_sp` 在 B_sp=0 时不成立。说明实际 Lean 使用足够的非严格估计，并保留零状态与 1/4、1 原常数。
- (6.2)、(7.7) 定义并非因本轮重新获得完成勾。没有给 (6.8)–(6.9)、(9.5)–(9.7)、完整 D₇ 非负、最终单调性、矩形 PDE 主定理新增整体完成勾。
- 全部旧标记保留；本轮没有删除或重新定位原批注，也没有重复叠加同一 ID。

### 编辑保护、定位与验收

"""
text+=f"- [修改前备份](../logs/v0.3.3/pdf/{Path(plan['backup']['backup']).name})；[备份及哈希](../logs/v0.3.3/pdf/backup.json)。原哈希 `{plan['backup']['sha256_before']}`。\n"
text+="""
- [标注脚本](../logs/v0.3.3/pdf/annotate_pdf.py)、[定位及证据计划](../logs/v0.3.3/pdf/annotation_plan.json)、[定位预检](../logs/v0.3.3/pdf/coordinate_preflight.json)。红勾由矢量折线绘制；范围文字使用嵌入中文字体。稳定 ID 与计划哈希防止重复叠加；目标外部变化时停止写入。
- [实际 PDF 编辑日志](../logs/v0.3.3/20261013T100559_337529_pdf_annotate.log)、[渲染日志](../logs/v0.3.3/20261013T100607_874052_pdf_render.log)、[最终验证日志](../logs/v0.3.3/20261013T100735_806250_pdf_verify.log)。
- [结构/证据验收](../logs/v0.3.3/pdf/verification.json)、[逐页视觉检查](../logs/v0.3.3/pdf/visual_review.json)：重新打开副本，四页均以 Poppler 150 dpi 渲染并逐页检查，标记清晰、无限定文字裁切、无正文/公式/编号遮挡。原页序、页面框、可选文本以及未改页面提取文本保持。
- 最终 PDF SHA-256：`c9d5b114e9de7befb92e001ccc1486227acef27c8c0933fc688722eaf3ca44a3`。
"""
path=root/'docs/pdf_formalization_marks.md'
assert '## v0.3.2–v0.3.3：条件性' not in path.read_text()
path.write_text(path.read_text()+text)
print('已追加12项逐式证明证据、6项范围说明及视觉验收记录。')
