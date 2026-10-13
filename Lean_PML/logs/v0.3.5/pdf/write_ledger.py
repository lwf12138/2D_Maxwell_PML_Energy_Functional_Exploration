from pathlib import Path
import json
root=Path.cwd();folder=root/'logs/v0.3.5/pdf'
p=json.loads((folder/'annotation_plan.json').read_text());v=json.loads((folder/'verification.json').read_text())
file=root/'docs/pdf_formalization_marks.md';s=file.read_text()
marker='## v0.3.4–v0.3.5：第 9 节与条件性有限区间结论（2026-10-13）'
assert marker not in s
out=['\n\n'+marker,'',
'用途：把本轮实际证明、PDF 标记与真实构建证据逐项连接。以下是追加记录；上方所有标记及历史说明保留。两个阶段已分别通过验收，最终当前工程审计 369 条声明，没有 sorryAx，仅标准 propext、Classical.choice、Quot.sound。', '',
'条件性表示 Lean 证明了列明分析接口下的结论，不表示具体矩形 Green、迹、精确 Poincaré 常数及时间/空间微分交换已经证明。定理 6.1 的抽象分析核心已闭合；原八变量完整 PDE 对应、提升唯一性及解存在唯一性仍未完成。', '',
'### 本轮新增标记', '',
'实际页序与印刷页码一致。红勾只覆盖下表的结论；(9.2) 的定义另有文字说明，不作为已证明结论。', '',
'| 页序／印刷页 | 公式或定位 | 类型 | 红勾旁的可见限定文字 |',
'|---|---|---|---|']
for e in p['entries']:
 out.append(f"| {e['page']}／{e['printed_page']} | {e['location']} | {e['category']} | ✓ {'；'.join(e['draw']['lines'])} |")
for e in p['entries']:
 out += ['',f"#### {e['page']} 页：{e['location']}",'',
 f"- Lean 文件：[{Path(e['module']).name}](../{e['module']})。", 
 '- 完整定理：'+'、'.join('`'+t+'`'for t in e['theorems'])+'。',
 '- 准确范围与条件：'+e['scope'],
 '- 剩余接口：'+e['missing'],
 f"- 本轮新增矢量红勾；稳定标记 ID `LeanPML.v0.3.5.{e['id']}`。",
 f"- 实际证据：[构建](../{e['build_log']})／[独立公理审计](../{e['audit_log']})，退出码均为 0。当前最终复核还通过 v0.3.5 的完整导入和全部审计。"]
out += ['', '### 时间范围及未勾选结论', '',
'能量导数、(9.4)–(9.7) 同源估计及精确定量耗散下界作用于开时间区间 (0,T)。闭区间 [0,T] 的静态约束与实际场连续性另行输入，得到静态双边界、能量非负、单调性、初值控制。积分平衡额外需要真实导数层 second.R=P_tt 的 L² 闭区间连续性。允许 T=0、t₁=t₂ 和两个端点，不要求端点普通双侧导数，也不由 T=0 的空内部条件推导端点耗散正性。', '',
'本轮没有给具体矩形 Green/Poincaré、实际微分交换、完整 PDE 对应或解存在唯一性加完成勾。定义/假设本身没有完成勾；单调不增不代表严格递减。', '',
'### 旧标记与保护', '',
'第 10、12、13 页保留旧阶段“耗散/单调性待完成”等文字，新增页首说明其历史属性及当前条件性范围；第 14 页保留旧 θ 性质和 KS² 系数代数红勾，不重复叠加。第 14 页另加“J定义已录入；另证可积非负”及条件性图例。本輪不删除或重写用户批注。', '',
f"入场 18 页、{v['old_annotations']} 项批注，最终 18 页、{v['total_annotations']} 项批注，新增 {v['new_red_ticks']} 个红勾和 {v['new_notes']} 条说明。旧页框、可选正文与旧批注保持；其余 14 页可选文本完全相同。修改页均经 Poppler 150 dpi 渲染并逐页检查：可见、对应准确、无覆盖正文/编号、无缺字及裁切。",'',
f"- [阶段时间备份]({Path(p['backup']['backup']).relative_to(root).as_posix().join(['../',''])})。",
f"- 修改前 SHA-256：`{v['sha256_before']}`；修改后：`{v['sha256_after']}`。",
'- [备份信息](../logs/v0.3.5/pdf/backup.json)、[证据/定位计划](../logs/v0.3.5/pdf/annotation_plan.json)、[坐标预检](../logs/v0.3.5/pdf/coordinate_preflight.json)。',
'- [结构与证据验收](../logs/v0.3.5/pdf/verification.json)、[逐页视觉验收](../logs/v0.3.5/pdf/visual_review.json)。',
'- [标注脚本](../logs/v0.3.5/pdf/annotate_pdf.py)使用独立阶段 ID 和计划哈希，完全相同计划重跑直接跳过；目标发生外部修改时停止，不覆盖新批注。',
'- [编辑日志](../logs/v0.3.5/20261013T214910_164598_pdf_annotate.log)、[渲染日志](../logs/v0.3.5/20261013T214930_701266_pdf_render.log)、[最终复核日志](../logs/v0.3.5/20261013T215008_802109_pdf_verify.log)。',
'- [最终目标 PDF](../../results/V7_Maxwell_Debye_PML/V7_global_energy_副本.pdf)。原始 V7 md/tex/pdf、路线图、模型合同和依赖锁文件哈希全部保持。','']
file.write_text(s+'\n'.join(out))
print('追加PDF账本：10项证明、5处说明、4个修改页；历史保留。')
