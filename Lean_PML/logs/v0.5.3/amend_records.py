# -*- coding: utf-8 -*-
from pathlib import Path
import hashlib
from datetime import datetime

root = Path(__file__).resolve().parents[2]
p = root / 'README.md'
s = p.read_text().replace('通过；覆盖前三阶段当前源码', '通过；覆盖本轮三阶段当前源码')
s = s.replace('$$\\frac{N_0^2+KN_1^2}{4}', '图平方界及能量比较在 $[0,T]$；以下导数恒等式与定量耗散下界仅在 $t\\in(0,T)$。\n\n$$\\frac{N_0^2+KN_1^2}{4}', 1)
p.write_text(s)
p = root / 'docs/source_inventory.md'
p.write_text(p.read_text().replace('`FullDomainProfile.profile`', '`LeanPML.Examples.FullDomain.profile`'))
p = root / 'docs/pdf_formalization_marks.md'
s = p.read_text()
categories = {
    '§2.3 命题2.2与H=t∇ψ未编号公式': '实际古典场、空间积分与范围反例',
    '§5.2数据类的§11.1启动子族': '初始场证书、真实初始导数与空间成员；非区间解',
    '定理6.1及(6.7)–(6.10)': '具体光滑原模型先验定理',
    '(7.5)已证矩形Green在原场入口的使用': '已证具体分析接口的调用说明',
    '(7.6)–(7.8)能量律的具体总装': '实际L²/加权空间值时间求导',
    '(9.5)–(9.7)既有估计的具体实例化': '既有空间估计与真实导数的具体接入说明',
    '§10原(10.1)/(10.2)旁的C∞替代实例': '实际光滑函数、精确参数及系数证明',
    '§11.3非零静态模态未编号公式': '实际非零古典静态解、空间成员与主定理调用',
}
for label, category in categories.items():
    s = s.replace(label + '<br>', label + '<br>类别：' + category + '<br>', 1)
p.write_text(s)
p = root / 'logs/v0.5.1/semantic_review.md'
s = p.read_text()
if '最终计数更正' not in s:
    s += '''

## 2026-10-14 最终计数更正（保留上方原记录）

此前两处“20字段”是人工误计数；按最终实际类型逐字段数为19，D/R及材料/T是类型参数，不是额外字段。独立复核与最终类型扫描一致。history_regular含八个原场沿时间连续和实际u历史联合光滑；加权正则性含三层成员及前两层曲线连续可微。早期计数错误不影响证明类型或范围，未改任何数学源码。
'''
    p.write_text(s)

sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
s = '# v0.5 最终文档与假设检查\n\n时间：' + datetime.now().astimezone().isoformat() + '''。root 与独立 geometry 代理实际逐段读过主入口/报告和新增清单。

- 主结构实际19字段：参数与对象、原式、边界、初值及强正则性；输出包与输入包分开。没有Green/Poincare/耗散/单调等目标输入。
- history_regular包括八个原场时间连续，实际u历史联合光滑；UniformTimeJet和WeightedJetRegular区别已经报告列明。
- 一般定理保留更强正则性；具体实例由构造证明成员与导数，不将非零数据说成一般存在性。
- 报告、源码与日志619/683/740一致，最后全工程覆盖全部。
- 保守CP2Lx、K/c*一致；profile正式名称已纠正为LeanPML.Examples.FullDomain.profile，mathlib平坦函数来源同为SmoothTransition.lean。
- README明确导数/闭合仅内部，闭区间图界/比较包含端点与T0初始兼容。
- 静态例wy3、真正主定理调用；增长例全未来量词、真实积分与不兼容界限准确。单层只针对原候选。
- PDF八页检查通过，6勾+2说明；具体类别、剩余范围和完整声明逐条记账，未给原π/传播/弱范围/存在唯一勾。
- 原20字段人工误数在早期记录后追加更正，不覆盖历史；未涉及证明修改。

## 当前记录哈希

'''
for f in ['README.md', 'PROGRESS.md', 'reports/smooth_theorem.md', 'docs/source_inventory.md',
          'docs/theorem_inventory.md', 'docs/claim_ledger.md', 'docs/pdf_formalization_marks.md']:
    s += f'- `{f}`：`{sha(root/f)}`\n'
(root / 'logs/v0.5.3/final_documentation_review.md').write_text(s)
print('Final scope/count/name review recorded; Lean sources unchanged.')
