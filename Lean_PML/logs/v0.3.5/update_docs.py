from pathlib import Path
import json
root=Path.cwd();a={s:json.loads((root/'logs'/s/'acceptance.json').read_text())for s in ['v0.3.4','v0.3.5']}
p=root/'README.md';s=p.read_text()
s=s.replace('**本轮 v0.3.4–v0.3.5 正在分别验收。** 最终状态以本页下方的实际构建、公理审计和范围记录为准。','**v0.3.4、v0.3.5 已分别通过验收。** 本轮新增 53 条正式定理，最终审计共 369 条；以下结论均有列明的分析接口范围。')
validation=['| 阶段 | 实际默认构建 | 独立公理审计 | 新定理／审计总数 |','|---|---|---|---|']
for stage,e in a.items():
 validation.append(f"| {stage} | [lake build]({e['build']}) | [lake env lean Audit.lean]({e['audit']}) | {e['new_public_theorems']}／{e['audited_declarations']} |")
validation+=['','四条命令退出码均为 0。每个同名 `.json` 保存命令、工作目录、完整输出文件名和退出码；[v0.3.4 验收](logs/v0.3.4/acceptance.json)与[v0.3.5 验收](logs/v0.3.5/acceptance.json)登记源码哈希。审计只出现 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx` 或自定义占位公理。最终阶段重新检查整个工程和全部旧审计。', '',
'编译失败、修复及检查失败均保留：包括固定版本 FTC 编译产物缺失、一次并行开发导致暂时缺失 `.olean`，以及审计注册脚本因前缀重名漏列 `debye_absorption`。覆盖检查拦下漏项后，改为逐行精确匹配、补审并重跑构建审计；数学结论未放宽。', '',
'新增正式模块须加入 [LeanPML.lean](LeanPML.lean) 的导入链，并在 [Audit.lean](Audit.lean) 加入完整定理名的 `#print axioms`，两者都在默认 Lake target 中；不要仅创建一个未导入的文件。']
s=s.replace('VALIDATION_LINKS','\n'.join(validation))
s=s.replace('PDF_SUMMARY','[指定 PDF 副本](../results/V7_Maxwell_Debye_PML/V7_global_energy_副本.pdf) 保持 18 页和原 168 项批注，新增 10 个带范围红勾及 5 条说明。第 10 页对应 (6.8)、(6.9)，第 13 页对应 (9.1)，第 14 页对应 J 的可积/非负子结论、(9.3)–(9.7) 及剩余耗散；第 12 页只追加旧状态说明。四个修改页已逐页渲染检查，无正文遮挡、裁切或缺字；既有待完成文字保留，并说明历史属性。\n\n[PDF 备份与哈希](logs/v0.3.5/pdf/backup.json)、[标注定位及证明证据](logs/v0.3.5/pdf/annotation_plan.json)、[结构验证](logs/v0.3.5/pdf/verification.json)、[逐页视觉检查](logs/v0.3.5/pdf/visual_review.json)均已记录。')
p.write_text(s)
p=root/'PROGRESS.md';s=p.read_text();assert not s.startswith('# 2026-10-13：v0.3.4')
new='''# 2026-10-13：v0.3.4–v0.3.5 分别验收完成

用途：登记第 9 节空间估计、耗散闭合及有限区间条件性主定理。下方全部历史原样保留，旧“当前/下一阶段”指记录当时。本轮止于 v0.3.5，未实施 v0.4，没有提交、推送、依赖更新或新增 reading_guide。

## v0.3.4：已完成

新增 [GradientControl.lean](LeanPML/PML/GradientControl.lean)，18 条正式定理。

- (9.2)：实际 L² 的有界 θ 乘子及 J 内积定义，密度可积、积分对应与非负性；空间约束把 Λ−ψ 接到梯度。
- 零区 θ=1/2、ψ=0 a.e. 给 J 密度为梯度平方和，保留空间耗散，不删除物理区。
- (9.3)：实际 fieldSpatialDissipation 同时控制 (c−S)J 和 3cJ/4。
- (9.4)：真实原层辅助演化、SameSourcePath 与时间/梯度接口推出两方向关系。
- (9.5)：系数分配、三项平方估计、a.e. 场等式、可积性和积分序关系得到准确常数 3、3S²；全零吸收、两个不对称边层与不对称角层均有正式调用。

VALIDATE034

## v0.3.5：已完成

新增 [DissipationClosure.lean](LeanPML/PML/DissipationClosure.lean)（14 条定理）和 [MainAbstract.lean](LeanPML/PML/MainAbstract.lean)（21 条定理）。本轮合计 53 条新定理。

1. 实际单层积分下界和 (9.1)，其中 Debye 关系从邻域兼容及真实导数得到，未新增教学子系统方程。
2. (9.6) 使用同一迹核的 Poincaré、(9.3)、(9.5) 与原阈值；正式证明 KS²≤Kc²/16≤1/16≤1。非空空间载体仅用于从0≤p≤S取得S≥0，矩形载体ℝ×ℝ自动满足，不排除零吸收或零测度。
3. (9.7) 从真实 κE_t=P_t+τP_tt 得到平方分项界，再分别使用两条材料阈值。
4. (6.8) 精确定量闭合：空间耗散支付 E 负项后剩一半；Debye 耗散支付 E_t 负项后剩 μτ/(4κ) 平方项；由剩余项证明非负，随后结合原条件性能量律给真实导数非正。
5. 有限闭区间单调性、0≤E₇(t)≤E₇(0)，保留 (6.7) 及七类原/辅助变量重构控制并接到初始能量。
6. 实际时间积分平衡单独用固定 mathlib FTC 证明，能量连续与耗散可积都从实际普通/加权场路径推出。

VALIDATE035

两个阶段完整审计仅出现标准 `propext`、`Classical.choice`、`Quot.sound`，没有 sorryAx。源码、默认导入与每条新定理的审计覆盖已经核对。v0.3.5 最终构建包含 v0.3.4 全模块，没有修改旧数学模块。

## 最终定理假设与时间范围

`FiniteIntervalProblemConditional` 的输入只包括：T≥0；Ioo 0 T 上同源真实普通/加权导数；原层 primitive 演化；受限梯度/散度、Green、迹和时间交换接口；两层 Icc 0 T 上分量连续；闭区间静态极化、空间和同一迹核约束。一般 Poincaré 单独列明，参数包只有原阈值及正性。没有目标梯度界、耗散符号、单调性或积分平衡字段。`PhysicalInitialControlBounds` 是结论包，不是输入条件。

- 真实能量导数、同源梯度估计、定量耗散下界在 (0,T) 使用内部演化。
- 静态双边界、能量非负、单调性及初值控制在 [0,T] 成立。
- 积分平衡额外要求 second.R（内部实际为 P_tt）在闭区间 L² 连续；由此证明 D₇ 连续和 IntervalIntegrable。单调性无需这项附加条件。
- T=0、t₁=t₂、t₁=0、t₂=T 都保留，没有端点双侧导数；不能用 T=0 的空内部条件推出端点兼容或耗散正性。

以上输入另经人工语义审查；仅通过 #print axioms 不足以发现普通结构字段中的循环假设。逐项内容追加于 [定理清单](docs/theorem_inventory.md)、[结论账本](docs/claim_ledger.md)。学习内容集中在 [README](README.md) 和代码中文注释。

## 失败、修复与来源记录

实际日志保留固定 FTC 模块缺少编译产物后的补编译、系数/积分/序关系 API 修复、一次并行期间短暂缺失 GradientControl.olean，以及审计覆盖检查拦截的一条前缀重名漏项。后者修改注册工具为完整行精确匹配，补列 debye_absorption 后重新构建与审计。没有修改锁文件、降低常数或通过占位证明填补缺口。

[来源复核](logs/v0.3.4/source_review.md)、[入场快照](logs/v0.3.4/source_snapshot.json)、[前阶段证据复核](logs/v0.3.4/previous_review.json)确认原 V7、模型合同和固定配置未变。路线图部分复选框已勾选而状态文字仍旧，本轮保持路线图原样，以源码和真实验证为准。

## PDF 标注及最终保护检查

通过全部构建/审计后，才编辑指定副本。18 页、168 项旧批注及可选正文全部保留；实际/印刷第 10、12、13、14 页新增 10 个带范围矢量红勾和 5 条说明，最终 183 项批注。

- 第 10 页：(6.8) 条件性精确耗散闭合，(6.9) 条件性单调性及积分平衡；定理 6.1 只说明抽象接口下核心闭合。
- 第 12 页：只更新历史状态说明，不重复叠加旧红勾。
- 第 13 页：(9.1) 条件性耗散下界。
- 第 14 页：J 的可积非负子结论，(9.3)、(9.4)、(9.5)、(9.6)、(9.7) 以及未编号剩余耗散下界；J 定义只标说明。
- 具体矩形分析、原 PDE 对应和解存在唯一性没有完成勾；既有旧待完成标记保留，旁边/页首说明其历史范围。

[PDF 账本](docs/pdf_formalization_marks.md)、[新备份与哈希](logs/v0.3.5/pdf/backup.json)、[证明及定位计划](logs/v0.3.5/pdf/annotation_plan.json)、[结构验收](logs/v0.3.5/pdf/verification.json)、[逐页视觉验收](logs/v0.3.5/pdf/visual_review.json)均保留。四个修改页用 Poppler 150 dpi 重新渲染、逐页查看，无遮挡、裁切或缺字。最终保护、导入、审计、历史与链接检查见 [final_checks.json](logs/v0.3.5/final_checks.json)。

## 下一阶段（未实施）

v0.4.1：具体矩形 Domain、Fields、Boundary，建立全矩形上的光滑场、坐标导数、四边迹及 PEC/零迹表示。之后再兑现 Green/Poincaré、时间微分交换、完整原模型映射及提升唯一性。本轮已经闭合的是条件性先验能量定理；没有证明具体原 PDE 全形式化、解存在唯一性或严格衰减。

---

'''
for stage,key in [('v0.3.4','VALIDATE034'),('v0.3.5','VALIDATE035')]:
 e=a[stage];part=f"- [实际默认构建]({e['build']})／[独立公理审计]({e['audit']})：退出码均为 0，审计 {e['audited_declarations']} 条。\n- [命令、哈希与阶段验收](logs/{stage}/acceptance.json)／[新增定理索引](logs/{stage}/new_theorems.json)。每个日志旁同名 `.json` 记录真实命令、目录与退出码。"
 new=new.replace(key,part)
p.write_text(new+s)
print('README已完成状态/学习/日志链接；PROGRESS追加两阶段验收，旧历史保留。')
