# v1.0_completion 语义验收（2026-10-14）

本记录区分已核验的新版本与 ROADMAP 全部原文对齐。后者仍未完成，不能以构建成功替代。

## 基线与实际新增

基线 `baseline_20261014T162626.json` 与 closeout 源码快照逐项一致；本轮复用 λ_tt 推导、原 Z/Q 控制、弱反向八式、算子指数历史和全部旧回归。旧 Lean 模块没有修改；新增数学模块及正式导入/审计另行存档。原 V7/合同/路线图/锁文件哈希复核见最终验收。

|工作单元|实际结果|调用链|
|---|---|---|
|一般分离 W¹,∞ 连续代表|**未完成**；没有删除 p_continuous/r_continuous|现有 WeakRegionalAbsorption 仍有独立区域连续代表输入|
|(5.7) 标量指数核|**完成**：连续函数代数同态、连续性、映射指数、恢复算子与 Bochner 积分交换|dampingKernel_eq_scalarExpMultiplier → auxiliary_scalar_memory → OriginalInterval.scalar_memory_both；physical_x/y 给原 L² 场|
|(5.1) 精确常数|**完成**：一维平方展开/FTC → 紧支切片 → Fubini → H¹ 图闭包|weak_sharp_poincare → sharpWeakPoincareDomain → sharpFiniteProblem → main_energy_estimate_SharpWeakOriginal|
|第10节数值|**完成 (10.1) 阈值证书**：CP²=2/π²、K=48/π²、三条严格小量及 S 界|original_parameters_threshold；非零静态 sharpParameters 调用。未新建 (10.2) 任意 m 的 W¹,∞ 代表构造|
|(6.6) Cᵏ 充分性|正长度区间的连接**完成**，不宣称任意单点时间数据等价于给定解的限制|V7ClosedCkCore → canonicalInterval → ClosedCkRegularity → V7TimeRegularity → OriginalJet → main_energy_RegionalSharpCk|
|原变量控制|精确 CP 下 (6.10)、(8.4)–(8.8) **完成**|SharpEnergyConclusions.physical；SharpOriginalAuxiliaryBounds 的 Z/Q 是 O.fields 中原变量|
|规范选择|复用既有 CompatibleLift.twoLayerEnergy_independent，对任意 K 有效|需区域连续代表，不能将其适用范围扩大为代表选择已证|

## 第一个仍未闭合的数学接口

给定一维开区间 I=(a,b)、有界可测 f,d，且对每个 η∈C_c∞(I) 有
∫ f η′ = −∫ d η，证明存在 c，使 f(x)=c+∫ₐˣ d(s)ds a.e.，从而得到闭区间 Lipschitz 代表。
这必须再与现有二维分离 RegionalWeakCoefficient 的测试关系连接，保持幅度与 a.e. 乘法/权重一致；当前未实现。

本轮核查了两条可行路线：
1. 原函数路线：先证明积分原函数具有该弱导数，再证明弱导数为零的局部可积函数 a.e. 为常数。后者需零均值测试函数的紧支原函数构造。现有 `ae_eq_zero_of_integral_contDiff_smul_eq_zero` 只在所有测试配对为零时适用，不能直接把含 η′ 的条件当作该输入。
2. 卷积路线：区域紧子区间上用弱导数控制光滑化的一致 Lipschitz 常数，再取极限和闭端点延拓。已有 H₀¹ 紧支光滑化模块证明的是 L² 图逼近，不能直接当成所需的局部一致梯度界/代表选择。

固定 mathlib 的 `AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero`
位于 `Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean:170`，
**先要求**绝对连续；它不能从当前分布弱导数输入自动给出 AC。
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` 位于
`Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean:219`。
没有为绕过此缺口新建“存在连续代表”的假设字段。该缺口仍属于 v1.0 主线，不改列可选任务。

## 最终输入逐项审查

- 空间：整个非退化矩形，真实 H₀¹ 三槽 L² 图闭包、H(div) 图。普通/加权空间均为 a.e. 商类。
- 系数：区域分离弱导数、非负/幅度限制、时间不变；推荐 A 入口还要求区域连续代表（上列未闭合差异）。内部零延拓只作乘法/积分，不作跨边界弱导数。
- 原场：OriginalInterval 八个实际 L² 路径及真实内部 OriginalAt；E 的 H₀¹、旋转磁通量的 H(div)；初始五兼容。原场闭区间连续为明确正则性输入，不藏在结论中。
- 正长度 Cᵏ 入口：历史 u 的 C²(H₀¹)/C³(L²)、P 的 C²(L²)、λ 的 C¹(H(div))。函数与图导数由 ContDiffOn/derivWithin/HasDerivAt 连接。φ 的初始加权成员仍输入；传播、所需加权求导由旧原演化结果提供，不以有限范数直接声称 C²。
- 正长度端点：canonicalInterval 仅选取 E/P 的区间导数槽，原八场逐时刻相同；内部原式由导数唯一性保留。新入口无需额外端点槽识别，不要求端点 PDE。
- T=0：使用 main_energy_estimate_SharpWeakOriginal + OriginalJet + DegenerateJetCompatibility。不能从 Cᵏ 在单点的空内部信息推出任意初始导数兼容；因此未将正长度 Cᵏ 入口伪装为无需初始 jet 的统一 T≥0 入口。
- 无目标能量律、耗散非负、单调性、初值界、Green、Poincaré 输入。空间接口由已证明的弱 Green 与本轮精确 Poincaré 填入。
- 无磁场法向/散度附加约束；无吸收正下界；不删除零区；没有把能量权重当作普通 L² 有界乘子。
- 同源两层来自实际历史和原场导数。真实 λ_tt 沿用已证辅助演化与图投影求导。
- 输出包括准确定量剩余耗散、FTC 的实际 IntervalIntegrable、闭区间 AntitoneOn 和原场控制。不是一般存在唯一性、严格或指数衰减。
- 原文 (5.7) 的固定差值系数放在时间积分内；已证的是每个固定时刻的空间商类等式，不交换 a.e./时间量词，不主张同一零测集上所有时间的点态等式。

## 调用与回归

非零弱静态原解：sharp_main_call（含 T=0）、sharp_nonzero_static_regression（正能量、常值、零耗散）、canonical_main_call（实际 Cᵏ 新入口）。非恒定空间剖面调用 nonconstant_profile_scalar_kernel，核验一般乘子不是只在常数上证明。旧全零/双边层/角层、非相容增长及单层失败回归仍进入默认构建和全部审计。

精确 CP 主入口没有修改旧保守入口及历史证书。第10节证书核验阈值，不自动核验原文 min 的最小分支显式等式，也不自动宣称 (10.2) 全族构造已实现。

## 验收结论

新增已证数学连接可独立交付；ROADMAP v1.0 原文逐项对齐仍不完成。一般弱系数代表选择、与该选择相连的最终区域入口仍是首要剩余任务。正长度 (6.6) 充分性已建立，T=0 的独立初始兼容范围继续明确保留。
