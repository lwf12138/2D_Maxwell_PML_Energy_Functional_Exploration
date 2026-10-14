# v1.0 最终语义验收（2026-10-14）

用途：检查命题及结构字段，不以 `#print axioms` 代替数学范围审计。正式类型输出见本目录最新 `*_type_review.log`；当前源码快照见 `source_snapshot.json`。本轮复用前轮已经成立的精确 Poincaré、标量指数核、Cᵏ 规范化和原辅助变量控制。

## 真实基线

`baseline_20261014T173547.json` 与 `logs/v1.0_completion/source_snapshot.json` 的正式源码差异为空。原论文 md/tex/pdf、模型合同、路线图和三个锁文件保持哈希不变。旧验收 `verified_partial_completion` 保留；本轮不回写其状态或文档哈希。前轮尚缺一般连续代表和原 (10.2) 全族，本轮新增真正证明及调用。

## 六条关键连接

| 原要求 | 当前声明（统一省略 LeanPML. 前缀） | 实际输入、输出与调用 |
|---|---|---|
| 一维弱导数的积分原函数表示 | `Analysis.ae_eq_integral_primitive_of_weak_derivative`、`exists_regional_lipschitz_representative` | 对所有内部 C∞ 紧支测试的弱导数等式；以零积分测试的紧支原函数、分布零导数为常数、真实 AC 积分分部证明 f=a.e.常数+∫d；有界 d 给 Lipschitz。无“存在连续代表”字段。 |
| 二维分离→一维→闭区间代表 | `PML.separated_weak_derivative_x/y`、`RawWeakRegionalAbsorption.representatives` | 归一化非负横向测试与 Fubini，取得真实一维弱导数；连续代表保持闭区间非负/幅度。区域弱导数仍由测试定义；不假定普通可导。 |
| 换代表不换原问题 | `rawSpatial_ae`、`weighted_spaces_eq`、`energy_integral_original`、`OriginalInterval.changeCoefficients` | 乘法算子、加权闭子空间/恢复映射、实际密度积分一致；真实八条方程通过算子相等搬运。原 fields、历史、PEC、时间条件不变。不是给原函数强加全轴物理界。 |
| 最终新入口 | `OriginalInterval.main_energy_GeneralWeakCk`、`main_energy_GeneralWeakJet` | 原始区域弱系数+原八式+初始兼容+初始实际加权元素+材料/精确阈值；证明内构造代表及有限区间分析对象。SharpEnergyConclusions 为输出。 |
| 原 (10.2) 全族与原阈值 min | `Examples.OriginalPower.absorption`、`absorption_branches`、`represented_profiles`；`Rectangle.ParameterCertificate.original_threshold_exact` | m≥2、0<ηx,ηy≤1/512 的原剖面；技术截断只改变域外值，AC 积分分部给真实弱导数。原 c*=π²/1152 精确相等，不只是 c≤c*。 |
| 新入口的实际调用 | `Examples.GeneralWeak.static_main_call/static_ck_call/static_energy_positive/static_energy_constant/static_dissipation_zero`、`original_profile_main/four_branch_main` | 非零静态原八式解实际调用；正能量恒定，内部耗散零；原剖面全族与四种（含不对称）分支调用。原剖面调用用零解，只作合法系数入口证书，未宣称非零演化存在。 |

## 输入结构逐字段核对

- `RegionalBounded`：可测实际代表及区域幅度界。`RegionalWeakCoefficient`：值及两弱偏导均区域有界，以全部内部测试函数配对绑定。`SeparatedRegionalWeakCoefficients`：域内值依赖 x 或 y，横向弱导数零为已证结果。它们是 W¹,∞ 的具体有界代表/分布定义，不是仅命名的抽象类型；域外零延拓只用于 L² 乘法。
- `RawWeakRegionalAbsorption`：上述数据、c/S 及 0<c、0≤S≤c/4、闭坐标区间的 0≤p,r≤S；无连续性字段。物理幅度只要求矩形对应坐标区间。Lipschitz 代表在域内 a.e. 与这些实际代表一致；闭端点由连续性与 a.e. 幅度得到。
- `OriginalInterval`：八个 L² 原场、真实导数数据、E 的 H₀¹ 图、旋转磁通量的 H(div) 图、初始 u₀/q₀，闭区间连续与空间识别，内部 `OriginalAt` 八式，只有 t=0 的五个初始兼容。没有全时段兼容、耗散或能量条件。
- `V7ClosedCkCore`：u∈C²(H₀¹)∩C³(L²)、P∈C²(L²)、λ∈C¹(H(div))；均为实际 `ContDiffOn`。没有 OriginalJet 字段。u 是实际历史。φ 的初始 WeightedL2 成员与物理恢复相等另外给出；其历史及所需加权求导由真实演化取得，有限范数本身不被解释为 C²。
- `V7TimeRegularity.flux_second` 从已证邻域空间等式、辅助演化、连续线性坐标及系数乘子求导得到 λ_tt。新 Cᵏ 入口不要求调用者传入 λ_tt。
- `SharpEnergyConclusions`：图界、HasDerivAt 与精确剩余耗散、单调、初值界、IntervalIntegrable、积分平衡和输入原 E/H/P 控制，全部在结论侧。`SharpOriginalAuxiliaryBounds` 同样是输出，Z1/Z2/Qx/Qy 明确为 `O.fields` 的坐标。
- `CompatibleLift`：同一实际原状态的重构与空间成员条件；不含唯一性或能量等式。`historical_energy_independent_GeneralWeak` 与 `twoLayerEnergy_independent_GeneralWeak` 用本轮已构造连续代表调用已证规范唯一性。相等为 L²/弱图/加权商类，不读取指定点值。两层同源由原解路径提供，静态唯一性定理不把任意两状态称为同源。

## (6.6)、端点与 T=0

正长度入口只在 (0,T) 要求原八式和普通 HasDerivAt。闭区间 Cᵏ 使用 mathlib 的真实 `ContDiffOn`；`canonicalInterval` 将 E/P 的端点导数槽选为 `derivWithin`，内部由导数唯一性与旧槽识别。原 fields 不变，闭端点比较和积分平衡不额外输入端点 PDE 或能量导数公式。这里没有全轴 C∞ 或全轴 PDE 假设。

T=0 时单点 Cᵏ 不决定任意导数槽。`main_energy_GeneralWeakJet` 使用真实 jet 接口和 `DegenerateJetCompatibility`（只对 T=0 生效的初始极化、两个空间导数层兼容），并由 `auxiliary_initial_GeneralWeakJet` 给原辅助变量控制。这表达一个合法图状态/实际解限制到单点；不宣称任意单点导数数据自动相容。新静态调用包含 T=0。这个分支语义是显式保留的初始数据条件，不是未证分析接口。

论文 (6.6) 的正则性是充分条件、不是适定性结论。当前 Cᵏ 入口使用其中 u/P/λ 条件及原演化；φ 的初始加权成员和演化给实际历史、成员及所需导数。旧 jet 入口仍可单独使用，但它的较强槽字段不是新正长度主定理的额外假设。

## 原系统与 primitive、历史和记忆

原向 primitive 复用 `WeakPrimitiveSystem` 中原八式→五不变量→兼容→primitive 的证明；反向 `primitive_to_original_WeakOn` 在实际 H₀¹/H(div) 路径、邻域极化约束、真实时间导数下逐条恢复八式，μ≠0 由材料正性给出。两个方向均为内部时间的方程对应，零迹在正确标量空间；无磁法向/磁散度条件。反向 primitive 极化约束是该系统的方程输入，不是把原解全时段兼容预设。

(5.7) 复用 `dampingKernel_eq_scalarExpMultiplier`、`scalar_memory_both` 及两方向 physical 公式；新系数经换代表仍是同一乘法算子与加权空间，故这些已证公式直接适用。等式在每个时刻的空间商类/该时刻 a.e. 意义，不交换成共同零测集上的全时间点态等式。(5.8) 及 φ_t/时间层估计复用 `WeightedMemoryBound`、`AuxiliaryWeightedEvolution`；成员保持未预设全时段成员，也未从有限范数推出任意 C²。

## 常数和回归

采用已证 $C_P^2=(\pi^2/L_x^2+\pi^2/L_y^2)^{-1}$、$K=8\mu(\varepsilon+2\kappa)C_P^2$。单位方形 ε=κ=τ=μ=1 时 $C_P^2=2/\pi^2$、$K=48/\pi^2$，$c_*=\pi^2/1152$，$c=1/128$、$S=1/512$。π 相关比较为严格 Lean 实数证明。保守 CP=2Lx 版本及旧实例原样保留，参数没有混用。

原 (10.2) 的 `extension` 在计算域外截断至有限 Lipschitz 值；`extension_eq_profile` 证明整个闭坐标区间不变。这不要求原原式剖面全轴有界，也不把分段多项式称为 C∞。非恒定代表调用 `representative_nonconstant` 验证代表在0和3/4不同。

旧不兼容增长族由初始磁辅助关系排除，未加磁场约束。单层失败仍只否定已定义候选。所有旧证明模块哈希不变；本轮不重做旧反例。

## ROADMAP 验收矩阵

| 条目 | 数学状态 | 依据/范围 |
|---|---|---|
| v1.0.1 真实弱图、H₀¹闭包、加权零区/嵌入、有界乘法 | 完成，复用 | WeakSpaces、SmoothWeakClosure、WeakCompactApprox、WeightedL2/Operators、WeakZeroProduct |
| v1.0.2 Green/Poincaré、弱分离系数、(5.7)/(5.8)、规范唯一 | 完成 | 本轮补连续代表；精确常数/标量核/传播/提升证明接入，无未证分析字段 |
| v1.0.3 原系统→同源两层→(6.7)–(6.10)、(8.4)–(8.8) | 完成 | 新 GeneralWeakCk/Jet、初值辅助界、提升选择无关；T=0 采用明确合法图状态语义 |
| 第15节证明可信与命题范围 | 最终工程证据见 acceptance.json | 类型字段已逐项核对；标准基础公理允许；无能量目标输入 |
| 第16节可复现交付 | 最终工程/PDF证据见 acceptance.json | 真实失败/修复日志保留；隔离重编本项目，精确依赖缓存复用 |

不属于本轮：一般解存在唯一性、严格或指数衰减、任意幅度、可选 Laplace/V6 对照、R/D 分支。没有把本轮主线困难移动到这些可选项。最终“完成”须再由 `acceptance.json` 确认当前源码的构建、审计、隔离及 PDF 检查均通过。
