# Lean PML 结论与验证状态表

核查日期：2026-10-06（Asia/Shanghai）。阶段：v0.0.1。来源编号、绝对路径与版本哈希见 [材料来源清单](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML/docs/source_inventory.md)。

目前的起点是：V7 提供一个带明确条件的二维 Maxwell–Debye PML 纸面先验能量定理；旧 PML Lean 文件主要提供辅助代数引理；外部标量工程已有真实函数求导与单调性源码。本轮清点不将这些证据合并成“V7 已通过 Lean 验证”。

## 状态怎样理解

| 标记 | 含义 |
|---|---|
| 本轮源码确认 | 已读取声明或实现，能够说明它表达的内容；本轮未运行编译器 |
| 纸面主张 | 来源中有定理或推导；本轮没有重新完成全部数学审稿或形式化 |
| 历史通过／历史失败 | 已有文件记录过去的结果，保留其日期、范围和环境；本轮未复跑 |
| 待形式化 | 在本轮核对的材料中没有对应的完整 Lean 证明链 |
| 未完成范围 | 文稿明确未证明，不能因较弱结果存在而扩大结论 |

“有源码”“历史通过”和“当前编译通过”分别记录。本轮不存在“当前编译通过”的新 Lean 结果。

## 已有 Lean 与计算证据

| 编号 | 结论或对象 | 来源与本轮确认 | 已有运行证据 | 尚缺什么 |
|---|---|---|---|---|
| C01 | 标量 ODE 的能量非负、真实求导、单调不增及初值界 | [T1](/Users/wcli/Desktop/资料/graduate_student/博/Lean_study/ScalarDissipation/ScalarDissipation/Energy.lean)：`hasDerivAt_energy`、`energy_deriv_nonpos`、`energy_antitone`、`energy_bound` 等；本轮源码确认 | [T7](/Users/wcli/Desktop/资料/graduate_student/博/Lean_study/ScalarDissipation/README.md) 记载 2026-09-23 构建及公理审计通过；本轮未复跑 | v0.0.3 重新验证；v0.1.1 增加仅在闭区间连续、内部满足导数假设的版本，处理端点与 $T=0$ |
| C02 | 非零指数解及标量能量定理的调用 | [T2](/Users/wcli/Desktop/资料/graduate_student/博/Lean_study/ScalarDissipation/ScalarDissipation/Examples.lean)：`explicitSolution_hasDerivAt`、初值和能量界；[T0](/Users/wcli/Desktop/资料/graduate_student/博/Lean_study/ScalarDissipation/ScalarDissipation.lean) 已导入该文件 | T7 的历史记录；本轮未复跑 | 与新工程对接并按实际构建验收；不据此声称一般 ODE 适定性 |
| C03 | V5 六条辅助定理 | [S6b](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/verification/algebra/VariableCoefficientBaffet.lean)：四条有理数代数恒等式、实数完成平方与标量吸收不等式；本轮源码确认 | [S5](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/results/lean_core_theorem_coverage_review_20260924.md) 记录过去退出码 0；[H3](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/results/v5_variable_coefficient_baffet/verification_outputs.md) 同时保留早期环境失败 | 尚未连接实际 PDE 解、空间积分和时间能量；`Pt` 等名字不等于导数定义 |
| C04 | V6 十条辅助定理 | [S6a](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/results/v6_tex/NonlocalMemoryStrictPML.lean)：Schur 吸收、标量非局部代理展开、二元二次型及条件零反射等；本轮源码确认 | [H2](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/results/v6_tex/verification_outputs.md) 记录 2026-07-14 退出码 0；S5 另有历史通过叙述 | 实际函数空间、PDE 求导、边界通量及整体状态控制仍未形式化；`Yp = Y0` 是相应零反射引理的输入 |
| C05 | 旧 `NewEnergyFunctional.lean` | [L2](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/verification/algebra/NewEnergyFunctional.lean) 文件存在；本轮登记路径与哈希 | S5 记录退出码 1，类型类／实例及未关闭目标问题 | 不标为当前通过；是否修复需单独任务与真实编译 |
| C06 | V7 的符号与参数检查 | [S7](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/results/V7_Maxwell_Debye_PML/verify_v7.py) 含空间、电、Debye 局部代数、约束消元、磁辅助关系及参数例子；本轮读取脚本 | [H1](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/results/V7_Maxwell_Debye_PML/verification_output.txt) 保留成功输出；本轮未运行 | 精确恒等式与浮点参数检查需区分；脚本未覆盖完整空间分析、耗散闭合和时间单调性 |
| C07 | 工作流报告被标为成功 | [H4](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/results/v6_tex/VERIFICATION_STATUS.json) 含 `ok: true` 和 `goal_success`，目标是 V6 报告 | 历史工作流状态 | 不能作为整个 PDE 主定理的 Lean 证明或独立同行评审 |

S6b 与 L1 的当前文件哈希相同；C03 只计一组定理。T3 的 `#print axioms` 命令用于追踪公理依赖，本轮没有执行；即使以后输出没有 `sorryAx`，也仍要审查是否把待证结论直接写进了假设。

## V7 主证明链当前处于哪一层

下表均以 [V7 正文](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/results/V7_Maxwell_Debye_PML/V7_global_energy.md) 为纸面来源，[V7 自审](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/results/V7_Maxwell_Debye_PML/proof_audit.md) 为辅助定位。状态“待形式化”只针对本轮可访问、已核对的材料，不断言其他未知工程中不存在实现。

| 编号 | 目标结论 | 纸面位置 | 本轮状态 | 路线图对应工作 |
|---|---|---|---|---|
| P01 | 原八变量与 primitive 系统的时域对应、五个初值不变量 | §2，命题 2.1，式 (2.4)–(2.6) | 纸面主张；S7 有部分磁辅助代数检查，真实时间／场层 Lean 证明待完成 | v0.1.3、v0.4.4 |
| P02 | 兼容初值、零吸收区保持、加权空间与提升唯一性 | §§5.1–5.3 | 纸面主张；不能把普通命名变量当作已构造的函数空间 | v0.2.1、v0.3.1、v0.4.4、v1.0 |
| P03 | 两层能量的实际定义及导数恒等式 | 式 (6.2)–(6.4)、§7，尤其 (7.8) | 纸面主张；局部符号检查不替代积分求导、Green 和两层边界处理 | v0.2、v0.3.2、v0.4.2–3 |
| P04 | 能量与加权图范数双边估计 | 式 (6.7)、§8 | 纸面主张；旧二元正定引理不构成这条全域定理 | v0.3.3、v0.4、v1.0 |
| P05 | 跨边层梯度估计与两个负项吸收 | §9，式 (9.5)–(9.7) | 纸面主张；尚无对应完整 Lean 证明 | v0.3.4–5，再兑现具体空间接口 |
| P06 | 耗散非负、积分平衡、任意两时刻单调性及原场控制 | 定理 6.1，式 (6.8)–(6.10)，并见 §8 辅助变量控制 | 纸面先验定理；不能称已由 Lean 核验 | v0.3 抽象核心，v0.5 光滑具体版本，v1.0 实际覆盖的 V7 范围 |
| P07 | 非平凡全域吸收剖面与兼容初值例子 | §10、§5.2 | 有纸面构造及部分脚本检查；初值可容许性不蕴含解存在 | v0.5.2 的精确参数与初值证书 |
| P08 | 任意初值增长例、单层候选失败与非零静态模态 | 命题 2.2、§11.1、§11.3 | 纸面结论；需要分别固定量词与解／数据假设 | v0.2.4、v0.5.3 的范围回归与障碍模块 |

## 本阶段必须保留的数学范围

V7 当前纸面主张依赖：

- 原八变量 Maxwell–Debye 系统，材料为正常数，保留 Debye 极化（$\alpha=1$）。
- 整个矩形外边界的 PEC 条件。
- 吸收非负、时间不变、分离依赖，并满足显式小幅度条件；允许零吸收物理区、边层和角层。
- 文中定义的兼容初值及有限加权图范数。
- 已存在且满足式 (6.6) 等要求的足够正则解。

目标结论是**单调不增**，允许等号；能量控制指定加权图范数和原变量。它没有声明与任意裸八变量 $L^2$ 范数等价。

本轮只登记这些限制，尚未完成 v0.0.2 的逐参数、逐量词模型合同。后续应从原方程推出能量律与耗散闭合，不能将这两项作为最终具体 PDE 定理的未证假设。

以下范围仍未完成或不由该结果自动给出：

| 范围 | 状态依据 |
|---|---|
| 任意吸收幅度的一般全域单调能量 | S2 §13 和 S3b 明确未证明 |
| 任意八变量初值统一适用 | 与 S2 命题 2.2 的限定增长例有关；主定理限定兼容类 |
| 完整解存在、唯一和正则性传播 | S2 定理 6.1 后明确是先验定理 |
| 所有非零状态都严格耗散 | S2 §11.3 保留非零静态模态 |
| 空间变材料、任意二维依赖吸收、分数阶系统 | S2 §13 未覆盖；$\alpha=1$ 仍需保留极化 |
| DG／其他真实空间离散与 CN 结论 | 路线图 D 分支，尚未实施 |
| 数值优化得到最优参数或 AI 模型训练经验 | 需 R／A 分支的额外实际成果 |

## 阶段交接

- **v0.0.1：本轮完成材料定位、哈希、分类及状态清点。**
- v0.0.2：未开始。下一步建立 `model_contract.md`、`theorem_inventory.md` 和 `scope.md`，把原模型、最终命题、公式对应与未证接口写清楚。
- v0.0.3：未开始。届时才实测工具链、建立独立工程并记录最小构建与公理审计。
- 本轮没有新增 Lean 定理、编译任何 Lean 文件或复跑 S7；历史成功与失败均按历史证据保留。


## 2026-10-13：v0.3.2–v0.3.3 增量状态（上文保留为历史）

本节以本次真实源码、构建和独立公理审计更新状态，不把 v0.0.1 的“未运行”叙述当作当前结论。

- **P03 / T12、T17、T18：条件性版本已形式化。** 实际普通/加权 L² 路径，从原层 primitive 演化经邻域求导得到导数层，再用明确 Green、时间交换和两层零迹接口，证明单层含边界能量律及 $\mathcal E_7'=-\mathcal D_7$。目标能量律不在模型字段中。具体矩形 Green/迹/交换仍未证明。
- **P04 / T20、T21：条件性图范数界与零分离已形式化。** (8.3)、§8 双边估计及 (6.7) 使用同一状态和参数，从原阈值推出小量条件；依赖显式零迹 Poincaré。零状态保留，没有未经证明的 Norm 实例。
- **P06 / T29：兼容提升重构的原场控制已形式化。** (6.10)、(8.4)–(8.8) 在实际 L² 上保持论文全部常数；不表示任意裸八变量范数双向等价。
- **P05、P06 的耗散闭合与单调性仍未完成。** 没有证明 D₇≥0、(9.5)–(9.7)、(6.8)–(6.9) 的完整结论；正能量和精确能量律并不单独推出单调性。
- **P01/P02 的完整模型等价、提升唯一性，以及 PDE 解存在唯一性仍未完成。** 本轮未把定义或重构自动登记为这些结论。

原文 §8.2 的严格小于在 B_sp=0 时需改用非严格估计；代码已处理，源文保持原样。其他输入与剩余接口详见 [定理清单追加记录](theorem_inventory.md)、[README](../README.md)。

[v0.3.2 构建](../logs/v0.3.2/20261013T095839_225389_lake_build.log)／[独立审计](../logs/v0.3.2/20261013T100104_046897_axioms_audit.log)；[v0.3.3 构建](../logs/v0.3.3/20261013T100156_159842_lake_build.log)／[独立审计](../logs/v0.3.3/20261013T100321_602582_axioms_audit.log)。四条命令均退出 0。v0.3.2 审计 288 条，v0.3.3 审计 316 条（保留旧 263 条，分别增加 25、28 条）；仅标准基础公理。失败及修复过程保存在对应 logs 目录。


## 2026-10-13：v0.3.4–v0.3.5 增量状态（保留全部历史）

本节更新 P05、P06 的**条件性实际空间版本**，不删除上轮“耗散闭合与单调性仍未完成”的历史记录。路线图中的部分“待实现”文字落后于源码和既有勾选；本轮未改路线图，来源版本与差异见 [入场复核](../logs/v0.3.4/source_review.md)。阶段构建与独立审计的实际退出码、完整输出及失败修复记录分别由 [v0.3.4 验收记录](../logs/v0.3.4/acceptance.json)、[v0.3.5 验收记录](../logs/v0.3.5/acceptance.json) 汇总。

| 当前结论 | 实际证据 | 准确范围 |
|---|---|---|
| P05 / T22–T23：J 和跨边层梯度估计 | [GradientControl.lean](../LeanPML/PML/GradientControl.lean)：`fieldJ_integrable`、`fieldJ_eq_integral`、`fieldJ_nonneg`、`fieldJDensity_zero_region`、`fieldSpatialDissipation_ge_J`、`gradient_evolution_Conditional`、`gradient_control_Conditional` | (9.2) 为实际 L² 内积/积分；(9.3) 保留零区贡献；(9.4) 来自原辅助演化和真实同源导数；(9.5) 经 a.e. 关系、可积性及积分序关系推出。不是独立点态分量的矩阵估计 |
| P05 / T24–T26：耗散下界与两类吸收 | [DissipationClosure.lean](../LeanPML/PML/DissipationClosure.lean)：`dissipation7_preliminary_Conditional`、`spatial_absorption_Conditional`、`spatial_absorption_half_Conditional`、`debye_relations_Conditional`、`debye_absorption_Conditional` | 精确验证 (9.1)、(9.6)、(9.7)；原阈值提供材料条件，原幅度提供 KS²≤1/16；Poincaré 使用同一 G.trace 零迹核。κE_t=P_t+τP_tt 从邻域真实求导获得 |
| P06 / T27：定量耗散闭合与非负 | `dissipation7_lower_Conditional`、`dissipation7_nonneg_Conditional`、`energy7_law_and_closure_Conditional` | (9.7) 后未编号下界保留一半空间耗散及 μτ/(4κ) Debye 项；导数恒等式、耗散下界、导数符号分别证明。最终内部结论不预设 D₇≥0 |
| P06 / T28：有限区间单调性与积分平衡 | [MainAbstract.lean](../LeanPML/PML/MainAbstract.lean)：`energy7_antitoneOn_Conditional`、`energy7_integral_balance_Conditional`、`main_energy_estimate_Conditional` | 实际 energy7 在 [0,T] 单调不增；对 0≤t₁≤t₂≤T 有实际 intervalIntegral 平衡。闭区间坐标连续、内部演化；FTC 另用 P_tt 的闭区间 L² 连续性 |
| P06 / T21、T29：接通初始能量控制 | `graphSquare7_initial_bound_Conditional`、`physicalControl_initial_Conditional` | 由已证静态界和新单调性，将 (6.7)、(6.10)、(8.4)–(8.8) 的右端接到 E₇(0)，保持原常数；这是兼容提升下的先验估计 |

表内 Lean 名称的统一完整前缀是 `LeanPML.PML.`。`fieldJ` 定义本身不登记为“证明完成”；其合法积分、代表元无关和非负性分别由上述定理支撑。四种吸收分支均保留，边层实例区分 x/y 的不同方向次序；未增加吸收正下界或 w 本质有界性。

本轮另行审查了普通假设字段，因为公理审计不会自动指出结构字段中隐藏的目标：

- `FiniteIntervalProblemConditional` 输入 T≥0、原层 primitive 演化、同源真实导数、条件性空间路径及闭区间坐标连续/静态兼容；没有 (9.5)、(9.6)、(9.7)、能量律、耗散非负、单调性或积分平衡字段。
- Green、独立迹/边界配对、梯度/散度定义域、时间交换仍是显式条件；Poincaré 针对同一个迹的核，不能把目标吸收估计代替 Poincaré。
- `Nonempty α` 仅用于从某一点的 0≤p≤S 取得 S≥0；二维载体 ℝ×ℝ 自动满足，仍允许零吸收和零测度，不把积分域缩成物理区。
- 路径只在 (0,T) 内要求 HasDerivAt 和演化。闭端点只要求连续与静态约束；T=0 的端点兼容不能由空内部方程推出。定量耗散和导数结论在开区间，闭区间得到能量界和单调性。
- 积分平衡额外使用 `hsecondR`：P_tt 在闭区间的实际 L² 连续性，由此证明耗散连续和可积；单调性不需要该附加条件。FTC 不要求端点普通双侧导数，且包含 t₁=t₂、t₁=0、t₂=T。

因此可以称为**明确分析接口下的条件性单调能量先验定理**。还不能称为“原八变量二维 PDE 已完整形式化”：具体矩形 Green、迹、精确 Poincaré、微分交换及原模型/primitive 双向对应仍未完成，提升唯一性和解存在唯一性也未完成。没有严格衰减结论，没有以有限时间估计证明全局解存在，没有扩大原小幅度范围。

本轮结束于 v0.3.5。下一入口 v0.4.1 仅是具体矩形光滑场、方向导数和四边边界/零迹表示；未提前实现。逐项依赖见 [定理清单新增记录](theorem_inventory.md)，PDF 的范围说明与旧批注更新见 [标注账本](pdf_formalization_marks.md)。
