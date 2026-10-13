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
