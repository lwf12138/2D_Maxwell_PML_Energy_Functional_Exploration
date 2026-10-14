# 2026-10-14 v1.0 finalization：一般弱系数已接入 V7 主线

> 2026-10-14 发布标识整理：Lake 包版本已同步为 `1.0.0`，旧连续代表注释已更新。数学声明与证明未变，构建和公理审计重新通过；当前源码相对下述最终验收快照的两项差异及补充证据见 [整理记录](logs/v1.0_metadata_cleanup/record.md)。旧验收日志和快照保留不变。

> **最终验收通过（2026-10-14）：ROADMAP v1.0.1–v1.0.3 主线完成。** 119 个正式 Lean 文件进入默认构建；1058 次公理审计输出（1050 个不同声明），无 sorryAx；当前源码隔离构建及完整审计通过。范围为报告列明的 V7 足够正则弱图空间兼容类，T=0 合法初始 jet 语义单列。

本轮补齐一般分离 W¹,∞ 的连续代表构造、原 (10.2) 幂次剖面全族及精确阈值最小分支。精确 π 常数、实际标量指数记忆核和 Cᵏ 入口直接复用前轮证明。**最终工程、语义与 PDF 验收以 [本轮记录](logs/v1.0_finalization/acceptance.json) 为准**；下方旧“缺口/完成”文字均保留其历史日期含义。

推荐入口是 [MainGeneralWeak.lean](LeanPML/PML/MainGeneralWeak.lean) 的 `main_energy_GeneralWeakCk`（T>0）及 `main_energy_GeneralWeakJet`（T≥0，T=0 初始导数图兼容单列）。它们从原八个实际 L² 场及内部原方程、整个矩形 PEC、原材料/区域弱系数与精确阈值、初始兼容和实际加权成员出发，在证明中构造连续代表和已证空间接口。输出 (6.7)–(6.10)；配套 `auxiliary_current_GeneralWeakCk/Jet` 与 `auxiliary_initial_GeneralWeakJet` 给输入原 Z/Q 和 u/q/φ 的 (8.4)–(8.8) 当前/初值控制。

没有独立的 p/r 连续性输入，没有 Green/Poincaré/目标能量假设；没有正吸收下界、磁法向/散度约束或域内分区边界条件。采用 $C_P^2=(\pi^2/L_x^2+\pi^2/L_y^2)^{-1}$。不是一般解存在唯一性、严格衰减或任意分布解理论。

建议先读三条声明：

1. [一维真实弱导数→积分原函数与代表](LeanPML/Analysis/WeakIntervalRepresentative.lean)：`exists_regional_lipschitz_representative`。
2. [二维分离系数→合法连续代表](LeanPML/PML/WeakAbsorptionRepresentative.lean)：`RawWeakRegionalAbsorption.representatives`。
3. [原系统主入口](LeanPML/PML/MainGeneralWeak.lean)：`OriginalInterval.main_energy_GeneralWeakCk`。

随后看 [原幂次剖面](LeanPML/Examples/OriginalPowerProfile.lean) 与 [新非零静态/四分支调用](LeanPML/Examples/GeneralWeakRegression.lean)。将光标放在 `have`、`calc` 后查看 InfoView 的当前目标；F12 查结构字段与 mathlib 依赖；导入陈旧时执行 **Lean 4: Restart Server**。

```bash
python3 scripts/run_logged.py --stage v1.0_finalization lake_build lake build
python3 scripts/run_logged.py --stage v1.0_finalization axioms_audit lake env lean Audit.lean
```

完整命题、(6.6)/T=0 语义、论文映射及学习说明见 [弱定理报告](reports/weak_theorem.md)；[语义审查](logs/v1.0_finalization/semantic_review.md) 与 [PDF 账本](docs/pdf_formalization_marks.md) 分别记录命题范围和标记。隔离复现不复制项目编译产物，复用固定精确依赖缓存，并非完全无缓存测试。

---

# 以下为此前验收记录（历史原文保留）

# LeanPML：光滑版本与弱图空间兼容原解的全域先验定理

> 2026-10-14 closeout 最新对齐状态：本轮新增连接已验证，但 V7 原文逐项对齐仍未完成。一般连续代表、精确 π 常数及标量指数核识别仍列为缺口。下文既有“当前版本完成”指已列明假设与保守常数下的版本，不表示这些差异已经消除。详见本文件 closeout 追加节及 `logs/v1.0_closeout/semantic_review.md`。

## 2026-10-14 v1.0 数学闭合与本地验收通过

新弱版本已从实际原八式推出 (6.7)–(6.10)，包含图范数界、真实导数、准确耗散下界、闭区间单调性、积分平衡和输入原 E/H/P 控制。没有预设能量目标或未证 Green/Poincaré。旧 v0.5 光滑证明及实例保持不变。

当前源码、完整输入和差异见 [弱定理报告](reports/weak_theorem.md)；逐项工程/PDF验收见 [总记录](logs/v1.0.3/completion_20261014T122020/acceptance.json)。下方此前段落中的“尚未完成”均保留为历史。

- **v1.0.1**：真实弱图/加权空间及一般零迹桥接，补齐 [粗糙乘积零迹保持](LeanPML/PML/WeakZeroProduct.lean)。
- **v1.0.2**：[规范唯一](LeanPML/PML/WeakLiftCompatibility.lean)、区域 W¹,∞ 乘法、弱 Green/Poincaré、五不变量及已证 (5.8) 接到原辅助演化。
- **v1.0.3**：[弱原八式主定理](LeanPML/PML/MainWeakRectangle.lean)、[区域入口/原剖面积分](LeanPML/PML/WeakCanonicalEnergy.lean)、[非零静态解实际调用](LeanPML/Examples/WeakStaticMode.lean)、[四分支](LeanPML/Examples/WeakBranchRegression.lean)与不兼容增长排除。两阶段构建、913条审计和当前源码隔离复现均通过，见总记录。

范围：真实 H₀¹/H(div) 图路径，区域弱系数的连续代表及显式时间 jet；不再要求未知场联合 C∞。仍使用 **C_P=2Lx**，不是论文精确 π 常数。原式只在内部时间区间；闭区间连续、初值兼容及 T=0 初始导数兼容单列。不是一般弱解存在唯一性或严格衰减定理。

优先读 `weakCoefficientMul_mem_zeroBoundaryGraph` → `CompatibleLift.u_unique` → `main_energy_estimate_RegionalWeak`。InfoView 看每个具名 have/calc 后的目标，F12 查结构字段和依赖；导入陈旧时 **Lean 4: Restart Server**。

```bash
lake build
lake env lean Audit.lean
```

带完整命令/退出码的复现使用 `python3 scripts/run_logged.py --stage v1.0.3 lake_build lake build` 与 `python3 scripts/run_logged.py --stage v1.0.3 axioms_audit lake env lean Audit.lean`。隔离构建复用精确依赖缓存，不复制项目编译产物。

---

# 以下为此前版本的原始说明

# LeanPML：光滑兼容解类的全域先验能量定理

用途：从原八变量方程读到真实 L² 两层能量、耗散和有限区间单调性。**v0.5.1、v0.5.2、v0.5.3 已分别验收，整个 v0.5 完成。** 下方保留 v0.4 原说明作为历史；其中“本轮/下一阶段”指当时，不代表当前状态。准确命题和全部输入见 [光滑定理报告](reports/smooth_theorem.md)，历史见 [PROGRESS](PROGRESS.md)。v0.5 的证明及输入保持不变；最新弱分析进展见下节；其后的旧阶段段落保留历史。

## 2026-10-14 再次补齐：M1 已证，实际加权 (5.8) 已接通

当前证据优先于下方历史阶段文字。新增数学证明见 [弱空间报告](reports/weak_theorem.md)：

- [SmoothWeakClosure](LeanPML/Rectangle/SmoothWeakClosure.lean) 证明任意旧光滑四边零迹函数的内部紧支 H¹ 图逼近，已用非预先紧支多项式泡调用。v1.0.1 对应遗留连接补齐。
- [WeightedMemoryBound](LeanPML/PML/WeightedMemoryBound.lean) 证明真实弱场、实际 WeightedL2 和 Bochner 历史上的精确 (5.8)，同时给出原辅助场的密度可积性和积分界。成员资格由普通 L² 演化与初始加权成员推出，没有预设全时段加权成员。导数右端与非零调用见 [AuxiliaryWeightedEvolution](LeanPML/PML/AuxiliaryWeightedEvolution.lean)、[WeightedEvolution](LeanPML/Examples/WeightedEvolution.lean)。
- [WeakCoefficients](LeanPML/PML/WeakCoefficients.lean) 证明真实区域 W¹,∞ × H₀¹→H¹ 的弱乘积法则；[WeakDirectionalPoincare](LeanPML/Rectangle/WeakDirectionalPoincare.lean) 证明方向估计和单偏导零分离。尚缺乘积保持 H₀¹、分离弱系数入口、零水平集性质及提升唯一性。

**v1.0.2 仍部分完成；v1.0.3 弱原系统主定理仍未完成。** 新结果没有放宽旧 v0.5 主定理的输入，也没有把辅助演化实例称为非零弱 PDE 解。没有本轮新的隔离总装复现；下方旧独立构建仅对应当时源码。

优先阅读 `smoothToWeakH1_mem_zeroBoundaryGraph` → `auxiliary_weak_memory_bound` → `weakCoefficientMul_derivatives`。光标放在 `have`/`calc` 后看 InfoView，F12 跳转；导入陈旧时 **Lean 4: Restart Server**。复现：`python3 scripts/run_logged.py --stage v1.0.2 continuation_lake_build lake build`，随后 `python3 scripts/run_logged.py --stage v1.0.2 continuation_axioms_audit lake env lean Audit.lean`。

[本轮新验收及源码哈希](logs/v1.0.2/continuation_20261014T110047/acceptance.json)；[PDF 证据账本](docs/pdf_formalization_marks.md)。以下旧阶段段落保留历史含义。

## 2026-10-14 追加：弱分析子项已实现，v1.0 尚未闭合

本轮新增 [WeakGreen](LeanPML/Rectangle/WeakGreen.lean)、[WeakPoincare](LeanPML/Rectangle/WeakPoincare.lean)、[WeakPaths](LeanPML/Rectangle/WeakPaths.lean)、[AuxiliaryMemory](LeanPML/PML/AuxiliaryMemory.lean) 和 [非零调用](LeanPML/Examples/WeakAnalysis.lean)。以下 v1.0.1 文字保留为前一轮历史；当前状态以本段和 [弱空间报告](reports/weak_theorem.md) 为准。

已证明 H₀¹ 图闭包 × H(div) 弱 Green、保守 CP=2Lx 的弱 Poincaré，并实际填入旧空间接口；图范数真实时间导数可投影到 L² 梯度/散度。(5.7) 已完成固定空间点的真实时间积分版本，尚未完成 (5.8) 加权传播。

**v1.0.1 仍部分完成，v1.0.2 部分完成，v1.0.3 主定理未完成。** 尚缺一般光滑零迹的图范数逼近、W¹∞ 乘积法则、加权传播、规范唯一性和弱原系统总装。旧 v0.5 主定理、静态/增长/退化回归保持，不冒称新的弱主定理调用。

优先读 `Rectangle.weak_green`、`Rectangle.weak_poincare`、`PML.auxiliary_memory_formula`。InfoView 中逐步查看 `hspan`、`hclosed`、`hFTC`；F12 查看调用的闭包、连续性和 FTC 引理。导入未刷新时用 **Lean 4: Restart Server**。

复现命令、准确假设与源码位置见报告；实际 [v1.0.2 验收记录](logs/v1.0.2/acceptance.json) / [v1.0.3 交付记录](logs/v1.0.3/acceptance.json) 区分构建通过与数学阶段未完成。隔离工程不复制项目编译产物，复用精确依赖缓存；[独立环境](logs/v1.0.3/clean_environment.json) 与 [结果](logs/v1.0.3/clean_result.json) 如实记录。

## v1.0.1 当前进展：空间构造子项通过，连接仍有缺口

本轮新增 [弱空间构造](LeanPML/Rectangle/WeakSpaces.lean)、[加权空间算子](LeanPML/Analysis/WeightedL2Operators.lean) 和 [非零调用](LeanPML/Examples/WeakSpaces.lean)。没有更新依赖或进入 v1.0.2。具体 API、实际类型、来源与失败/成功记录集中在 [阶段记录](logs/v1.0.1/stage_record.md) 和 [验收记录](logs/v1.0.1/acceptance.json)。

建议先读这三条声明，再回到下方保留的 v0.5 主定理：

1. `Rectangle.HasWeakPartial`：对象是实际 L² 商类，弱偏导由所有内部紧支 C∞ 测试函数的积分配对定义；`HasWeakPartial.unique` 证明导数唯一。
2. `Rectangle.weakSpatialDomain_smooth`：新弱梯度与旧光滑函数的真实偏导相同。`weakH1Graph/weakHDivGraph` 是闭且完备的实际图空间，`zeroBoundaryGraph` 是内部紧支光滑图的张成闭包。
3. `Analysis.physicalL2_range_iff`：恢复映射的像恰是“平方根加权可积且零区 a.e. 为零”的普通 L² 类。旧 WeightedL2 的嵌入、完备性及积分表示全部复用；`weightedMul` 只让**有界系数**作用，未把无界能量权重当成普通 L² 有界乘子。

新弱空间不要求未知场 C∞；只有测试函数和光滑桥接使用 C∞。图表示采用最大值乘积范数，并已证明它与分量平方和的双边控制。梯度、散度仍有受限定义域；没有增加吸收正下界、边界磁条件或全域正阻尼。

**v1.0.1 暂按部分完成登记。** 所有旧光滑场已进入弱 H¹，光滑通量已进入弱 H(div)，非零紧支场已进入 H₀¹ 闭包；但所有旧光滑零迹场进入该闭包的一般图范数逼近尚未实现。弱迹/弱 Green、Poincaré、W¹∞ 乘积与切片、加权传播及提升唯一性仍待后续。现有光滑 PDE 主定理的联合 C∞、C(K) 和实际加权路径假设**没有因此放宽**。

在 InfoView 中先查看弱导数定义的 `∀ φ`，再看 `eq_zero_of_test_inner` 的 a.e. 结论，以及 `weakH1Graph_isClosed` 如何用连续配对保持导数。F12 可跳到固定 mathlib 的 `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`（`Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean:219`）。`TemperedDistribution.MemSobolev`（`Sobolev.lean:149`）是全空间 Bessel 势表示，不是这里的矩形 H₀¹；普通 Lp 光滑密度也不能直接代替图范数或无界权重下的逼近。

```bash
python3 scripts/run_logged.py --stage v1.0.1 lake_build lake build
python3 scripts/run_logged.py --stage v1.0.1 axioms_audit lake env lean Audit.lean
```

命令在本工程根目录运行。导入过期时先构建，再执行 **Lean 4: Restart File**。本轮保留 v0.5 全部证明及回归，未修改 PDF、路线图、模型合同或依赖锁文件。

## 先读三条声明

都在 [MainSmoothRectangle.lean](LeanPML/PML/MainSmoothRectangle.lean)，命名空间为 `LeanPML.PML.SmoothRectangle`。

1. `SmoothCompatibleSolution`：逐个展开输入字段。它接收原八变量、原方程、区域吸收界、PEC、初始兼容和明确的强正则性；不接收现成能量问题或目标估计。
2. `SmoothCompatibleSolution.energy_law_and_closure`：从实际原模型总装得到真实 `HasDerivAt` 和定量耗散下界。比较导数等式、耗散符号与剩余预算三个结论。
3. `main_energy_estimate_smoothRectangle`：把图范数平方界、闭区间单调性、实际 FTC 积分平衡和输入原 E/H/P 控制汇总为结论包。

接着读 [FullDomainProfile](LeanPML/Examples/FullDomainProfile.lean) → [CompatibleData](LeanPML/Examples/CompatibleData.lean) → [StaticMode](LeanPML/Examples/StaticMode.lean) → [UnrestrictedData](LeanPML/PML/Obstructions/UnrestrictedData.lean)。辅助 `SmoothBump`、`PathHelpers` 服务于真实光滑函数、普通/加权路径的成员与导数；`DegenerateBranches.four_branches_main` 检查四种吸收接口。

## 当前具体定理证明什么

在整个非退化矩形上，原方程只要求在 $(0,T)\times\Omega$ 成立；PEC、连续性和静态条件覆盖 $[0,T]$。区域系数入口只限制闭坐标区间内的原 $p,r$；内部截回代表与原系数域内及 a.e. 一致，能量/耗散已接回原系数的合法空间积分。

图平方界及能量比较在 $[0,T]$；以下导数恒等式与定量耗散下界仅在 $t\in(0,T)$。

$$\frac{N_0^2+KN_1^2}{4}\le\mathcal E_7\le N_0^2+KN_1^2,\qquad
\mathcal E_7'=-\mathcal D_7,$$

$$\mathcal D_7\ge\frac{\mathcal S_0+K\mathcal S_1}{2}
+\frac{\mu\tau}{4\kappa}(\|P_t\|_2^2+K\|P_{tt}\|_2^2)\ge0.$$

由此得到 `AntitoneOn`、$0\le\mathcal E_7(t)\le\mathcal E_7(0)$，以及

$$\mathcal E_7(t_2)+\int_{t_1}^{t_2}\mathcal D_7(s)\,ds=\mathcal E_7(t_1)
\quad(0\le t_1\le t_2\le T).$$

(6.10) 控制的是输入原场的实际 L² 范数，代码用 `MemLp.toLp` 与实际历史/磁重构证明对应；不是仅给任意重构坐标一个名字。相同时刻、端点和 $T=0$ 均包含；退化时保留初始导数层兼容，不能从空的内部方程推出它。

这仍是给定解的先验估计。联合 C∞ 技术延拓、C(K) 一致范数路径和实际加权成员/可微性是强于 V7 (6.6) 的输入，不是由论文弱正则性自动推出。无界权重没有被当成普通 L² 有界乘子；零吸收区仍保留普通场与 $c|\nabla v|^2$。没有新增吸收正下界、磁场约束或内部边界条件。

## 参数与三个非平凡检验

采用已证明的 $C_P=2L_x$，不是论文最优 π 常数。实例在 $(-1,1)^2$ 上使用

$$\epsilon=\kappa=\tau=\mu=1,\quad C_P=4,\quad A=3,\quad K=384,
\quad c=1/16384,\quad S=1/65536.$$

参数调用 `ParameterCertificate` 的精确证书。$p(x)=S\,\mathrm{smoothTransition}(4x^2-1)$、$r(y)$ 同式是真正 C∞ 替代剖面：物理区为零，四边单向吸收、四角双向吸收，域内幅度界由构造证明；没有冒充原(10.2)分段幂函数。

- 非零物理区紧支初值证明五兼容、初始八式、真实一阶导数、迹及有限正图平方。方便计算的时间延拓只在 $t=0$ 核验方程，**不是该初值的区间解存在证明**。
- 静态例实际满足八式及全部输入，并调用最终定理；非零正能量恒定、耗散为零。加权有限性来自实例紧支落在 $p=S$ 平台，$w_y=3$，不是主定理新增全域下界。
- 任意八变量初值增长例是实际全未来场 $H=t\nabla\psi,Q=\mu\nabla\psi$；八式、PEC、可积性与磁 L² 的 $t^2$ 增长均已证。它违反磁辅助初始兼容；只否定固定正磁控制、有限初能量和全未来单调同时成立的能量，不否定所有能量。

## InfoView、F12 与复现

VS Code 打开整个工程文件夹，光标依次放在 `by`、具名 `have`、`calc`、`rw` 后查看 Lean InfoView 的假设和目标。F12 从主定理进入 `problem`，再进入 `originalRegionalFiniteIntervalProblem`，可看到 Green/Poincaré 和原方程兼容如何被真正填入。导入过期时先构建，再执行 **Lean 4: Restart File**。

固定依赖中的关键出处：`Real.smoothTransition` 在 `Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`；`expNegInvGlue` 同样在 `Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`；混合导数对称性在 `Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`；FTC `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` 在 `Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`。文件均位于 `.lake/packages/mathlib/` 下，F12 可查准确使用点。

```bash
cd '/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML'
lake build
lake env lean Audit.lean
```

分别保存阶段日志可运行：

```bash
for stage in v0.5.1 v0.5.2 v0.5.3; do
  python3 scripts/run_logged.py --stage "$stage" lake_build lake build
  python3 scripts/run_logged.py --stage "$stage" axioms_audit lake env lean Audit.lean
done
```

下表保留 v0.5 的独立验收，新增空间的当前验证见上方 v1.0.1 记录。

| 阶段 | 验收 | 当时完整构建 / 独立审计 | 审计声明数（含历史） |
|---|---|---|---|
| v0.5.1 | 通过 | [构建](logs/v0.5.1/20261014T005346_311276_lake_build.log) / [审计](logs/v0.5.1/20261014T005434_779198_axioms_audit.log) | 619 |
| v0.5.2 | 通过 | [构建](logs/v0.5.2/20261014T011030_802569_lake_build.log) / [审计](logs/v0.5.2/20261014T011311_263210_axioms_audit.log) | 683 |
| v0.5.3 | 通过；覆盖本轮三阶段当前源码 | [构建](logs/v0.5.3/20261014T011533_485975_lake_build.log) / [审计](logs/v0.5.3/20261014T011752_801259_axioms_audit.log) | 740 |

审计只有 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx` 或自定义占位公理。结构字段另做语义检查，不能用公理审计代替范围检查。失败日志、命令、退出码和源码哈希保留。最终整体验收见 [overall_acceptance.json](logs/v0.5.3/overall_acceptance.json)。Lean v4.31.0 和 mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` 未变。

## PDF 历史与后续工作

以下是 v0.5 的 PDF 历史，本轮 v1.0.1 未修改副本：指定副本保留18页和200条旧批注；第5/8/10/12/15/16页新增6个带范围红勾，第11/14页只补说明。详见 [PDF账本](docs/pdf_formalization_marks.md)、[逐页视觉检查](logs/v0.5.3/pdf/visual_review.json)。原论文、模型合同、路线图和历史日志保持。路线图旧“待实现”是冻结文本，当前实现状态以源码和本轮证据为准。

本轮交接停在 **v1.0.1 部分完成**：优先补齐一般光滑零迹场进入新 H₀¹ 闭包的图范数逼近连接。v1.0.2 再处理弱 Green/Poincaré、W¹∞ 系数、(5.7)/(5.8) 加权传播和提升规范唯一性，本轮没有实施。精确 π 常数、一般解存在唯一性、严格/指数衰减仍未证明。

---

# 以下为 v0.4 及对齐修复时的完整 README 历史

以下“本轮/下一阶段/尚未实施”保持当时含义，当前状态见上文与本轮验收。

# LeanPML：具体光滑矩形接口与原模型映射

用途：沿实际函数、L² 商类、四边迹、历史提升这条线阅读 v0.4。本次对齐补齐参数证书、区域幅度入口和古典空间可导包装；旧验收范围的更正见文末。v0.4.1–v0.4.4 已分别完成实现、完整构建、公理审计和假设检查。此前说明见 [v0.4 入场 README](logs/v0.4.1/initial_files/README.md)，阶段历史见 [PROGRESS](PROGRESS.md)。本轮不实施 v0.5，不更新 Lean/mathlib。

## 先读三条声明

1. [ParameterCertificate.lean](LeanPML/Rectangle/ParameterCertificate.lean) 的 `unitSquare_parameter_certificate`：从实际矩形算出 $C_P,A,K$，然后查看 `unitSquare_explicit_smallness` 和阈值等价的调用。
2. [ClassicalSystem.lean](LeanPML/PML/ClassicalSystem.lean) 的 `original_to_primitive_classical_rectangle`：比较原八方程、真实空间可导证据和兼容保持结论；反向见同文件 `primitive_to_original_classical_rectangle`。
3. [RegionalCoefficients.lean](LeanPML/Rectangle/RegionalCoefficients.lean) 的 `RegionalAbsorption.originalRegionalFiniteIntervalProblem`：查看域内幅度条件怎样生成旧框架需要的实现代表，再进入古典映射和具体 Green/Poincaré 构造。

先读每条声明冒号后的结论，再追踪输入和具名 `have`。原 v0.4 的学习路线仍是 Domain → Fields/Boundary → Green/Poincare → TimeSpace/L2Paths → WeightedCalculus/StatePaths → 原系统与实际历史 → ClassicalSystem → RegionalCoefficients。旧 `originalFiniteIntervalProblem_separated` 保留兼容，但其全轴幅度条件较强，不再作为推荐入口。

## 本轮究竟选择了什么光滑类

空间是整个非退化开矩形

$$\Omega=(x_-,x_+)\times(y_-,y_+),\qquad L_x=x_+-x_->0,\quad L_y=y_+-y_->0.$$

`Rect.measure` 复用原工程二维 Lebesgue 限制测度。`measure_eq_closed` 证明四边零测度允许使用闭矩形代表计算体积分；`integral_fubini` 使用真正的 Fubini。全域没有缩成物理区。

| 条件 | 本轮采用的表示 | 与 V7 的差异及用途 |
|---|---|---|
| 空间光滑 | 场切片有全空间 C∞ 技术延拓；PDE 仅在 Ω 内成立 | 强于 H₀¹/H(div) 弱空间。用真实 `fderiv` 定义 x/y 导数，并由连续代表的 a.e. 唯一性证明导数与四边迹良定义 |
| 混合光滑 | 所用原层与导数层联合 C∞ 延拓 | 从二阶导数对称性证明时间—空间交换；交换公式本身不是输入字段 |
| 普通路径 | 闭矩形 K 上 C(K) 一致范数路径连续、相关路径可微 | 比仅逐点可导强。`UniformTimeJet` 明确列出使用的曲线；由 `evalCLM` 识别导数，经 `continuousToL2` 得到真正 L² 的 HasDerivAt |
| 时间延拓 | 技术延拓的正则性可以在全实轴要求 | 原八条演化只在 (0,T)×Ω 要求，PEC、初值及静态条件覆盖 [0,T]；不是全实轴 PDE 解假设 |
| 吸收 | 实际分离 p(x)、r(y)，非负、时间不变、原幅度限制；所选光滑版本另列光滑条件 | 不要求任何吸收正下界，不对 w 作空间求导。尚未覆盖一般 W¹,∞ 弱解类 |
| 加权路径 | √wφ、√wφ_t、√wφ_tt 的实际 L² 成员；加权路径连续与可微 | 普通光滑不能自动推出这些条件。本轮识别其导数，不证明 (5.7)/(5.8) 的加权正则性自动传播 |
| 初值 | 固定任意 u₀、q₀，五个初始不变量为零；u₀ 四边零迹，零区 φ₀=0 | 不默认 u₀=q₀=0，不要求全时段兼容作为原解输入 |
| T=0 | 内部方程为空；必要初始图状态兼容另列 | 特别不能从某个时刻 E=0 推出任意 E_t=0。T>0 时用连续性将内部结果延至端点 |

`SmoothTimeJet` 的 `value/first/second` 各自是真实空间函数，并有 HasDerivAt 绑定；`UniformTimeJet` 只说一致范数可导，不直接给目标 L² 导数。`SmoothZeroOn` 是中间构造需要的兼容**结论**，最终原系统入口必须从真实保持定理填入，不能作为原系统“正则性”假设。

## 四边 Green 与本轮 Poincaré 常数

实际边界数据依次为右、左、上、下的连续函数。边界配对独立定义为这四条一维积分：

$$
\int_\Omega f\,\mathrm{div}\Lambda
=-\int_\Omega(\partial_x f\,\Lambda_x+\partial_y f\,\Lambda_y)
+\int_{y_-}^{y_+}f(x_+,y)\Lambda_x(x_+,y)\,dy
-\int_{y_-}^{y_+}f(x_-,y)\Lambda_x(x_-,y)\,dy
+\int_{x_-}^{x_+}f(x,y_+)\Lambda_y(x,y_+)\,dx
-\int_{x_-}^{x_+}f(x,y_-)\Lambda_y(x,y_-)\,dx.
$$

零迹逐边消去。主线没有分区积分，也不增加磁场法向约束或内部边界条件。光滑代表相同 L² 类时在闭矩形相等，所以迹不是从任意 L² 代表上读点值。梯度、散度仅定义在光滑代表的 L² 像子空间上，不是整个 L² 上的有界算子。

本轮实际证明的是保守常数

$$C_{P,\mathrm{smooth}}=2L_x,\qquad
\|v\|_2^2\le4L_x^2\bigl(\|\partial_xv\|_2^2+\|\partial_yv\|_2^2\bigr).$$

证明对 $(x-x_-)v^2$ 使用 Green/散度公式，再对非负平方积分作估计。于是本轮必须使用

$$K_{\mathrm{smooth}}=32\mu(\epsilon+2\kappa)L_x^2,\qquad
c_{*,\mathrm{smooth}}=\min\left\{K_{\mathrm{smooth}}^{-1/2},\frac{\kappa\tau}{8AK_{\mathrm{smooth}}},\frac{\kappa}{8A\tau}\right\}.$$

`scaleK_rectangle` 精确核验这一替换，`threshold_rectangle_pos` 证明原材料正性下阈值仍为正。旧阶段到此只完成了符号替换，尚缺保守常数下的具体参数证书；本次由 `ParameterCertificate` 补齐。没有证明原文 (5.1) 的最优 π 常数；合同和原文原样保留。

非平凡调用使用四边为零、内部非零的多项式泡函数。已证明其 L² 类非零，并实际调用 Green、Poincaré 和时间路径求导。这是接口调用，不是 PDE 非零解存在性证明。

## 历史提升、五个不变量与零区

`integralLift` 是实际时间积分：

$$u(t,x)=u_0(x)+\int_0^tE(s,x)\,ds,\qquad
q(t,x)=q_0(x)+\int_0^tP(s,x)\,ds.$$

`HistoryL2` 通过连续线性映射与 Bochner 积分交换，连接逐点历史和 L² 历史。FTC 证明初值与导数；固定初始原函数的历史唯一性不等于任意兼容提升的规范唯一性。

先证明五个实际不变量沿时间等于其初始**空间函数**，再使用初始零值：

$$C_D=q+\tau P-\kappa u,\quad C_{z1}=Z_1+\epsilon bu,\quad C_{z2}=Z_2+bq,
\quad C_x=Q_x-p\phi_y,\quad C_y=Q_y+r\phi_x.$$

两个磁不变量核对了 $\lambda=(\mu H_y,-\mu H_x)$ 的方向，并使用已证真实混合求导。场层定理还给出相应实际 L² 等价类相等，未止于某个点的普通实数验证。一般非零初始不变量的保持已覆盖，但其带源 primitive 版本不属于本轮无源主线。

在零吸收区，$p=r=0$ 和辅助演化给 $\phi_t=0$，还须用初始 $\phi_0=0$ 才推出全时段零值。加权恢复映射在零区取零并不能替代这条原场保持证明。普通场与零区 $c|\nabla v|^2$ 仍保留。

## 学习时怎样看目标

用 VS Code 打开整个 Lean_PML 文件夹。把光标放在 `by` 后及每条 `have`、`calc`、`rw` 后，在 Lean InfoView 查看当时的假设与目标。F12 可跳转项目声明和固定 mathlib 源码；尤其比较“导数存在”“导数值识别”“方程代入”三个步骤。导入显示过期时先在工程终端 `lake build`，再执行 **Lean 4: Restart File**；必要时重新打开文件。

关键 mathlib 来源（都来自当前锁定依赖）：

- `ContDiffAt.isSymmSndFDerivAt`：`.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`。
- `integral_divergence_prod_Icc_of_hasFDerivAt_of_le`：`.lake/packages/mathlib/Mathlib/Analysis/Calculus/DivergenceTheorem.lean`。
- `ContinuousMap.evalCLM`：`.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Algebra.lean`。
- `BoundedContinuousFunction.toLp`：`.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LpSpace/ContinuousFunctions.lean`。
- `ContinuousLinearMap.intervalIntegral_comp_comm`、`intervalIntegral.integral_hasDerivAt_right`：固定依赖的 IntervalIntegral 模块；F12 显示实际声明位置。

## 验证与下一步

固定 Lean v4.31.0 / mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`。四阶段命令、失败与修复输出分别保存于 `logs/v0.4.1` 至 `logs/v0.4.4`；每个 `acceptance.json` 只在对应数学及工程检查通过后写为完成。

```bash
cd '/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML'
lake build
lake env lean Audit.lean
```

要另存本次对齐修复的复现日志：

```bash
python3 scripts/run_logged.py --stage v0.4_alignment lake_build lake build
python3 scripts/run_logged.py --stage v0.4_alignment axioms_audit lake env lean Audit.lean
```

下一阶段 v0.5.1 才把具体接口构造接到 `main_energy_estimate_Conditional` 并发布名称清楚的光滑兼容类先验主定理。本轮不创建 MainSmoothRectangle.lean 或 smooth_theorem.md。弱 H₀¹/H(div) 范围、W¹,∞ 的一般实现、精确 π 常数、(5.7)/(5.8) 自动传播、提升规范唯一性和解存在唯一性均不能因本轮接口构造而自动登记完成。

## 最后怎样进入已有能量框架

推荐改用 [RegionalCoefficients.lean](LeanPML/Rectangle/RegionalCoefficients.lean) 的 `RegionalAbsorption.originalRegionalFiniteIntervalProblem`：输入真实八变量、仅闭坐标区间受幅度限制的分离系数、仅内部的原方程、初始五兼容、PEC、初始零区 φ、强正则性和实际历史的坐标识别，返回旧 `FiniteIntervalProblemConditional`。它没有输入现成的条件性问题，也没有输入 Green、Poincaré、混合交换、全时段兼容或目标能量结论。

`LiftIdentified` 将八个光滑时间槽逐一识别为实际积分提升及磁场重构；不是重新选取无关的 u/q。`original_static_closed` 从初始条件产生闭区间两层静态条件；`original_smoothZeroOn` 从原场零区保持产生加权坐标所需零值，再对邻域零函数求真正的一、二阶导数。`originalFiniteIntervalProblem_second_R_continuous` 另给积分平衡所需 P_tt 的实际 L² 连续性。

T=0 时额外的 `InitialDerivativeCompatible` 只要求初始导数层极化关系及零区 φ_t；不能由空内部方程推出。有限区间能量接口只需要内部 E_t 的零迹；若另外要求整个闭区间 E_t 零迹，`BoundaryTime.velocity_PEC_on_Icc` / `twoLayer_zeroBoundary` 明确要求 T=0 时该初始迹。u 与 E 的闭区间零迹则来自 u₀ 零迹、历史积分与 PEC。

底层 `OriginalAt`/`PrimitiveAt` 用真实 `fderiv` 的总定义书写空间导数。其代数方程定理本身不自动产生空间正则性；旧最高入口的具体解释已依靠 `SmoothStateData` 与 `LiftIdentified` 的真实光滑代表。本次把这一步显式化为 `OriginalClassicalOn` / `PrimitiveClassicalOn`；由光滑识别与 $\mu\ne0$ 导出所需空间可导性，再通过带 `_classical_rectangle` 的双向定理恢复全部八式和 PEC。旧代数证明保持成立，不表示方程自动改善正则性。

任意非零初始不变量的时间保持已经证明；把它们设为零后才得到本轮无源 primitive 对应。带非零不变量的额外源项系统未实现，不混入主范围。固定 u₀、q₀ 的历史唯一性也不等于同一原状态的提升规范唯一性。

| 阶段 | 状态 | 完整输出 | 审计声明数（含历史） |
|---|---|---|---|
| v0.4.1 | 已验收 | [构建](logs/v0.4.1/20261013T224101_375806_lake_build.log) / [审计](logs/v0.4.1/20261013T224142_908894_axioms_audit.log) | 410 |
| v0.4.2 | 已验收 | [构建](logs/v0.4.2/20261013T224801_700595_lake_build.log) / [审计](logs/v0.4.2/20261013T225034_426223_axioms_audit.log) | 429 |
| v0.4.3 | 已验收 | [构建](logs/v0.4.3/20261013T230513_776030_lake_build.log) / [审计](logs/v0.4.3/20261013T230651_423759_axioms_audit.log) | 484 |
| v0.4.4 | 已验收 | [构建](logs/v0.4.4/20261013T230822_044824_lake_build.log) / [审计](logs/v0.4.4/20261013T231144_117778_axioms_audit.log) | 537 |

审计仅出现标准 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx`；证明源码无 sorry/admit/自定义占位公理。构建还检查了此前全部模块。源码哈希、受保护文件复核、独立语义审查见 [最终验收](logs/v0.4.4/acceptance.json)、[语义审查](logs/v0.4.4/semantic_review_geometry.md)；PDF 的范围和证据集中在[原标注账本](docs/pdf_formalization_marks.md)。

## v0.4 对齐：参数、区域和真实空间导数

在实际 `unitSquare : Rect`，即 $\Omega=(-1,1)^2$ 上，取 $\epsilon=\kappa=\tau=\mu=1$。从已证明的 $C_P=2L_x$ 得到

$$C_P=4,\quad A=3,\quad K=384,\quad c=\frac1{16384},\quad S=\frac1{65536}=\frac c4.$$

三条阈值条件的左端精确为

$$c^2K=\frac3{2097152}\le1,\qquad8cAK=\frac9{16}\le1,\qquad8cA\tau=\frac3{2048}\le1.$$

`unitSquare_le_threshold` 调用已有 `le_threshold_iff_explicit.mpr` 得到 $c\le c_*$。原文 §10 的 $c=1/128$ 使用另一 Poincaré 常数；在当前 $K=384$ 下第二条变成 $72\le1$，不成立。`oldC_not_le_threshold` 给出正式对照。这里只补数值参数证书，没有提前实现吸收剖面或非零初值族。

`RegionalAbsorption` 只要求 $x\in[x_-,x_+]$ 时 $0\le p(x)\le S$，以及对应 y 条件。内部取

$$\widetilde p(x)=p(\max(x_-,\min(x_+,x))),\quad
\widetilde r(y)=r(\max(y_-,\min(y_+,y))).$$

截回后的函数连续可测且全轴有界，供旧 L² 乘子实现使用；它不必在截回端点光滑。原技术延拓仍可 C∞，但不再限制其域外幅度，也不要求域外 PDE。`coefficients_eq_closed` 和 `coefficients_ae` 证明闭域逐点及体积分 a.e. 一致；`weights_ae`、`weighted_memLp_iff` 保留零区和可能无界的权重。`fieldEnergy_eq_regional_integral`、`fieldDissipation_eq_regional_integral` 连同各自可积性证明，把已有能量、耗散接回原 $p,r$ 的整个矩形积分。

原空间证据仅要求 E、Hx、Hy 可导；primitive 侧要求 u、E、Λx、Λy 可导，没有给 P/Z/Q 增加无关空间条件。`hasDerivAt_spaceDx_of_differentiable` 和 y 版本从真实 Fréchet 可导性推出坐标切片的 HasDerivAt。最终区域入口实际调用“光滑识别 → 古典原解 → 域内系数改写 → 古典 primitive → 有限区间接口”，不是仅增加未被调用的类型标签。

当前仍采用强于 V7 (6.6) 的联合 C∞ 技术延拓、C(K) 一致范数路径条件，以及真实加权成员资格/连续可微性。这些是为兑现接口而选择的正则性输入，**不是由论文弱空间假设推出**。普通光滑没有取代加权正则性；全时段兼容与零区保持则由初值和原演化证明。有限区间问题构造只需要 $\mu\ne0$；使用后续能量定理时仍须原材料正性和对应阈值，不能把这个构造自身当成完整先验定理。

本次逐项范围及历史更正见 [对齐记录](logs/v0.4_alignment/alignment_record.md) 和 [独立语义检查](logs/v0.4_alignment/semantic_review.md)。构建、审计及 PDF 验收结果在本次 [验收记录](logs/v0.4_alignment/acceptance.json) 中登记；旧 v0.4 日志仅对应旧源码。

本次对齐验证： [完整构建](logs/v0.4_alignment/20261014T000055_917026_lake_build.log)、[独立审计](logs/v0.4_alignment/20261014T000341_178705_axioms_audit.log)、[类型检查](logs/v0.4_alignment/20261014T000341_178709_interface_types.log) 均退出 0；共审计590个声明，新增53项。PDF页3/4/7/15已按实际范围对齐，详见[账本](docs/pdf_formalization_marks.md)及[视觉检查](logs/v0.4_alignment/pdf/visual_review.json)。


## 2026-10-14：v1.0 closeout 新增连接（保留前述历史状态）

本轮六项对齐中：(6.6) 所需 λ_tt 已由真实图导数与辅助演化推出；(8.4)–(8.8) 已直接控制输入原 Z1/Z2/Qx/Qy 并接到初值能量；弱 primitive 反向重构的八个真实导数、八式及兼容已证明。新增加权空间算子指数记忆公式，与已有历史及原辅助场连接。非零静态路径调用了新正则性入口、反向映射和两个方向的核公式。

仍未完成：一般分离 W¹,∞ 的连续代表自动构造；原 (5.1) 精确 π 常数；算子指数与逐点标量指数乘法的识别。当前仍用 C_P=2Lx，区域连续代表仍单列，T=0 的初始导数兼容仍保留。因此“本轮已实现连接验证通过”与“V7 原文逐项对齐完成”分开登记，后者仍为否。

新增源码：`PML/WeakPhysicalControl.lean`、`PML/WeakV7Regularity.lean`、`PML/WeakReverse.lean`、`Analysis/OperatorMemory.lean`、`PML/AuxiliaryOperatorMemory.lean`、`Examples/WeakCloseout.lean`（均在 LeanPML 下）。逐字段和缺口核查见 `logs/v1.0_closeout/semantic_review.md`；构建、审计、隔离复现及最终哈希见该目录的验收记录。未更改旧数学证明、路线图、模型合同或依赖版本。

建议先读 `V7TimeRegularity.flux_second`（真实导数如何产生）、`original_auxiliary_initial_control`（重构识别和初值界）、`primitive_to_original_WeakAt`（八式反向链）。指数核随后读 `operator_memory_formula` 和 `operator_memory_both`。VS Code 打开工程根，在 `have`/`calc` 后移动光标看 InfoView；F12 跳到被调用引理。刷新导入可先运行 `lake build`，再执行 Lean: Restart File。

复现本轮：
```sh
python3 scripts/run_logged.py --stage v1.0_closeout lake_build lake build
python3 scripts/run_logged.py --stage v1.0_closeout axioms_audit lake env lean Audit.lean
```
mathlib 精确 API：`hasDerivAt_exp_smul_const` 在 `Mathlib/Analysis/SpecialFunctions/Exponential.lean:382`；`HasDerivAt.clm_apply` 在 `Mathlib/Analysis/Calculus/Deriv/Mul.lean:643`；FTC 位于 `Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`。本轮完整类型打印见 `logs/v1.0_closeout/TypeReview.lean` 及对应运行日志。


## 2026-10-14 最新收尾：精确常数与标量核已接通

**当前已核验版本通过；ROADMAP v1.0 主线尚未全部完成。** 本轮证明原 (5.1) π 常数并接入最终弱原系统能量、原 (5.7) 的实际标量指数乘子/Bochner 公式；核验原 c=1/128、S=1/512 数值阈值。真实 Cᵏ 字段可在 T>0 构造路径及规范端点导数槽；T=0 继续明确初始导数兼容。一般分离 W¹,∞→连续代表仍缺，`WeakRegionalAbsorption` 的区域连续性没有被删除或伪装为已证。

先读三条声明：
1. [weak_sharp_poincare](LeanPML/Rectangle/SharpPoincare.lean)：一维→Fubini→H¹ 图闭包；保守常数版本保留。
2. [scalar_memory_both](LeanPML/PML/AuxiliaryScalarMemory.lean)：双方向真实原辅助场与标量指数核；每时刻商类等式。
3. [main_energy_RegionalSharpCk](LeanPML/PML/WeakCanonicalTime.lean)：从区域原系数、原八式、初始兼容和真实正则性到精确常数主结论。

完整输入、T=0 与非零调用见 [弱定理报告最新节](reports/weak_theorem.md)，核查记录见 [semantic_review.md](logs/v1.0_completion/semantic_review.md)。[SharpWeak.lean](LeanPML/Examples/SharpWeak.lean) 有非零实际静态解调用和正能量/零耗散回归。InfoView 中逐步查看 `have`/`calc` 的目标，F12 查原结构字段；刷新导入先构建，再执行 Lean: Restart File。

```sh
cd '/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML'
python3 scripts/run_logged.py --stage v1.0_completion lake_build lake build
python3 scripts/run_logged.py --stage v1.0_completion axioms_audit lake env lean Audit.lean
```

本轮实际通过完整构建、997项审计、类型审查和当前源码隔离复现。隔离未复制本项目编译产物，复用精确依赖缓存。证据：[acceptance.json](logs/v1.0_completion/acceptance.json)、[isolated_result.json](logs/v1.0_completion/isolated_result.json)。没有升级依赖、修改原论文/合同/路线图或提交远端。
