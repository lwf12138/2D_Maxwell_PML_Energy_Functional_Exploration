# 2026-10-14 最终入口：一般分离弱系数的 V7 全域先验能量定理

> **最终验收通过（2026-10-14）：ROADMAP v1.0.1–v1.0.3 主线完成。** 119 个正式 Lean 文件进入默认构建；1058 次公理审计输出（1050 个不同声明），无 sorryAx；当前源码隔离构建及完整审计通过。范围为报告列明的 V7 足够正则弱图空间兼容类，T=0 合法初始 jet 语义单列。

本节是最新范围；以下历次报告原文保留，旧缺口不代表当前状态。实际验收见 [acceptance.json](../logs/v1.0_finalization/acceptance.json)，完整结构审查见 [semantic_review.md](../logs/v1.0_finalization/semantic_review.md)。本轮没有修改旧光滑主定理或原论文/数学合同。

## 准确命题

给定非退化整个矩形 Ω、正材料 ε/κ/τ/μ，真实区域分离 W¹,∞ 系数 p(x)、r(y)，区域内 $0\le p,r\le S\le c/4$，$0<c\le c_*$。使用

$$C_P^2=(\pi^2/L_x^2+\pi^2/L_y^2)^{-1},\quad A=\varepsilon+2\kappa,\quad K=8\mu A C_P^2.$$

原八变量是 L² 商类，E 的 H₀¹ 图表示整个 PEC，$(\mu H_y,-\mu H_x)$ 是真实 H(div) 图；八条方程及 HasDerivAt 仅在 $(0,T)$，空间域是整个 Ω。初值只给五个不变量零、合法 u₀/q₀ 和实际加权辅助成员。原场、E 图、λ 图在闭区间连续。

对 T>0，`V7ClosedCkCore` 输入恰为所用真实空间路径的 $u\in C^2(H_0^1)\cap C^3(L^2)$、$P\in C^2(L^2)$、$\lambda\in C^1(H(\mathrm{div}))$。u 是 Bochner 历史；φ 的所需加权历史与导数从初值和演化构造，未将 OriginalJet 或能量律包成字段。$\lambda_{tt}$ 的 L² 证据由空间关系和实际辅助演化求导产生。`canonicalInterval` 内部规范端点 E/P 导数槽，保留全部原场。

`PML.Weak.OriginalInterval.main_energy_GeneralWeakCk` 证明：

$$\frac{N_0^2+KN_1^2}{4}\le E_7\le N_0^2+KN_1^2,$$
$$E_7'=-D_7,\qquad D_7\ge\frac{\mathcal S_0+K\mathcal S_1}{2}+\frac{\mu\tau}{4\kappa}(\|P_t\|_2^2+K\|P_{tt}\|_2^2)\ge0,$$
$$E_7(t_2)+\int_{t_1}^{t_2}D_7(s)\,ds=E_7(t_1),\quad E_7(t_2)\le E_7(t_1),\quad 0\le E_7(t)\le E_7(0),$$
$$\varepsilon\|E\|_2^2+\mu(\|H_x\|_2^2+\|H_y\|_2^2)+\kappa^{-1}\|P\|_2^2\le(4/\mu)E_7(t)\le(4/\mu)E_7(0).$$

导数/耗散结论在内部，图界、单调比较、实际积分平衡和原变量控制覆盖闭区间。积分可积性是证明结果，不是从单调性冒推。`auxiliary_current_GeneralWeakCk/Jet` 与 `auxiliary_initial_GeneralWeakJet` 给 (8.4)–(8.8)，其中 Z1/Z2/Qx/Qy 正是输入 `OriginalInterval.fields`，常数 8、4、16、8 及 S²/S⁴ 原样保持。

T=0 另用 `main_energy_GeneralWeakJet`：给定合法初始图状态及 `DegenerateJetCompatibility` 的三条初始导数层兼容，得到单点结论。不能从单点 ContDiffOn 或空内部方程决定任意 jet。本轮没有把该语义差别伪装成正则性等价，也不要求端点 PDE；这是实际解限制至单点的合法状态分支。T>0 入口不输入此独立兼容或端点 PDE。

## 本轮论文→声明→最终调用

名称公共前缀 `LeanPML.`，完整类型输出在本轮 `*_type_review.log`。

| 论文/数学步骤 | 声明与文件 | 调用/范围 |
|---|---|---|
| §1 分离 W¹,∞ 的代表 | `Analysis.exists_regional_lipschitz_representative`；`PML.separated_lipschitz_representative_x/y` | 弱测试积分→原函数→Lipschitz；张量测试/Fubini→一维；不输入连续性 |
| 区域幅度、原乘子/权重识别 | `RawWeakRegionalAbsorption.representatives/rawSpatial_ae/weighted_spaces_eq/energy_integral_original` | 构造旧入口，证明商类与积分不变；原剖面可在域外无界 |
| (5.1)、(5.2) | 复用 `Rectangle.weak_sharp_poincare`；新增 `ParameterCertificate.original_threshold_exact` | 精确常数用于 sharpEnergy/K/c*，旧保守实例不改 |
| (5.7)、(5.8) | 复用 `OriginalInterval.scalar_memory_both/scalar_memory_physical_x/y`、`auxiliary_weak_memory_bound` | 实际加权/L² 商类与 Bochner 积分；每个时刻 a.e.，不交换时间与零测集量词 |
| §5.3 | `historical_energy_independent_GeneralWeak`、`twoLayerEnergy_independent_GeneralWeak` | 一般弱系数的代表在证明内构造，已证合法提升唯一性给实际能量选择无关 |
| (6.6) | `V7ClosedCkCore.regularity`→`V7TimeRegularity.flux_second/toOriginalJet` | 输入是真实 Cᵏ；λ_tt 为推导；非解正则性自动传播定理 |
| (6.7)–(6.10) | `OriginalInterval.main_energy_GeneralWeakCk/Jet` | 同一原解的真实两层，内部构造弱 Green 和精确 Poincaré |
| (8.4)–(8.8) | `auxiliary_current_GeneralWeakCk/Jet`、`auxiliary_initial_GeneralWeakJet` | 当前能量及初值能量直接控制输入原变量 |
| (10.1) 最小分支 | `ParameterCertificate.original_threshold_min/original_threshold_exact` | $\min\{\pi/\sqrt{48},\pi^2/1152,1/24\}=\pi^2/1152$；复用 c=1/128,S=1/512 |
| (10.2) | `Examples.OriginalPower.absorption/absorption_branches/represented_profiles` | 全族 m≥2、0<ηx,ηy≤1/512；原剖面等于域内技术扩展，非 C∞ 伪装 |
| 非零与退化调用 | `Examples.GeneralWeak.static_main_call/static_ck_call/static_energy_positive/static_energy_constant/static_dissipation_zero`、`original_profile_main/four_branch_main` | 非零原八式静态解调用；全剖面零解入口证书与非零解存在性分开 |

## 输入表示、依赖与剩余范围

`RawWeakRegionalAbsorption` 采用区域有界可测代表及有界弱导数的测试函数定义，是实际 W¹,∞ 表示。普通系数乘子由有界性构造；能量权重不要求有界或正吸收下界。代表 a.e. 替换保持实际加权闭子空间，并通过等距映射保持恢复；零区没有被删掉。`original_profile_main` 在证明内选择代表并调用主定理；非恒定性由 `representative_nonconstant` 真正验证。

依赖顺序：真实弱导数→分布原函数→连续代表→原式/权重等价搬运→历史与兼容保持→同源路径→已证弱 Green/精确 Poincaré→已有能量代数/闭合→FTC/单调→原变量控制。没有 Green、Poincaré、全时段兼容或目标能量结果作为原解输入。

正反模型对应复用 `WeakPrimitiveSystem` 和 `primitive_to_original_WeakOn`：实际图空间、内部时间、真实导数、μ≠0 和正确极化关系。它不是任意分布解的无正则性等价理论。所有相等按商类/适当 a.e. 理解，不在任意点读取 L² 值。

当前不再保留独立系数连续性、保守常数或指数核识别差异。仍明确区分实际先验正则性与一般存在/传播：不证明一般解存在唯一性、严格/指数衰减、任意幅度或任意八变量初值稳定性。没有以“有限加权范数”代替 C²。T=0 的合法初始 jet 分支如上；不宣称单点函数值决定导数。可选 Laplace、V6 历史、R/D 分支不属于本轮。

## 阅读与复现

先读 `exists_regional_lipschitz_representative` → `RawWeakRegionalAbsorption.representatives` → `main_energy_GeneralWeakCk`。在 InfoView 中跟随具名 have/calc，F12 查结构字段，导入陈旧时 **Lean 4: Restart Server**。

在工程根目录运行：

```bash
python3 scripts/run_logged.py --stage v1.0_finalization lake_build lake build
python3 scripts/run_logged.py --stage v1.0_finalization axioms_audit lake env lean Audit.lean
```

最终核验及源码哈希：[本轮验收](../logs/v1.0_finalization/acceptance.json)；隔离工程复用固定依赖缓存、没有拷贝本项目编译产物：[隔离结果](../logs/v1.0_finalization/isolated_result.json)。真实失败和修复均保留；旧 acceptance/文档哈希不覆盖。PDF 的每个新标记另见 [证据账本](../docs/pdf_formalization_marks.md)。

---

# 以下为此前报告（历史原文保留）

# v1.0 当前已核验版本：矩形弱图空间兼容原解的先验能量定理

> 2026-10-14 closeout 最新对齐状态：本轮新增连接已验证，但 V7 原文逐项对齐仍未完成。一般连续代表、精确 π 常数及标量指数核识别仍列为缺口。下文既有“当前版本完成”指已列明假设与保守常数下的版本，不表示这些差异已经消除。详见本文件 closeout 追加节及 `logs/v1.0_closeout/semantic_review.md`。

用途：给出本轮**实际弱原八变量入口**的命题、输入、证明链和范围。下方旧报告完整保留，旧“尚未完成”是对应时间的历史状态。当前数学实现、两阶段完整构建、公理审计、隔离复现和 PDF 验收均已通过；v1.0.1–v1.0.3 按下述准确范围登记完成。

## 阶段及源码入口

| 阶段 | 本轮补齐的数学内容 | 正式源码与声明（公共前缀 `LeanPML.`） |
|---|---|---|
| v1.0.1 | 在原 H₀¹ 定义上补齐粗糙系数乘积的内部紧支光滑图逼近；函数和两个实际偏导同时 L² 收敛。复用此前一般光滑零迹桥接、真实加权商类及嵌入。 | `PML/WeakZeroProduct.lean`：`PML.weakCoefficientMul_mem_zeroBoundaryGraph`；`Rectangle/WeakCompactApprox.lean` |
| v1.0.2 | 区域分离弱系数、零迹乘积保持、合法双提升唯一、实际历史和五不变量、原辅助 ODE 到已证加权传播。弱 Green/Poincaré 沿用既有证明。 | `PML/SeparatedWeakCoefficients.lean`、`LiftUniqueness.lean`、`WeakLiftCompatibility.lean`、`WeakOriginalSystem.lean`、`WeakPrimitiveSystem.lean` |
| v1.0.3 | 从弱原八式构造同源两层及所有分析接口，合成 (6.7)–(6.10)，连接原 p/r 积分、非零静态原解和四分支。 | `PML/WeakPathAssembly.lean`、`WeakFiniteProblem.lean`、`MainWeakRectangle.lean`、`WeakCanonicalEnergy.lean`；`Examples/WeakStaticMode.lean`、`WeakBranchRegression.lean` |

推荐最终声明：`PML.Weak.main_energy_estimate_RegionalWeak`。它在证明体内调用 `OriginalInterval.main_energy_estimate_WeakOriginal` 并构造 `finiteProblem`。输入没有现成能量问题、Green/Poincaré、全时段兼容或能量目标。`EnergyConclusions` 是**输出**，不是原解结构中的假设。

本轮采用路线图 v1.0.3 允许的“已核验版本及准确差异”。它是弱空间、强时间正则的先验结果，不声称覆盖任意分布解或原文全部最弱解释。

## 完整命题与输入审查

取非退化矩形 $\Omega=(x_-,x_+)\times(y_-,y_+)$，使用整个矩形限制的二维 Lebesgue 测度。材料 $\varepsilon,\kappa,\tau,\mu>0$，采用已证明的保守常数

$$C_P=2L_x,\qquad A=\varepsilon+2\kappa,\quad K=8\mu A C_P^2,$$

以及原有 $c_*$ 定义、$0<c\le c_*$、$0\le S\le c/4$。区域入口 `WeakRegionalAbsorption` 的原 p、r 幅度只在闭坐标区间要求。内部零延拓代表与原 p(x)、r(y) 在 Ω 内及限制测度 a.e. 相等。

输入按实际结构逐项列在下面；完整 Lean 类型保存在本轮 `final_type_review` 日志。

| 输入对象 | 实际字段、用途及与 V7 的关系 |
|---|---|
| `RegionalWeakCoefficient`、`SeparatedRegionalWeakCoefficients` | 区域有界可测函数及两个区域有界弱导数，通过内部紧支光滑测试配对绑定；另有 p(x)、r(y) 的域内分离识别。横向弱导数为零由 Fubini/FTC 证明，不作为字段。无全轴 C∞ 条件。 |
| `WeakRegionalAbsorption` | 上述弱系数、c/S、区域非负和幅度、Ω 内连续代表。连续代表是当前明确选用的技术表示；没有另证任意 W¹,∞ 商类自动选取连续/Lipschitz 代表。域外技术代表不要求满足物理幅度或 PDE。 |
| `OriginalState`、`OriginalAt` | E、Hx、Hy、P、Z₁、Z₂、Qx、Qy 都是实际 L² 商类；逐条八式及 `HasDerivAt`。E 由 H₀¹ 图识别，旋转通量 $(\mu H_y,-\mu H_x)$ 由真实 H(div) 图识别；无 H·n=0 或磁散度条件。 |
| `OriginalInterval` | T≥0，原八场在 Icc 连续，E 的 H₀¹ 图和 λ 的 H(div) 图在 Icc 连续，空间识别覆盖 Icc；原八式及真实时间导数只在 Ioo。u₀∈H₀¹、q₀∈L²，五个兼容条件只在 t=0。 |
| `OriginalJet` | E 的真实 H₀¹ 导数 E_t，λ 的真实 H(div) 导数 λ_t；E_tt、P_tt 和 λ_tt 两分量的实际 L² 导数。E_t 图、λ_t 图、P_t/P_tt 在闭区间连续。特别是 λ_tt 分量仍作为显式正则性输入，没有把它称为仅由原式自动产生。P_tt 连续用于耗散时间可积性和 FTC。 |
| 初始加权元素 W₀x/W₀y | 实际 WeightedL2 成员，并要求物理恢复等于初始 $\lambda-\nabla u_0$。全时段成员、零区保持、加权历史的连续及内部导数由演化证明；没有将它们作为原解输入。 |
| `DegenerateJetCompatibility` | 只在 T=0 时要求初始导数层的极化和两个空间兼容关系。T>0 时内部演化加连续性推出端点约束；不能从 T=0 的空内部推出任意导数数据。 |

这里空间正则性已经从旧联合 C∞、C(K) 一致范数表示放宽为真实弱图空间。**旧 v0.5 定理和其输入原样保留**。本轮不预先要求未知场 C∞，不对无界能量权重作空间求导，也不把它当成普通 L² 上的有界乘子。

与 V7 (6.6) 的对照：u 的 H₀¹ 历史由 E 图连续及图导数得到；P 的第二 L² 时间导数被明确绑定，P_tt 连续为输入；φ 的加权历史及其内部两次导数通过连续线性强迫算子得到，所需梯度/通量导数来自上述 jet；λ 的 H(div) 一阶图导数与 L² 分量二阶导数分开陈述。没有宣称“有限加权范数 ⇒ C²”。本入口不要求端点普通双侧导数或端点 PDE；函数类型虽写 ℝ→空间，所有正则性条件均按声明限制在 Icc/Ioo，域外不要求原方程。

## 已证明的输出：原文 (6.7)–(6.10)

记 $\mathcal E_7$、$\mathcal D_7$ 为现有 `energy7`、`dissipation7` 在该原解实际两层路径上的值，$\mathcal N_7^2=N_0^2+KN_1^2$。

- 对所有 $t\in[0,T]$：$\mathcal N_7^2/4\le\mathcal E_7\le\mathcal N_7^2$，并有 $0\le\mathcal E_7(t)\le\mathcal E_7(0)$。
- 对所有 $t\in(0,T)$：`HasDerivAt` 形式的 $\mathcal E_7'=-\mathcal D_7$，以及准确剩余耗散

$$\mathcal D_7\ge\tfrac12(\mathcal S_0+K\mathcal S_1)
 +\frac{\mu\tau}{4\kappa}(\|P_t\|_2^2+K\|P_{tt}\|_2^2)\ge0.$$

- 闭区间上的 `AntitoneOn`；对 $0\le t_1\le t_2\le T$，真实 `IntervalIntegrable` 及

$$\mathcal E_7(t_2)+\int_{t_1}^{t_2}\mathcal D_7(s)\,ds=\mathcal E_7(t_1).$$

- 对输入原场本身（已证明磁重构与输入 H 相同）：

$$\varepsilon\|E(t)\|_2^2+\mu(\|H_x(t)\|_2^2+\|H_y(t)\|_2^2)+\kappa^{-1}\|P(t)\|_2^2
\le\frac4\mu\mathcal E_7(t)\le\frac4\mu\mathcal E_7(0).$$

同一命题处理 T=0、t₁=t₂ 和两个端点。初值界是推论，不是输入。图范数控制的是兼容状态，不是任意八变量裸 L² 范数的双向等价。

`RegionalIntegrals.energy_integrable_and_eq`、`dissipation_integrable_and_eq` 正式把既有块积分换回**输入原剖面** p(x)、r(y)，同时证明密度可积。两层直接复用同一单层组合；没有通过不可积积分的总定义制造能量。

## 关键数学连接

1. **零迹乘积。** 对 m 乘内部测试函数的粗糙乘积做真实光滑卷积；同一卷积的两个实际偏导等于弱偏导代表的卷积。三个 L² 收敛给出原图范数收敛，再通过连续乘积图算子推广到整个 H₀¹。没有用普通 L² 密度代替梯度收敛。
2. **规范唯一。** `CompatibleLift.u_unique` 从同一原八状态的两份重构推出横向差值约束和零区梯度条件；利用坐标乘子的 H(div) 通量与弱 Green 得到 pg=rg=0，再以连续系数的正集为开集，用弱局部性和 Poincaré 得到 g=0。这条路线不必使用额外的 bg=0，因而不需要除以 b。加权物理恢复单射给出 `state_unique`、`energy_independent` 和 `twoLayerEnergy_independent`。两层声明分别针对其同一原状态/导数状态的合法提升；不把独立状态叫作同源路径。
3. **实际历史。** `historyU/historyQ` 是 H₀¹/L² Bochner 积分；`all_invariants_eq_initial` 先保留任意初始常数场。`OriginalInterval.reconstruction` 再从五初始零值得到全时段兼容，包括两个磁辅助量。`historicalLift` 的兼容字段由这个结果填入；`historical_energy_independent` 将规范唯一连接到主定理原层能量。
4. **加权传播。** `OriginalInterval.auxiliary_hasDerivAt` 从八式消去 Q 得到真实普通 L² 辅助演化；`weighted_membership`、`memory_bound` 将它接入已完成的 Bochner 加权历史，给出全时段成员、零区保持和精确 (5.8)。采用与阻尼 ODE 等价的空间值历史路线；未新增指数核逐点代表公式的商类定理，不把旧点态 (5.7) 冒充它。
5. **同源与能量。** `baseState_hasDerivAt`、`firstState_hasDerivAt` 逐项绑定两层；`first_evolution` 对邻域内成立的原层 primitive 方程真实求导。H₀¹/H(div) 坐标投影提供时间—空间交换，weakGreenDomain/weakPoincareDomain 由已证明定理填入。最终调用旧能量代数、耗散预算和有限区间 FTC，没有重写目标为假设。

依赖链：真实弱图/加权空间 → 弱 Green/Poincaré、弱系数乘法 → 原八式历史/五不变量 → 加权恢复与同源 jet → `finiteProblem` → `main_energy_estimate_WeakOriginal` → 区域推荐入口。规范唯一另由弱乘积、弱 Green、局部性闭合，再连接实际合法提升及能量定义。

## 非零原解与回归

- `Examples.WeakStaticMode.main_call` 和 `nonzero_static_regression` 构造单位矩形上的真实原解：p=S、r=0、λ=(0,1)、Hx=−1、Qx=S，其余原变量为零。参数由已有 CP=4、A=3、K=384、c=1/16384、S=1/65536 证书提供。证明全部八式、真实导数、初始兼容、加权成员，**实际调用新主定理**。能量闭区间严格正且恒定；D=0 的正式声明在内部。它是 §11.3 机制的常数剖面允许变体，不是原紧支 F 配置原样核验。
- `Examples.WeakBranchRegression.all_four_configurations` 分别构造真实零原解并调用同一主定理，覆盖全零、x 单向、y 单向及双向，包括 T=0。它们是分支回归；非零调用由上一项承担。
- `Examples.WeakRegression.growthInitial_no_weak_compatible_lift` 使用旧完整场增长族的实际初值和非零梯度平方，证明全零吸收时不存在新合法兼容提升，排除误纳入。旧增长八式与任意大时间障碍证明保留。
- `single_layer_scope_preserved` 调用旧精确负耗散定理，仅否定已定义的指定单层候选。

## 验收、学习和未覆盖事项

本轮完整构建、公理审计、结构字段检查、当前源码哈希、隔离目录和最终 PDF 检查集中在 [总验收](../logs/v1.0.3/completion_20261014T122020/acceptance.json)。两阶段独立日志见其中链接；此前失败和修复日志全部保留。隔离构建不复制项目编译产物，但复用精确依赖缓存，不能称为完全无缓存构建。

建议先阅读三条声明：

1. `PML.weakCoefficientMul_mem_zeroBoundaryGraph`：粗糙乘积怎样进入原闭包。
2. `PML.Weak.CompatibleLift.u_unique`：相同原状态怎样消除规范差值。
3. `PML.Weak.main_energy_estimate_RegionalWeak`：所有真实输入怎样进入最终输出；随后 F12 到 `finiteProblem` 和 `EnergyConclusions`。

VS Code 打开工程根目录，光标放在具名 `have` 或 `calc` 后查看 InfoView；F12 查实际定义，尤其检查结构每个字段。导入未刷新时执行 **Lean 4: Restart Server**。固定 mathlib 的卷积微分、a.e. 收敛和图闭包推广源码位置见 [零迹乘积审查](../logs/v1.0.2/weak_zero_product_20261014T1202/semantic_review.md)；FTC 使用 `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`。

```bash
cd '/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML'
python3 scripts/run_logged.py --stage v1.0.2 lake_build lake build
python3 scripts/run_logged.py --stage v1.0.2 axioms_audit lake env lean Audit.lean
python3 scripts/run_logged.py --stage v1.0.3 lake_build lake build
python3 scripts/run_logged.py --stage v1.0.3 axioms_audit lake env lean Audit.lean
```

**没有新增的结论：**最优 π 常数；任意 W¹,∞ 商类的连续代表选择定理；一般非零弱边界迹理论；最低时间正则性或任意分布解；解存在唯一性、严格/指数衰减；任意幅度、分数阶或数值离散。新弱原系统已足以推出上述先验结论；没有另行扩展 v0.4 的光滑双向八式对应为一套任意低正则双向等价理论。无外部发布、提交、推送或依赖更新。

---

# 2026-10-14 前次 continuation 报告（原文保留，以下“当前/本轮”指当时）

# 本轮 v1.0 数学补齐：当前状态

用途：记录已经进入正式构建的数学增量及其准确边界。本轮补齐 M1，完成 M2 的实际加权成员传播、精确 (5.8) 及导数右端估计，补上 M3 的区域弱乘积与方向 Poincaré。**M3 的规范唯一性和 M4 的弱原八变量主定理仍未完成，v1.0.2、v1.0.3 不能整体登记完成。** 下方保留上一轮报告，旧“尚未完成”表示当时状态。

## 本轮实际声明与证明内容

| 单元 | 文件、主要声明（省略 `LeanPML.` 前缀） | 已证明的准确范围 |
|---|---|---|
| M1 | `Rectangle/SmoothWeakClosure.lean`：`smoothToWeakH1_mem_zeroBoundaryGraph` | 任意旧 `SmoothField` 四边零迹，进入原有 H₀¹ 图闭包。输入没有闭包成员或逼近序列。 |
| M1 收敛与调用 | `cutoffSequence_toL2_convergence`、`rectangleBubble_weakH01` | 真正内部紧支 C∞ 截断，函数、x/y 偏导同时 L² 收敛；非预先内部紧支的多项式泡函数调用并证明非零。 |
| M2 空间算子 | `PML/WeightedForcing.lean`：`weightedForcing`、`auxiliaryRate_weak_norm_sq` | 利用 $w_i\sigma_j^2\le cS$ 构造普通 L²→实际 WeightedL2 的强迫算子，绑定真实弱梯度/H(div) 坐标。不是将无界 w 作为有界乘子。 |
| M2 成员保持 | `PML/AuxiliaryWeightedEvolution.lean`：`physical_auxiliaryWeightedHistory`、`auxiliary_weak_field_membership` | 从初始加权元素、普通 L² 连续路径及内部真实演化，构造 Bochner 加权历史并识别其物理恢复；推出所有 t∈[0,T] 的加权成员与零区消失。 |
| M2 时间估计 | `Analysis/DissipativeMemoryEstimate.lean`：`dissipative_memory_square_bound` | 固定非负阻尼 Hilbert ODE 的真实范数估计；由正则化范数求导、FTC 和时间平方积分估计推出。不是预设目标传播估计。 |
| M2 (5.8) | `PML/WeightedMemoryBound.lean`：`auxiliary_weak_memory_bound` | 两个实际弱场分量上，证明原常数 $2$ 和 $4cSt$ 的 (5.8)。y 方向使用 C.swap，正确交换 p、r。 |
| M2 实际积分 | `auxiliary_weighted_integral_bound` | 输入普通 L² 场 φ(t) 的密度 $w_x\phi(t)^2$ 可积，并满足单方向 (5.8)；没有依赖不可积积分的总定义。 |
| M2 导数层 | `auxiliaryRate_weak_norm_sq`、`hasDerivAt_auxiliaryRateX` | $\|\phi_t\|_w^2\le2cS(\|\nabla u\|^2+\|\lambda\|^2)$ 的实际加权右端；若 h、l 有真实 L² 导数，右端路径也真实可导，并满足同一估计。原弱八式提供这些导数层数据的总装仍待 M4。 |
| M3 区域弱乘积 | `PML/WeakCoefficients.lean`：`weakCoefficientGraphMap_mem`、`weakCoefficientMul_derivatives` | 区域 W¹,∞ 可测有界代表及真实弱导数，乘以 H₀¹ 得到 H¹，并证明实际 Leibniz 坐标；未证明乘积仍在 H₀¹。 |
| M3 方向控制 | `Rectangle/WeakDirectionalPoincare.lean`：`weak_directional_poincare`、`weak_zero_of_dx_zero`、`weak_zero_of_dy_zero` | $\|g\|_2^2\le(2L_i)^2\|\partial_i g\|_2^2$；单个弱偏导为零即可推出 H₀¹ 图元素为零。这不是提升唯一性。 |

### M1：为何是 H¹ 逼近

四边截断使用真实 `Real.smoothTransition`。零迹和导数界给出 $|f|\le M\,\mathrm{dist}(\cdot,\text{边})$，抵消截断导数中的 $1/\delta$；因此两个偏导都有与截断尺度无关的上界。每个内部点附近最终截断恒等于 1，故函数及实际偏导最终相等。有限矩形上的支配收敛分别控制三个平方差积分，再得到原三坐标最大值图范数中的收敛。没有用普通 L² 密度代替一阶导数收敛。

### M2：初始成员如何传播

写 $h=\partial_i u$、$l=\lambda_i$，普通 L² 辅助场满足内部真实方程

$$\phi_t=\sigma_jh-\sigma_i l,\qquad l=h+\phi.$$

`auxiliaryWeightedHistory` 在已证明完备的 WeightedL2 中定义

$$W(t)=W_0+\int_0^t \mathcal R(h(s),l(s))\,ds.$$

先由连续线性强迫算子得到可积性和加权路径连续/内部可导，再由普通 L² 的 FTC 与物理恢复映射证明 $\operatorname{physicalL2}(W(t))=\phi(t)$。因此全时段加权成员不是输入。零区从恢复后的零值性质与这条由演化推出的识别得到，仍依赖初始加权元素及其初值识别，绝非仅用 p=r=0。

空间兼容把已构造路径的导数改写为 $W'=-B W+F$，其中 $B$ 是非负吸收的有界乘子，$\|F\|^2\le2cS\|h\|^2$。对 $\sqrt{\|W\|^2+\delta}$ 求导避免除以可能为零的范数；FTC、消去 δ 及真实时间 Cauchy 估计给出

$$\|W(t)\|^2\le2\|W_0\|^2+2t\int_0^t\|F(s)\|^2ds.$$

两方向合并即得到

$$\|\phi(t)\|_w^2\le2\|\phi_0\|_w^2+4cSt\int_0^t\|\nabla u(s)\|_2^2ds.$$

左端在 Lean 中是已识别加权历史的两个平方范数之和，不使用普通乘积类型的最大值范数代替欧氏平方和。单方向积分定理同时交付原辅助场密度可积性。

这里采用等价的真实空间值历史表示与 ODE 识别；**没有另行完成 (5.7) 指数核逐点公式在空间商类上的提升定理**。旧点态 (5.7) 保留。新结果不要求逐点代表可导、不输入全时段加权成员，也不由有限范数估计宣称 C²：加权连续性和内部 C¹ 来自实际历史构造；更高阶求导须另有 h、l 的真实导数证据。最终弱 PDE 的同源导数层仍未组装。

时间假设均明确限制在闭区间连续、开区间真实演化；t=0、t=T、T=0 由同一命题覆盖，不要求端点 PDE 或端点导数。低层 `SpatialAbsorption` 使用有界可测空间代表；旧区域截断方法仍可提供该代表，但本轮没有宣称新的分离 W¹,∞ 原解入口已总装。

### M3：新的系数空间没有隐藏哪些结论

`RegionalWeakCoefficient` 只含区域有界函数、两个区域有界弱导数及真实测试函数配对。幅度条件只在矩形 Ω，零延拓只用于普通 L² 乘子；没有声称零延拓跨边界仍保持原弱导数。乘积法则先对紧支测试证明，再以图映射连续性推广到 H₀¹ 闭包，输出 H¹。

没有输入 Green、Poincaré、Leibniz、规范唯一性或能量结论。也没有要求粗糙系数全轴 C∞。`hasDerivAt_weakCoefficientMul` 通过真实连续线性图算子求导，不能将逐点可导冒充图范数可导。

## 非零调用

- `Rectangle.rectangleBubble_weakH01`：四边零迹多项式泡，调用 M1 一般桥接，非预先内部紧支。
- `Examples.WeightedEvolution.nonzero_memory_bound`：实际非零 L² 场的 $e^{-t}f$ 路径，调用新的精确 (5.8)；`nonzero_weighted_propagation`、`nonzero_weighted_path_derivative`、`nonzero_rate_derivative` 分别核验成员、真实导数及导数层估计。这是辅助演化实例，不是新弱八变量解。
- `PML.weakCoefficient_nonzero_call`：实际非零 bump 调用一般区域弱乘积；常数 1 系数不是新的非光滑系数实例。
- `Rectangle.nonzero_directional_poincare_call`：真实非零 bump 对 x、y 两方向调用。
- 旧 v0.5 静态态、增长族、单层失败和退化回归仍进入当前总构建；未改名为尚不存在的弱主定理回归。

## 首个仍缺定理及下游影响

M1 已补齐旧验收中列为首缺的连接。v1.0.1 的该数学缺口关闭；不附带宣称一般弱迹核的完整刻画。

M3 首缺的明确目标是：对 `m : RegionalWeakCoefficient D`、`g : zeroBoundaryGraph D`，证明 `weakCoefficientMul D m g ∈ zeroBoundaryGraph D`。下一引理是：内部紧支的弱乘积 m*f 具有同域内部紧支光滑 **图范数** 逼近。M1 只能用于光滑 f，不能直接套到非光滑 m*f。

随后尚需分离系数横向弱导数零、合法双提升的差值约束，以及零水平集上的弱梯度局部性，才能从 bg=0 等推出 ∇g=0，再使用 Poincaré。**提升规范唯一性、能量与未固定提升选择无关仍未证明。**

M4 首个尚未完成的组装是：从真实弱八条原方程和初值兼容构造历史提升的五个场不变量保持（尤其两个磁辅助不变量）及 H₀¹/加权同源两层路径。当前未新建一个隐藏全时段兼容的“弱解”结构来替代它。因而没有新的弱版 (6.7)–(6.10)、非零弱主定理调用或新弱解存在性结论。

一般弱场可用上述新分析定理，无需联合 C∞、C(K) 代表；但 **v0.5 主定理的输入没有改变**。保守 $C_P=2L_x$、K 和参数证书原样保留；方向辅助估计的 $2L_y$ 不替换主能量常数。精确 π 常数、一般存在唯一性、严格/指数衰减均未新增。

## 验证与学习

建议优先读：
1. `smoothToWeakH1_mem_zeroBoundaryGraph`：从三坐标收敛到闭包；
2. `auxiliary_weak_memory_bound`：实际弱梯度、双方向及原常数；
3. `weakCoefficientMul_derivatives`：弱乘积真正输出了什么。

InfoView：光标放在具名 `have`/`calc` 后查看输入和目标；F12 跳到定义。导入未刷新时执行 **Lean 4: Restart Server**。新加通用时间估计已由真实 WeightedL2 定理调用，不是孤立的抽象辅助库。

本轮完整构建、独立公理审计、实际类型及源码哈希集中在 [新时间戳验收](../logs/v1.0.2/continuation_20261014T110047/acceptance.json)；M1/M3 和 M2 的结构字段审查也在同目录。所有旧 acceptance 与失败日志保留。数学总装 M4 未完成，故本轮没有执行“总装完成后”的新隔离发布复现；下方旧 clean_result 仅是旧源码历史证据，不能用来验证本轮新增源码。

```bash
cd '/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML'
python3 scripts/run_logged.py --stage v1.0.2 continuation_lake_build lake build
python3 scripts/run_logged.py --stage v1.0.2 continuation_axioms_audit lake env lean Audit.lean
```

PDF 只追加本轮已证范围，位置、限定文字、源码和日志在 [既有标注账本](../docs/pdf_formalization_marks.md)。不对 §5.3 规范唯一性或弱版 (6.7)–(6.10) 增加完成勾。

---

# 上一轮报告原文（历史快照，以下“本轮”指上一轮）

# 弱空间证明进展与尚未闭合的主定理

用途：记录本轮实际证明、输入条件、调用证据和缺口。**本轮为部分交付：v1.0.1 的一般零迹逼近尚缺；v1.0.2 未整体验收；v1.0.3 未合成新的弱原系统主定理。** 不把下面的空间结论当成 (6.7)–(6.10) 的弱解版本。

## 真实起点与来源

本轮核对了 `logs/v1.0.1/acceptance.json` 的全部 61 个正式文件哈希，开始修改前全部一致。V7 Markdown 仍为 `0a7f73a25cb119eeb75b3e7b3c3f2fbb3b319250f3354ed4dcad0ecff8eff4fb`。路线图中“待实现”属于规划文字；当前状态以本轮逐项证据为准，未改路线图。基线及比较见 [v1.0.2 日志](../logs/v1.0.2/baseline_comparison.json)。

固定 Lean 4.31.0 / mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`。未更新依赖。所有原正式证明文件保持，只有总导入和审计追加；旧 v0.5 主定理及其回归仍在构建内。

## 已证明的准确命题

下表名称均带前缀 `LeanPML`。这里的 $H_0^1$ 指已定义的 `zeroBoundaryGraph`，采用三个实际 L² 坐标的最大值图范数；旧 `graph_norm_sq_equivalence` 证明它与平方和图拓扑等价。

| 来源 | 正式声明 | 输入与输出 |
|---|---|---|
| V7 (7.5) 零迹式 | `Rectangle.weak_green` | 任意 `v : zeroBoundaryGraph D` 与 `L : weakHDivGraph D`，证明 $\langle v_x,L_x\rangle+\langle v_y,L_y\rangle=-\langle v,\operatorname{div}L\rangle$。没有通量法向零条件。 |
| 同式的旧接口连接 | `Rectangle.weak_green_domain`、`weakGreenDomain` | 图与实际 L² 像通过已证唯一性连接；接口的 Green 字段由前述定理填入，不要求调用者给 hGreen。标量域已限制为 H₀¹，trace/boundary 取零映射仅表示该域上的零迹接口，不是一般弱迹理论。 |
| V7 (5.1) 的保守常数版本 | `Rectangle.weak_poincare` | 任意该 H₀¹ 成员满足 $\|v\|_2^2\le(2L_x)^2(\|v_x\|_2^2+\|v_y\|_2^2)$。原文精确 π 常数仍未证明。 |
| 保守估计的旧接口连接 | `Rectangle.weak_poincare_domain`、`weakPoincareDomain` | 使用与 weakGreenDomain 相同的域/迹核；estimate 是本轮证明结果，无额外估计输入。 |
| 由 Poincaré 推出，原文未单列 | `Rectangle.weak_zero_of_gradient_zero` | 弱梯度两个分量为零时，整个 H₀¹ 图元素为零。**不是 §5.3 规范唯一性**：从规范约束推到零梯度尚未证明。 |
| 由 (6.6) 引出的分析连接 | `Rectangle.hasDerivAt_weakH1_coordinate`、`hasDerivAt_weakHDiv_coordinate` | 输入实际图范数路径的 `HasDerivAt`，通过有界坐标投影得到 L² 函数/梯度/散度的真实时间导数。输入不含交换公式，不从逐点导数跳到图范数导数。 |
| (5.7) 的固定空间点子结论 | `PML.auxiliary_memory_formula` | 实际实值时间函数 φ、g 在 [0,T] 连续，内部 `HasDerivAt φ (-σ*φ+(ρ-σ)*g)`，得到实际时间积分的变常数公式。σ、ρ 任意实常数；本引理中 g **尚未识别为某个弱场的梯度代表**。 |
| 由 (5.7) 推出的零点分支 | `PML.auxiliary_zero_absorption_preserved` | σ=ρ=0、连续、内部真实零导数及 φ(0)=0 推出区间内 φ(t)=0。没有将零吸收本身当作零初值。 |

所有内积均是实际矩形限制测度上的 L² 内积，故与代表元选择无关；对应乘积可积性复用 `Analysis.integrable_product`。弱导数仍由全部内部紧支光滑测试函数定义，没有把待证一般 Green 写入定义。

### 证明怎样从测试函数走到闭包

对固定通量 L，`weakGreenFunctional` 是图变量上的线性泛函

$$B(v)=\langle v_x,L_x\rangle+\langle v_y,L_y\rangle+\langle v,\operatorname{div}L\rangle.$$

弱散度定义给出测试图上 B=0；线性性给出其线性张成上 B=0；三个 L² 内积的连续性使核闭，故整个 H₀¹ 图闭包上 B=0。这里没有从未知弱场读取边界值。

Poincaré 使用不同的闭集：满足上述平方范数不等式的图变量集合。`span_test_has_smooth_zeroBoundary` 证明每个生成元的有限线性组合仍是光滑零迹函数，调用旧 `poincare_smooth`；三个坐标范数连续，故不等式推广到闭包。**没有用普通 L² 密度冒充梯度收敛。**

### (5.7) 的时间分析范围

证明真正计算 $(e^{\sigma t}\phi(t))'$，再用闭区间 FTC，最后将指数因子移入真实时间积分。ODE 只在 $(0,T)$ 要求成立；连续性覆盖闭区间；$t=0,t=T,T=0$ 均由同一命题覆盖，不要求端点 PDE 或导数公式。

它尚不是 L²/加权 L² 传播定理。没有证明时空可测性、空间积分交换、全时段加权成员、(5.8)、φ_t 的加权估计或 C¹/C² 加权正则性。PDF 对它只加限定说明，不给“辅助演化/加权保持全部完成”红勾。

## 非零调用与已有加权结果

[WeakAnalysis.lean](../LeanPML/Examples/WeakAnalysis.lean) 的 `nonzeroTest` 复用 v0.5 已证明的物理区紧支 bump：

- `nonzero_green` 实际调用新弱 Green，通量为该函数的真实梯度；
- `nonzero_poincare` 实际调用新弱 Poincaré，真实 unitSquare 的 CP=4，平方系数 16，函数在 L² 中非零；
- `nonzero_graph_path_derivative` 核验非恒定图路径 $s\mapsto s\,v$ 的真实 L² 梯度导数；
- `exponential_memory` 用 σ=1、ρ=0、φ=exp(−t)、g=0 调用变常数公式。

这些是新分析接口的非零回归，**没有新的弱 PML 主定理可供调用**。旧非零静态解、增长族和四吸收分支仍按 v0.5 的光滑定理验证；没有把它们更名为新弱实例。

`WeightedL2` 和 `WeightedL2Operators` 保持原文件。零延拓、a.e. 商类、物理恢复单射、普通 L² 嵌入、完备性和有界系数作用继续有效。w 可能无界，未被当成普通 L² 的有界乘子。尚无 W¹,∞ 乘法保持 H¹ 的新定理。

## 未完成项、依赖与对最终定理的影响

| 项目 | 当前缺口 | 影响 / 下一步 |
|---|---|---|
| v1.0.1 一般光滑零迹到 H₀¹ | 未构造内部紧支逼近并同时控制函数与两个导数。 | 需要矩形边界截断及边界条带上的导数误差估计，或等价的严谨图范数逼近。不能删除旧缺口；当前仅紧支子类有直接桥接。 |
| W¹,∞ 分离系数 | 现有有界 L² 乘法不含弱乘积法则；未构造本模型所需完整区域 W¹,∞ 系数接口。 | 后续必须证明测试乘积/逼近的合法性，不能保留全轴 C∞ 后称弱系数版本。 |
| (5.8) 与 φ_t 加权传播 | 只有点上的真实 (5.7)；尚缺空间积分、加权成员构造与识别。 | 不可把所有时间的加权成员作为传播输入；有限估计也不能替代加权 C²。 |
| §5.3 提升规范 | 未证明切片零迹、弱零水平集性质或等价路线。 | `weak_zero_of_gradient_zero` 只补最后一步；bg=0 等约束尚未推出 ∇g=0。不得宣称能量与未固定提升无关。 |
| 兼容空间及原系统弱映射 | 旧五不变量/双向八式依赖光滑代表；没有新的真实弱原解总装。 | 不能把旧原场字段直接视为新弱 PDE 定义。 |
| v1.0.3 最终定理 | 尚无从弱原八式构造的完整路径与问题对象。 | 未交付 (6.7)–(6.10) 的新弱原模型版本；图时间导数与空间接口只是已完成组件。 |

这不是发现原文数学结论错误，而是当前形式化证明链仍未闭合。没有使用占位公理，也没有将缺失结论改写成结构字段。

现阶段实际弱分析声明不要求未知场联合 C∞ 或 C(K) 代表；但 **v0.5 主定理的任何输入都没有放宽**。其全轴技术延拓、端点双侧可导性与内部 PDE 的区别仍以原光滑报告为准。新空间结论不提供一般存在唯一性、严格衰减或指数衰减。

## API、阅读与复现

建议按 `weak_green` → `weak_poincare` → `auxiliary_memory_formula` 阅读。VS Code 打开工程根目录；将光标放在 `have`/`calc` 后查看 Lean InfoView 的上下文与剩余目标，F12 跳转定义。新增导入未刷新时执行 **Lean 4: Restart Server**。

实际用到的固定 mathlib 声明：

- `Submodule.topologicalClosure_minimal`：`Mathlib/Topology/Algebra/Module/Basic.lean:177`；
- `Submodule.span_induction`：`Mathlib/LinearAlgebra/Span/Defs.lean:139`；实际类型保存在本轮类型核验日志；
- `HasFDerivAt.comp_hasDerivAt`：`Mathlib/Analysis/Calculus/Deriv/Comp.lean:389`；
- `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`：`Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:1142`；
- 普通 `Lp.dense_hasCompactSupport_contDiff`：`Mathlib/Analysis/Normed/Lp/SmoothApprox.lean:97`，**不是 H¹ 图范数内部紧支逼近**；
- `TemperedDistribution.MemSobolev`：`Mathlib/Analysis/Distribution/Sobolev.lean:149`，是全空间 Bessel 势表示，不直接等于本矩形 H₀¹。

```bash
cd '/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML'
python3 scripts/run_logged.py --stage v1.0.2 lake_build lake build
python3 scripts/run_logged.py --stage v1.0.2 axioms_audit lake env lean Audit.lean
python3 scripts/run_logged.py --stage v1.0.3 lake_build lake build
python3 scripts/run_logged.py --stage v1.0.3 axioms_audit lake env lean Audit.lean
```

本轮构建、审计、实际声明类型和失败修复记录分别保存在 [v1.0.2](../logs/v1.0.2/acceptance.json)、[v1.0.3](../logs/v1.0.3/acceptance.json)。阶段目录名只表示验证所属任务，不表示阶段整体通过。

独立工程复现没有复制本工程的 .olean/.ilean，包含当前所有正式源码（包括未提交文件）；依赖复用精确锁定包及其缓存，**不是完全无缓存测试**。实际隔离目录、哈希与命令见 [clean_environment.json](../logs/v1.0.3/clean_environment.json) 和 [clean_result.json](../logs/v1.0.3/clean_result.json)。

PDF 只追加本轮准确范围，旧光滑和条件性标记保留；具体位置及证据见 [标注账本](../docs/pdf_formalization_marks.md)。未给规范唯一性、(5.8) 或新的弱主结论添加完成勾。


## 2026-10-14：v1.0 closeout 新增连接（保留前述历史状态）

本轮六项对齐中：(6.6) 所需 λ_tt 已由真实图导数与辅助演化推出；(8.4)–(8.8) 已直接控制输入原 Z1/Z2/Qx/Qy 并接到初值能量；弱 primitive 反向重构的八个真实导数、八式及兼容已证明。新增加权空间算子指数记忆公式，与已有历史及原辅助场连接。非零静态路径调用了新正则性入口、反向映射和两个方向的核公式。

仍未完成：一般分离 W¹,∞ 的连续代表自动构造；原 (5.1) 精确 π 常数；算子指数与逐点标量指数乘法的识别。当前仍用 C_P=2Lx，区域连续代表仍单列，T=0 的初始导数兼容仍保留。因此“本轮已实现连接验证通过”与“V7 原文逐项对齐完成”分开登记，后者仍为否。

新增源码：`PML/WeakPhysicalControl.lean`、`PML/WeakV7Regularity.lean`、`PML/WeakReverse.lean`、`Analysis/OperatorMemory.lean`、`PML/AuxiliaryOperatorMemory.lean`、`Examples/WeakCloseout.lean`（均在 LeanPML 下）。逐字段和缺口核查见 `logs/v1.0_closeout/semantic_review.md`；构建、审计、隔离复现及最终哈希见该目录的验收记录。未更改旧数学证明、路线图、模型合同或依赖版本。
 
## 本轮新入口与原变量输出（2026-10-14 closeout）

`V7TimeRegularity.main_energy_and_auxiliary` 输出已有 `EnergyConclusions`（图范数双边界、真实能量律、定量耗散、单调性、积分平衡、输入 E/H/P 控制），并对每个闭区间时刻给出 `OriginalAuxiliaryBounds` 初值控制。输入为原八式的 `OriginalInterval`、13 项真实时间正则性证据、材料阈值、初始加权代表及 T=0 初始 jet 兼容。区域应用取 $C=A.spatial$，继续复用域内/a.e. 一致性与既有积分表示。

原变量控制保留论文系数：u 为 $8C_P^2$，φ 为 4，q 为 $16\kappa^2C_P^2+8\kappa\tau^2/\mu$，Z1 为 $8\epsilon^2S^4C_P^2$，Z2 为 q 的系数再乘 $S^4$，Qx/Qy 的平方和为 $4S^2$。右端能量可取当前值或初值。Z/Q 均直接识别为输入 `OriginalInterval.fields` 的原变量，范数是全矩形实际 L²。

弱反向方向输入明确的 H₀¹/H(div) primitive 图路径，输出八式和兼容，不声称任意低正则分布解等价。指数核使用有界吸收乘子 $B=M_p$（y方向交换），不读取商类指定点；算子核与标量核识别仍待证明。

下一优先任务是证明一维有界分布导数给出 a.e. 相等的 Lipschitz 代表，再构造分离系数入口。这应移除连续代表的独立输入，不能另添“存在代表”假设。精确 Dirichlet–Wirtinger 常数及算子核乘法识别另列缺口。当前保守版本及非零回归仍然有效。


本轮最终证据：`logs/v1.0_closeout/acceptance.json`。主工程完整构建与930条审计、隔离目录从零构建本工程及完整审计均通过；隔离复用精确依赖缓存。PDF第4、8、13页新增范围红勾，第10页增加正则性连接说明；旧221条批注全部保留。最终仍为部分收尾，未登记V7原文逐项对齐完成。


## 2026-10-14 v1.0_completion：本轮启动清单

基线：closeout 的全部正式源码/锁文件哈希逐项相符，见本轮 baseline 记录。当前实施顺序先补可独立接回原辅助场的指数核，不重复旧证明。验收前下表不表示完成。

| ROADMAP / 原文 | 可复用声明 | 本轮缺口 | 调用/证据要求 |
|---|---|---|---|
| v1.0.2 / (5.7) | operator_memory_formula、operator_memory_both | 有界乘子算子指数与标量核识别 | 原辅助场双方向，真实 Bochner 可积性 |
| v1.0.2 / 分离 W¹,∞ | WeakRegionalAbsorption、区域弱乘积 | 从弱导数构造连续代表，去掉独立连续输入 | 区域入口、非恒定调用 |
| v1.0.2 / (5.1) | weak_poincare 保守常数 | Dirichlet–Wirtinger、矩形 π 常数 | 最终入口及 §10 参数 |
| v1.0.3 / (6.6) | V7TimeRegularity.flux_second、toOriginalJet | 论文 Cᵏ 条件到各字段的充分性；端点解释 | 非空区间及 T=0 兼容审查 |
| v1.0.3 / (6.7)–(6.10),(8.4)–(8.8) | main_energy_and_auxiliary、原变量控制、规范唯一 | 接入上述代表和原常数后整体审计 | 非零静态、四分支、当前源码隔离复现 |

R/D、适定性、严格衰减不属于本轮任务。旧“已核验版本完成”与上述 V7 逐项对齐严格区分。


## 2026-10-14 v1.0_completion：实际验收结果

**当前新增版本已核验；ROADMAP v1.0 原文逐项对齐仍未完成。** 上一节为开工清单，本节为当前最终状态。一般分离 $W^{1,\infty}$ 的连续代表构造仍未闭合；不能以独立连续代表输入代替这项证明。

|任务/原文|本轮声明与实际调用|验收状态|
|---|---|---|
|(5.7) 算子核→标量核|`Analysis.dampingKernel_eq_scalarExpMultiplier` → `Weak.OriginalInterval.scalar_memory_both`、`scalar_memory_physical_x/y`|完成：实际加权商类、普通 L²、Bochner 可积性；逐时刻等式，不交换时间/a.e.量词|
|(5.1) 精确常数|`Rectangle.weak_sharp_poincare` → `sharpWeakPoincareDomain` → `OriginalInterval.sharpFiniteProblem`|完成：一维平方展开/FTC、两个方向切片与 Fubini、H¹ 图闭包极限|
|(10.1) 原数值阈值|`Rectangle.ParameterCertificate.original_parameters_threshold`、`original_parameters_explicit`、`original_amplitude_certificate`|完成：真实方形 $C_P^2=2/\pi^2$、$K=48/\pi^2$、$c=1/128$、$S=1/512$；严格用 $\pi>3$。不附带核验 (10.2) 全族，也未另证显示的 min 最小分支等式|
|(6.6)→真实时间路径|`Weak.V7ClosedCkCore.regularity` → `main_energy_RegionalSharpCk`|正长度区间充分性连接完成；真实 `ContDiffOn` 条件，并非将 OriginalJet 改名|
|(6.7)–(6.10)|`Weak.OriginalInterval.main_energy_estimate_SharpWeakOriginal`；`Weak.main_energy_RegionalSharpCk`|精确常数版本完成；区域连续代表仍输入，故未覆盖一般原文 W¹,∞ 入口|
|(8.4)–(8.8)|`sharp_original_auxiliary_control`、`sharp_original_auxiliary_initial_control`|直接控制输入 O.fields 的 Z1/Z2/Qx/Qy，以及 u/q/φ；保持原常数|
|一般弱系数代表选择|现有 `WeakRegionalAbsorption.p_continuous/r_continuous` 仍为输入|未完成；属于 v1.0 必要主线，不改列可选|

表中名称前缀分别为 `LeanPML.Analysis`、`LeanPML.Rectangle`、`LeanPML.PML.Weak`。精确完整类型见 [本轮类型输出](../logs/v1.0_completion/20261014T170234_873529_type_review.log)。

### 最终入口的输入与输出

推荐声明 `LeanPML.PML.Weak.main_energy_RegionalSharpCk` 接受非退化矩形、材料正性、区域分离系数及原 π 常数阈值、实际八变量 `OriginalInterval`、真实时间正则性和初始加权成员。`OriginalInterval` 的字段包含原八式的内部 HasDerivAt、全矩形 PEC 的 H₀¹ 表示、旋转磁通量 H(div)、闭区间连续、初始五兼容和初始零区条件；不输入全时段兼容或能量目标。

`V7ClosedCkCore` 的四项真实正则性为历史 $u\in C^2([0,T];H_0^1)\cap C^3([0,T];L^2)$、$P\in C^2([0,T];L^2)$、$\lambda\in C^1([0,T];H(\mathrm{div}))$。论文给出的 $u$ 的 H₀¹ C³ 条件更强；本轮只使用其中 C²。φ 的初始加权成员仍输入，实际演化历史、成员及所需导数复用已证结果。这里没有由有限范数估计直接推断 C²。真实 λ_tt 仍由已有图投影、兼容求导和辅助演化推出。

对 $T>0$，`canonicalInterval` 把 E/P 导数槽选为真实区间导数；内部由导数唯一性识别，闭端点由构造选择，**所有原八变量路径不变**。不要求端点 PDE 或端点能量导数公式。对 $T=0$，保留 `main_energy_estimate_SharpWeakOriginal` 的 `OriginalJet` 和 `DegenerateJetCompatibility`，不能把任意单点导数数据解释为解的唯一限制。这个分支没有从空内部推出额外事实。

输出 `SharpEnergyConclusions` 包括图范数双边界、内部 HasDerivAt 与原文定量耗散下界、闭区间 AntitoneOn/非负/初值界、真实 IntervalIntegrable 和积分平衡、输入 E/H/P 的控制；配套输出是原辅助变量的初值能量控制。既有提升选择无关定理 `CompatibleLift.twoLayerEnergy_independent` 对任意 K 有效，直接适用于精确 K，不需重证。既有弱反向八式保留。当前仍是给定足够正则兼容解的先验定理，不是一般适定性。

### 非零调用与剩余证明

`Examples/SharpWeak.lean` 中 `sharp_main_call` 覆盖 $T\ge0$，`canonical_main_call` 调用新 Cᵏ 入口，`sharp_nonzero_static_regression` 保持非零静态态的正能量、常值和零耗散。`Examples/ScalarKernel.lean` 的 `nonconstant_profile_scalar_kernel` 在真实非恒定剖面上调用核识别；它不冒充一般 W¹,∞ 代表选择。旧全零、两种非对称边层、双向吸收、不兼容增长和单层失败仍进入本轮完整构建/审计。

首个未闭合引理：在区间上，由 $\int f\eta'=-\int d\eta$（所有紧支光滑 η）和 $f,d\in L^\infty$，证明 $f=c+\int_a^x d$ a.e.，再构造闭区间 Lipschitz 代表。之后需连接二维分离弱测试关系、区域幅度及代表替换不变性，并去掉最终系数入口的独立连续性输入。已检查原函数/零弱导数路线及卷积路线；准确缺少的测试函数原函数/一致梯度估计见 [语义记录](../logs/v1.0_completion/semantic_review.md)。现有要求 AC 的定理不能反过来证明 AC，没有以普通可导定理冒充弱导数结果。

### 验证与阅读

正式工程构建 3105 jobs 通过；完整公理审计 997 项通过（新增 67 项），无 `sorryAx`；实际类型审查通过。当前未提交源码在隔离目录从零构建本项目并审计通过，只复用精确依赖缓存，未复制本项目编译产物。见 [验收](../logs/v1.0_completion/acceptance.json)、[隔离结果](../logs/v1.0_completion/isolated_result.json)。

建议先读 `weak_sharp_poincare`、`scalar_memory_both`、`main_energy_RegionalSharpCk`，再读各自上游引理。VS Code 中光标放在 `have`/`calc` 后查看 InfoView；F12 跳到定义，修改导入后先 `lake build` 再 Restart File。复现命令见 README。本轮 PDF 7、8、10、13、15 页分别追加精确常数、标量核、Cᵏ/主结论、原变量控制、数值证书范围；未给连续代表缺口打完成勾。
