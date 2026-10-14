# 光滑兼容解类的全域先验能量定理

用途：把最终 Lean 命题翻译回纸面，列清原模型输入、技术正则性、已经推出的结论及未覆盖范围。本文对应已经分别验收的 v0.5.1–v0.5.3；数据证书与显式状态在下方登记，不把数据可容许性解释成一般解存在。

## 纸面命题与正式入口

空间为整个非退化矩形

$$\Omega=(x_-,x_+)\times(y_-,y_+),\qquad L_x=x_+-x_->0.$$

给定有限 $T\ge0$、正材料 $\epsilon,\kappa,\tau,\mu$，采用本工程已经证明的保守常数

$$C_P=2L_x,\quad A=\epsilon+2\kappa,\quad K=8\mu A C_P^2,
\quad c_*=\min\{K^{-1/2},\kappa\tau/(8AK),\kappa/(8A\tau)\}.$$

实际分离系数 $p(x),r(y)$ 时间不变，闭坐标区间内满足 $0\le p,r\le S\le c/4$，$0<c\le c_*$。全零吸收、单向边层和双向角层均允许。取原八变量 $E,H_x,H_y,P,Z_1,Z_2,Q_x,Q_y$，只要求原方程 V7 (2.1) 在 $(0,T)\times\Omega$ 成立，整个四边满足 PEC，初值五个不变量为零，初始原函数 $u_0$ 零边界，零吸收区初始 $\phi_0=0$。

再声明所选强光滑/一致范数/加权正则性及真实历史识别，得到：[MainSmoothRectangle.lean](../LeanPML/PML/MainSmoothRectangle.lean) 中

`LeanPML.PML.SmoothRectangle.main_energy_estimate_smoothRectangle`。

输入类型是 `SmoothCompatibleSolution`。其字段没有条件性能量问题、Green、Poincaré、混合交换、全时段兼容、耗散闭合、单调性或积分平衡。`s.problem` 是证明中由 `RegionalAbsorption.originalRegionalFiniteIntervalProblem` **构造的结果**，不能回填成原解输入。`SmoothEnergyConclusions` 是输出包，与输入包分开。

## 每项假设的来源与用途

| 输入 | 来源及用途 | 是否比论文强 |
|---|---|---|
| 非退化 `Rect` | §1全计算域；测度、四边Green、明确Poincaré常数 | 几何相同 |
| `RegionalAbsorption` 的c/S/p/r与闭域界 | (5.3)；建立系数界、乘法算子、零区与加权表示 | 幅度只在计算域；p/r的全轴C∞延拓是技术加强 |
| `ε_pos/κ_pos/τ_pos/μ_pos/c_le_threshold` | (1.1)、(5.2)–(5.3)；强制性、分母正性、两类耗散吸收 | 相同形式，但CP采用保守值 |
| `T_nonneg` | 有限区间T≥0；含T=0与闭区间比较 | 原时间范围 |
| `F`、`u0/q0` | (2.1)、(2.3)；实际原场及固定历史起点 | 不默认u0=q0=0 |
| `B : SmoothStateData` | 为兑现(6.3)/(6.6)选择实际光滑时间层 | 联合C∞技术延拓强于弱空间表述 |
| `regular : SmoothStateRegular` | C(K)一致范数路径及实际加权成员/连续可微，保证真正L²/加权导数 | 明确技术加强；不是由(6.6)自动推出 |
| `identified : LiftIdentified` | B的八槽必须等于实际积分历史及磁场/辅助场 | 代表识别与正则性；不是独立两层状态 |
| `history_regular` | 八个原场沿时间连续、实际u积分历史联合光滑；用于FTC和混合偏导 | 本轮技术表示，不要求域外PDE |
| `equations : OriginalOn` | 全部八条方程及真实HasDerivAt，只在内部时空域 | 方程相同；空间可导证据由光滑识别推出 |
| `initial` | (2.4)、§5.2；只在t=0兼容，随后证明保持及无源primitive对应 | 没有预设全时段兼容 |
| `zero_initial` | §5.2；零区φ0=0，再由原演化推出保持 | 保留独立初始条件，不由p=r=0自动得出 |
| `PEC/u0_boundary` | (2.2)、§5.2；四边E=0，历史u零边界，两层乘子边界消去 | 无磁场法向/散度或内部边界条件 |
| `degenerate` | T=0时初始导数层极化/零区兼容仍有内容 | 必要端点输入；空内部方程不能证明它 |

展开 `SmoothStateRegular`：八个普通槽都要求 `UniformTimeJet`；辅助槽还要求 `WeightedJetRegular`。后者明确列出 $\sqrt{w_i}\phi_i$、$\sqrt{w_i}\phi_{i,t}$、$\sqrt{w_i}\phi_{i,tt}$ 的真实 L² 成员；前两层加权曲线连续可微。权重允许无界；普通光滑不能代替这些条件。(5.7)/(5.8) 的自动传播尚未证明。

技术延拓可在域外光滑，但 PDE 只在 $(0,T)\times\Omega$ 成立。内部有界代表取 $p\circ\operatorname{clamp}$、$r\circ\operatorname{clamp}$，在闭矩形及其限制测度下与原系数相同；该截回代表不被误称为全轴光滑函数。

## 原场到两层真实能量

真实历史及缩放磁场为

$$u(t)=u_0+\int_0^tE(s)\,ds,\qquad q(t)=q_0+\int_0^tP(s)\,ds,
\qquad\lambda=(\mu H_y,-\mu H_x),\quad\phi=\lambda-\nabla u.$$

所有积分/导数都连接实际函数与实际L²类。状态对应：

| 槽 | 原层U0 | 导数层U1 |
|---|---|---|
| v、速度V | u、E | E、E_t |
| R、z | P、q | P_t、P |
| Λ、加权ψ | λ、φ | λ_t、φ_t |
| 耗散中的R_t | P_t | P_tt |

`energy` 直接是已有 `energy7`，`dissipation` 直接是已有 `dissipation7`，`graphSquare` 直接是 `graphSquare7`。没有另一套无联系能量。`energy_eq_original_integrals` 与 `dissipation_eq_original_integrals` 将两层表示接回**原p/r**的整个矩形空间积分，各自的密度可积性单独证明。

`electricL2/polarL2/magneticXL2/magneticYL2` 从输入原函数的 `MemLp.toLp` 定义。四条 `_eq` 定理通过a.e.代表和 $\lambda=(\mu H_y,-\mu H_x)$ 识别它们与状态槽/重构槽。因此(6.10)控制输入原E/H/P，不是只给坐标换名字。

## 各结论的时间范围

对 $t\in[0,T]$，(6.7)给

$$\frac{N_0^2+KN_1^2}{4}\le\mathcal E_7(t)\le N_0^2+KN_1^2,
\qquad0\le\mathcal E_7(t)\le\mathcal E_7(0).$$

对 $t\in(0,T)$，`energy_law_and_closure` 给实际 `HasDerivAt` 及(6.8)的预算：

$$\mathcal E_7'=-\mathcal D_7,\qquad
\mathcal D_7\ge\frac12(\mathcal S_0+K\mathcal S_1)
+\frac{\mu\tau}{4\kappa}(\|P_t\|_2^2+K\|P_{tt}\|_2^2)\ge0.$$

闭区间 `energy_antitone` 来自连续性、内部真实能量律和已经证明的耗散符号。`energy_integral_balance` 另用真实 $P_{tt}$ 的 L² 连续性推出耗散时间可积，再调用FTC：

$$\mathcal E_7(t_2)+\int_{t_1}^{t_2}\mathcal D_7(s)\,ds=\mathcal E_7(t_1),
\qquad0\le t_1\le t_2\le T.$$

相同时刻与两个端点包含在结论中，不要求端点普通双侧导数。$T=0$时保持单点比较与静态能量估计；其初始导数层兼容明确输入，不能从空的内部条件推出。

原物理场控制为(6.10)：

$$\epsilon\|E(t)\|_2^2+\mu(\|H_x(t)\|_2^2+\|H_y(t)\|_2^2)
+\kappa^{-1}\|P(t)\|_2^2\le\frac4\mu\mathcal E_7(t)
\le\frac4\mu\mathcal E_7(0).$$

`auxiliary_initial_bounds` 接入(8.4)–(8.8)的兼容重构控制。图平方控制依赖极化、空间和零迹约束；它不是任意八变量裸L²范数的双向等价。

## 参数证书、数据与范围回归

本轮使用实际矩形 $(-1,1)^2$ 与全1材料参数：$C_P=4,A=3,K=384$，$c=1/16384,S=1/65536$。证书调用 v0.4 的 `unitSquare_parameter_certificate`，不重新把CP设成自由数。原§10使用精确π常数，旧c=1/128在新K下使8cAK=72>1；本轮参数/光滑替代剖面不能冒充原(10.1)/(10.2)原样验证。

v0.5.2、v0.5.3的实际声明、实例调用和成功验证证据已在下方逐项登记。数据有限初始图范数仅说明可容许性；静态与增长例的明确函数若满足八式，则属于显式解验证；这两者均不能替代一般存在唯一性证明。

## 学习顺序与InfoView

先读以下三条：

1. `SmoothCompatibleSolution`：展开每个结构字段，确认没有把输出目标作为输入。
2. `SmoothCompatibleSolution.energy_law_and_closure`：追踪原方程总装→具体Green/Poincaré→抽象两层能量律及预算。
3. `main_energy_estimate_smoothRectangle`：查看闭区间估计、单调性、真实积分平衡和输入原场控制的汇总。

在VS Code打开工程根目录，光标依次放到`by`、具名`have`、`rw`和`calc`之后，查看Lean InfoView目标。F12跳转到调用者，再沿 `problem` 查看区域入口和原系统链。构建后执行 **Lean 4: Restart File** 刷新导入。关键通用FTC是mathlib的 `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`；空间求导与迹来自本工程Rectangle模块。

## 未覆盖内容与验证状态

当前是所选光滑兼容解类的**给定解先验定理**。尚未覆盖完整H₀¹/H(div)/W¹,∞弱范围、精确π常数、加权正则性自动传播、提升规范唯一性、一般解存在唯一性。单调不增允许非零静态状态，不附带严格或指数衰减。

三个阶段分别保存 acceptance.json；最终 v0.5.3 全工程构建与审计已重新覆盖本模块及所有实例。整体验收以 [overall_acceptance.json](../logs/v0.5.3/overall_acceptance.json) 为准。

### v0.5.1 已通过的实际验证

[完整构建](../logs/v0.5.1/20261014T005346_311276_lake_build.log)、[独立审计](../logs/v0.5.1/20261014T005434_779198_axioms_audit.log)、[类型检查](../logs/v0.5.1/20261014T005434_779198_interface_types.log)均退出0；审计619个声明，仅标准基础公理，无sorryAx。来源/锁定配置未变，源码哈希和失败修复记录见[阶段验收](../logs/v0.5.1/acceptance.json)。这是本阶段当时的证据；最终当前版本覆盖与后两个阶段的证据见文末。

## v0.5.2：实际剖面与非零数据证书

[FullDomainProfile.lean](../LeanPML/Examples/FullDomainProfile.lean) 构造

$$p(x)=S\,\mathrm{smoothTransition}(4x^2-1),\qquad r(y)=S\,\mathrm{smoothTransition}(4y^2-1).$$

mathlib的平坦过渡函数在输入非正时为0，输入至少1时为1，中间严格为正且不超过1。因此物理坐标 $[-1/2,1/2]$ 上吸收为0，外侧严格正，$|x|\ge3/4$处已经达到S平台。代码证明C∞、幅度界、四个单向边层与四个双向角层非空，再组成 `RegionalAbsorption` 并调用已锁定的CP4参数证书。这是C∞替代剖面，区别于原(10.2)的有限阶分段幂函数；一般主定理仍只要求计算域内幅度界。

物理区非零初值使用

$$f(x,y)=\mathrm{expNegInvGlue}(1/16-x^2)\,
\mathrm{expNegInvGlue}(1/16-y^2),$$

其拓扑支撑包含于 $[-1/4,1/4]^2\Subset\Omega_{\rm phys}$，中心严格为正。[CompatibleData.lean](../LeanPML/Examples/CompatibleData.lean) 以

$$u_0=0,\ E_0=P_0=f,\ q_0=-f,\ H_0=Z_{1,0}=Z_{2,0}=Q_{x,0}=Q_{y,0}=0$$

核验五个初始不变量、四边PEC、u0/E0/E_t0迹和零区辅助量。真实时间延拓取 $E=P=f$、$H=(-t\partial_yf,t\partial_xf)$，历史与φ实际计算为 $u=tf,q=(t-1)f,\phi=0$。它给出与八条**初始**方程一致的实际导数：

$$E_t(0)=P_t(0)=0,\qquad H_{x,t}(0)=-\partial_yf,\quad H_{y,t}(0)=\partial_xf.$$

只核验 `OriginalAt(...,0,X)`；这个方便检查数据的延拓在一般t≠0不满足电方程。其高阶延拓不是一般解的高阶导数，也不能用于宣称全时段PDE存在。

真实普通/加权成员由 `regular` 构造。φ三层为零，所以允许无界权重；普通场和梯度仍在全矩形L²中。两层初始图平方是合法有限表达式：

$$N_0^2+KN_1^2=2\|f\|_2^2+K(\|\partial_x f\|_2^2+\|\partial_y f\|_2^2)>0.$$

`physical_data_certificate` 汇总实际数据、初始方程、兼容、PEC与正图平方；`physical_initial_traces` 另明确列出 u₀/E₀/E_t₀ 三迹。非零L²不是仅由函数名字或一个普通实数normSq推断；使用内部连续代表唯一性证明实际商类非零。

## v0.5.3：退化、静态与错误范围回归

[DegenerateBranches.lean](../LeanPML/Examples/DegenerateBranches.lean) 的 `four_branches_main` 在同一保守参数下，对全零、仅x、仅y、双向实际剖面分别构造真实零路径并调用最终定理。`asymmetric_directions` 明确核对两个不同方向；这些接口回归不替代下面的非零解。

[StaticMode.lean](../LeanPML/Examples/StaticMode.lean) 构造r=0的实际非零静态解：

$$u=E=P=q=0,\quad\lambda=\phi=(0,F(x)),\quad H_x=-F(x),\ H_y=0,\quad Q_x=pF,$$

其余原辅助量为零，材料均取1。F是中心7/8、半径1/16的C∞紧支函数，支撑 $[13/16,15/16]$ 远离p=0并位于p=S平台。故仅在实例支撑上得到正吸收下界；一般定理没有全域吸收正下界。在这个方向上 $w_y=(c-p)/p=(c-S)/S=3$，a.e.恒等式给 $\sqrt{w_y}F=\sqrt3F$ 的实际加权成员；p=0处F=0也明确处理。

代码逐条证明八方程、真实时间和空间导数、PEC、五初始兼容、零区和全部路径正则性，再构造 `concreteSolution` 实际调用本阶段定理。`nonzero_static_regression` 给

$$\mathcal E_7(t)=\mathcal E_7(0)>0,\qquad\mathcal D_7(t)=0.$$

正能量来自主定理的图下界与真正非零L²场；零耗散由实际主定理能量律和常值函数导数唯一性得到。T=0时使用同一显式路径在[0,1]内部的证明，再用状态定义识别，不从空内部假设推出。因而单调不增不能无条件加强成严格递减或指数衰减。

[UnrestrictedData.lean](../LeanPML/PML/Obstructions/UnrestrictedData.lean) 对相同双向完整剖面、物理区C∞紧支ψ构造

$$H=t\nabla\psi,\quad Q=\mu\nabla\psi,\quad E=P=Z_1=Z_2=0.$$

真正的二阶混合偏导对称性使curlH抵消；支撑内p=r=0，支撑外梯度为零，全部八式与四边PEC都通过。证明空间平方密度可积，并给实际积分

$$\int_\Omega(|H_x(t)|^2+|H_y(t)|^2)=t^2\|\nabla\psi\|_2^2,\qquad\|\nabla\psi\|_2^2>0.$$

梯度在内部点(-1/8,0)真实非零，再由连续代表唯一性获得正L²范数与正积分。物理区p=0点的 $C_x=Q_x=\mu\partial_x\psi\ne0$，任意u0/q0都不能修复这一磁辅助初始兼容，因此此族不属于最终兼容定理的输入。

同一全时间显式族在任意晚时刻超过任意磁平方界。`fullProfile_unrestricted_no_coercive_antitone_energy` 只排除在这条增长路径上同时满足固定m>0磁L²控制、有限实数初能量和[0,∞)单调不增的能量。它使用任意大时间，不用固定有限区间中的增长冒充全未来矛盾。

`singleLayer_candidate_failure_regression` 使用本轮smallC和既有§11.1负耗散结论；它只否定指定单层候选，不能改写成所有单层能量均不可能存在。

---

## 三阶段最终验证与交接

| 阶段 | 验收 | 完整构建 / 独立审计 | 含历史声明数 |
|---|---|---|---|
| v0.5.1 | 通过 | [构建](../logs/v0.5.1/20261014T005346_311276_lake_build.log) / [审计](../logs/v0.5.1/20261014T005434_779198_axioms_audit.log) | 619 |
| v0.5.2 | 通过 | [构建](../logs/v0.5.2/20261014T011030_802569_lake_build.log) / [审计](../logs/v0.5.2/20261014T011311_263210_axioms_audit.log) | 683 |
| v0.5.3 | 通过；覆盖前两阶段当前源码 | [构建](../logs/v0.5.3/20261014T011533_485975_lake_build.log) / [审计](../logs/v0.5.3/20261014T011752_801259_axioms_audit.log) | 740 |

完整类型检查与独立语义审查检查了结构字段，而非仅看 theorem 表面参数。三阶段无 sorryAx，只有标准基础公理；全部历史审计保留。模板验收中的 regularity_inputs 列表描述一般主定理范围；[范围补充](../logs/v0.5.3/scope_supplement.json) 明确区分具体实例已经证明的正则性，不误称它们仍需外传输入。

18页PDF、200旧批注保持，新增6勾和2条说明的范围见[账本](../docs/pdf_formalization_marks.md)。[结构记录](../logs/v0.5.3/pdf/annotation_result.json)和[八页视觉验收](../logs/v0.5.3/pdf/visual_review.json)均通过；定义、输入条件与未证弱范围没有被打为证明完成。

下一步是路线图 v1.0.1：核验固定 mathlib 的真实弱空间及退化权重图空间，连接目前实际 WeightedL2 和光滑矩形版本。弱 Green、一般 W¹,∞、加权传播及提升规范唯一性属于后续阶段；本轮到此交接。
