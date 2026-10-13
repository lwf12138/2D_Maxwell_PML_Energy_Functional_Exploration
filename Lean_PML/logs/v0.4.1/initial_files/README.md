# LeanPML：V7 两层能量的条件性分析核心

用途：把论文第 9 节的梯度估计、耗散预算与有限区间结论逐步对应到 Lean。旧学习说明保存在 [v0.3.4 入场 README](logs/v0.3.4/initial_files/README.md)，阶段历史保留在 [PROGRESS](PROGRESS.md)。

**v0.3.4、v0.3.5 已分别通过验收。** 本轮新增 53 条正式定理，最终审计共 369 条；以下结论均有列明的分析接口范围。固定 Lean v4.31.0、mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`；不更新依赖，也不实施 v0.4。

## 先读这三条声明

1. [GradientControl.lean](LeanPML/PML/GradientControl.lean) 的 `gradient_control_Conditional`：原辅助演化和真实同源导数怎样提供 (9.4)，再变成 (9.5) 的实际空间积分估计。
2. [DissipationClosure.lean](LeanPML/PML/DissipationClosure.lean) 的 `dissipation7_lower_Conditional`：两类耗散分别吸收哪个负项，以及如何保留准确的剩余量。
3. [MainAbstract.lean](LeanPML/PML/MainAbstract.lean) 的 `main_energy_estimate_Conditional`：查看有限闭区间主结论及所有输入。先展开 `FiniteIntervalProblemConditional`，不要仅凭定理名称判断范围。

阅读时建议先看命题的 `:` 后面，再看输入，最后跟随证明中的具名 `have`。

旧结果仍由正式导入链复用：[WeightedL2](LeanPML/Analysis/WeightedL2.lean)、[State](LeanPML/PML/State.lean)、[Energy](LeanPML/PML/Energy.lean)、[EnergyIntegrals](LeanPML/PML/EnergyIntegrals.lean)、[BalanceAbstract](LeanPML/PML/BalanceAbstract.lean)、[Coercivity](LeanPML/PML/Coercivity.lean)、[PhysicalControl](LeanPML/PML/PhysicalControl.lean)。没有换一套任意实数能量或耗散来证明较弱命题。

## 从原演化到 (9.5)

分配权重 $\theta$ 与能量权重 $w$ 不同：正区 $\theta_x=p/(p+r)$、$\theta_y=r/(p+r)$，零区各为 $1/2$；它们有界于 $[0,1]$。能量权重 $w$ 可以无界，只在已有加权空间中使用。

`fieldJ` 定义在实际 L² 等价类上，四个有界系数内积等于

$$
J(U)=\int_\Omega\bigl[\theta_x\Lambda_x^2+\theta_yh_x^2
+\theta_y\Lambda_y^2+\theta_xh_y^2\bigr],\qquad h=\Lambda-\psi.
$$

`fieldJ_integrable` 先证明密度可积，`fieldJ_eq_integral` 再证明积分/内积对应，`fieldJ_nonneg` 从密度得到非负性。`spatialComponents_eq_gradient_Conditional` 在空间约束下把 $h$ 与梯度接口连接。这里的积分覆盖整个测度空间；二维入口可取整个矩形限制测度。

零区的 $\psi=0$ 来自 WeightedL2 的已证恢复映射，不是因为吸收为零就任意删除场。在这个区域，$\Lambda=h$，所以 $J$ 的密度为 $h_x^2+h_y^2$，空间耗散为 $c(h_x^2+h_y^2)$。

从实际辅助演化与对邻域空间约束的真实求导得到 (9.4)：

$$
\partial_iE=\lambda_{i,t}-\sigma_j\partial_i u+\sigma_i\lambda_i.
$$

x 方向使用 $(\sigma_i,\sigma_j)=(p,r)$，y 方向反过来。$E$ 和 $\lambda_t$ 由 `SameSourcePath` 的 `HasDerivAt` 绑定，梯度与时间微分交换仍是明确接口。

将 $h_1^2=(\theta_i+\theta_j)h_1^2$ 分开：只对 $\theta_i$ 部分使用三项平方和估计，$\theta_j$ 部分留在 $J(U_1)$。系数比较

$$
\theta_i\sigma_j^2\le S^2\theta_j,\qquad
\theta_i\sigma_i^2\le S^2\theta_i
$$

在正区和零区分别证明。然后将实际场的 a.e. 等式、密度可积性和积分序关系连接起来，得到

$$
\|\nabla E\|^2\le3J(U_1)+3S^2J(U_0). \tag{9.5}
$$

同一分支定义还给出 (9.3)：

$$
\mathscr S[U]\ge(c-S)J(U)\ge\frac{3c}{4}J(U).
$$

因此零吸收、单向边层和角层都在一般证明中，没有吸收正下界。

## 两类耗散怎样闭合

使用邻域内的真实极化兼容关系及同源导数，先得到
$R+\tau R_t=\kappa v_t$。电、极化余项中的有利系数非负，再用 $c\tau\le1/4$，推出

$$
D_c[U]\ge\mathscr S[U]+\frac{\mu\tau}{2\kappa}\|R_t\|^2
-\mu cA\|v_t\|^2,\qquad A=\epsilon+2\kappa.
$$

这条单层结论允许负项，没有宣称单层耗散非负。用于同源两层后，得到 (9.1) 中的两个负项：$\mu cA\|E\|^2$ 与 $\mu cAK\|E_t\|^2$。

| 负项 | 使用的证据 | 支付的耗散 |
|---|---|---|
| $\mu cA\|E\|^2$ | E 零迹的 Poincaré、(9.3)、(9.5)、$K=8\mu AC_P^2$、$KS^2\le1/16\le1$ | 至多 $(\mathscr S_0+K\mathscr S_1)/2$ |
| $\mu cAK\|E_t\|^2$ | 真实 Debye 导数 $\kappa E_t=P_t+\tau P_{tt}$，$8cAK\le\kappa\tau$、$8cA\tau\le\kappa$ | 至多 $\mu\tau(\|P_t\|^2+K\|P_{tt}\|^2)/(4\kappa)$ |

所有小量界都由原阈值 $c\le c_*$ 推出。为取得 $S\ge0$，最终空间吸收入口使用非空空间载体：任选一点，由 $0\le p\le S$ 得到；二维载体 $\mathbb R^2$ 天然满足。这不要求测度非零，也不要求任一吸收系数为正。

两次吸收使用不同预算，同时扣除后保留

$$
D_7\ge\frac12(\mathscr S_0+K\mathscr S_1)
+\frac{\mu\tau}{4\kappa}(\|P_t\|^2+K\|P_{tt}\|^2)\ge0. \tag{6.8}
$$

`first.R` 是 $P_t$，`second.R` 是 $P_{tt}$；并非仅凭坐标名字认定它们是导数。原层兼容在邻域成立，经两次真实求导获得所需的 Debye 关系。随后调用已有能量恒等式，才得到能量导数非正；这三步是三个不同结论。

## 有限区间主定理究竟假设什么

`FiniteIntervalProblemConditional` 把原始路径条件列明：

- `SameSourcePath` 的时间集合是 $(0,T)$；真实导数、primitive 原层演化只在内部要求。
- 原层与导数层的普通 L²、加权 L² 坐标在 $[0,T]$ 上连续。能量连续性由实际内积/范数二次型推出，不是输入字段。
- 两层在闭区间上满足极化、空间、同一迹下的静态约束。这些条件在 $T=0$ 时仍需给出，不能由空的内部方程推出。
- 一般 Green、受限梯度/散度域、时间交换、两层零迹是沿用的空间分析接口。Poincaré 始终使用同一个 `G.trace` 的核。
- 积分平衡额外要求 `second.R` 的 L² 路径在闭区间连续，从而推出实际耗散连续及 `IntervalIntegrable`；单调性不需要这项额外连续性。

没有输入 (9.5)、吸收估计、耗散符号、能量单调性或平衡。`#print axioms` 不会检查普通结构字段是否藏入目标，因此本轮还单独审查并登记了上述字段。

既有 `LeanPML.Time.antitoneOn_Icc_of_hasDerivAt_nonpos` 将闭区间连续和内部真实导数非正连接为 `AntitoneOn`。静态图范数下界另外给能量非负：

$$
0\le\mathcal E_7(t)\le\mathcal E_7(0),\qquad 0\le t\le T.
$$

积分平衡单独调用 mathlib 的微积分基本定理，得到

$$
\mathcal E_7(t_2)+\int_{t_1}^{t_2}D_7(t)\,dt=\mathcal E_7(t_1),
\qquad 0\le t_1\le t_2\le T. \tag{6.9}
$$

代码把能量导数和定量耗散下界声明在 $(0,T)$，把静态界、单调性和积分平衡声明在 $[0,T]$。$T=0$ 时内部条件为空，不能因此推导任意导数坐标在端点的耗散非负。

这里没有端点普通双侧导数要求，允许 $t_1=0$、$t_2=T$、$t_1=t_2$ 和 $T=0$。不乘 $e^{-Ct}$，也不要求未来积分收敛。

原有 (6.7)、(6.10)、(8.4)–(8.8) 继续作用于同一能量；各时刻的兼容重构场控制进一步接到 $\mathcal E_7(0)$，原常数保持。

## VS Code 与依赖来源

打开整个工程目录，保存文件，将光标放在具名 `have`、`calc`、`rw` 或 tactic 前后，观察 InfoView 的上下文和 `⊢` 目标。若面板未显示，执行 `Lean 4: InfoView: Display Goal`；F12 跳转声明，悬停查看隐式参数。构建后若导入未刷新，执行 `Lean 4: Server: Restart File`，必要时重新打开文件。

| 来源 | 本轮使用的内容 |
|---|---|
| mathlib | `ContinuousOn.inner`、`ContinuousLinearMap.continuous`、`Lp.coeFn_*`、`integral_mono_ae`、区间 FTC |
| 旧工程 | 实际 WeightedL2/恢复映射、参数阈值、能量积分、同源导数、条件性能量律、图范数界与重构控制、区间单调接口 |
| 本轮新证明 | J 的实际积分与分支、(9.3)–(9.7)、定量耗散剩余量、场路径连续性到有限区间单调和平衡 |

固定版本中可用 F12 核查：

- `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`：`.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:1142`。
- `ContinuousOn.intervalIntegrable_of_Icc`：`.../MeasureTheory/Integral/IntervalIntegral/Basic.lean:507`。
- `integral_mono_ae`：`.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:617`。
- `HasDerivAt.unique`、`HasDerivAt.congr_of_eventuallyEq`：`.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:399,615`。
- 项目的 `norm_sub_sq_le_twice` 在 [Coercivity.lean](LeanPML/PML/Coercivity.lean)；它不是 mathlib 同名结果。

## 实际验证与复现

| 阶段 | 实际默认构建 | 独立公理审计 | 新定理／审计总数 |
|---|---|---|---|
| v0.3.4 | [lake build](logs/v0.3.4/20261013T214336_169080_lake_build.log) | [lake env lean Audit.lean](logs/v0.3.4/20261013T214424_960799_axioms_audit.log) | 18／334 |
| v0.3.5 | [lake build](logs/v0.3.5/20261013T214810_766115_lake_build.log) | [lake env lean Audit.lean](logs/v0.3.5/20261013T214845_382134_axioms_audit.log) | 35／369 |

四条命令退出码均为 0。每个同名 `.json` 保存命令、工作目录、完整输出文件名和退出码；[v0.3.4 验收](logs/v0.3.4/acceptance.json)与[v0.3.5 验收](logs/v0.3.5/acceptance.json)登记源码哈希。审计只出现 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx` 或自定义占位公理。最终阶段重新检查整个工程和全部旧审计。

编译失败、修复及检查失败均保留：包括固定版本 FTC 编译产物缺失、一次并行开发导致暂时缺失 `.olean`，以及审计注册脚本因前缀重名漏列 `debye_absorption`。覆盖检查拦下漏项后，改为逐行精确匹配、补审并重跑构建审计；数学结论未放宽。

新增正式模块须加入 [LeanPML.lean](LeanPML.lean) 的导入链，并在 [Audit.lean](Audit.lean) 加入完整定理名的 `#print axioms`，两者都在默认 Lake target 中；不要仅创建一个未导入的文件。

~~~sh
cd '/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML'
python3 scripts/run_logged.py --stage v0.3.4 lake_build lake build
python3 scripts/run_logged.py --stage v0.3.4 axioms_audit lake env lean Audit.lean
python3 scripts/run_logged.py --stage v0.3.5 lake_build lake build
python3 scripts/run_logged.py --stage v0.3.5 axioms_audit lake env lean Audit.lean
~~~

本树包含两阶段，重跑时检查整个当前工程。日志脚本记录真实命令、目录、退出码及完整输出，每次生成独立文件，保留失败和修复记录。固定依赖中缺失的 FTC 编译产物已通过 `lake build Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus` 构建，没有更新版本。

## PDF、范围与下一阶段

[指定 PDF 副本](../results/V7_Maxwell_Debye_PML/V7_global_energy_副本.pdf) 保持 18 页和原 168 项批注，新增 10 个带范围红勾及 5 条说明。第 10 页对应 (6.8)、(6.9)，第 13 页对应 (9.1)，第 14 页对应 J 的可积/非负子结论、(9.3)–(9.7) 及剩余耗散；第 12 页只追加旧状态说明。四个修改页已逐页渲染检查，无正文遮挡、裁切或缺字；既有待完成文字保留，并说明历史属性。

[PDF 备份与哈希](logs/v0.3.5/pdf/backup.json)、[标注定位及证明证据](logs/v0.3.5/pdf/annotation_plan.json)、[结构验证](logs/v0.3.5/pdf/verification.json)、[逐页视觉检查](logs/v0.3.5/pdf/visual_review.json)均已记录。

[定理清单](docs/theorem_inventory.md)、[结论账本](docs/claim_ledger.md)、[PDF 标注账本](docs/pdf_formalization_marks.md)追加当前范围，保留全部历史。路线图 v0.3.2–3 复选框与“待实现”文字不一致，已在 [来源复核](logs/v0.3.4/source_review.md)记录，路线图原样保留。

本成果可称“V7 两层能量的条件性分析核心”。它是给定足够正则、兼容路径的先验估计，单调不增允许等号；没有证明严格衰减、全局解存在、唯一性或完整原八变量 PDE 等价。

下一步 **v0.4.1** 是具体矩形的 `Rectangle/Domain.lean`、`Fields.lean`、`Boundary.lean`：明确光滑场类、坐标导数、全矩形体积分及四边迹/PEC，并区分 $u_0$ 与 E 的零迹。之后才在 v0.4.2–4 兑现 Green/Poincaré、时间交换和完整模型对应。本轮不实现这些模块。
