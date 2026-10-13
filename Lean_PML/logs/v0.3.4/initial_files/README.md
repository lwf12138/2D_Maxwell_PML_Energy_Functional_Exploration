# LeanPML：条件性能量恒等式、图范数与原状态控制

用途：把 V7 §7–§8 的纸面证明与实际 Lean 声明对应起来。历史 README 保存在 [v0.3.2 入场快照](logs/v0.3.2/initial_files/README.md)，历次阶段记录见 [PROGRESS](PROGRESS.md)。

**v0.3.2、v0.3.3 已分别通过验收。** 本轮止于 v0.3.3；没有实现 v0.3.4 的梯度估计、耗散闭合或最终单调性。固定 Lean v4.31.0、mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`，锁文件未改。

## 先读三条主要声明

1. [hasDerivAt_energy7_Conditional](LeanPML/PML/BalanceAbstract.lean)：从同源真实路径、原层 primitive 演化和列明的空间接口，推出 $\mathcal E_7'=-\mathcal D_7$。
2. [fieldEnergy_bounds_Conditional](LeanPML/PML/Coercivity.lean)：从参数阈值、极化与空间约束、零迹 Poincaré，得到 $N(U)^2/4\le F_c[U]\le N(U)^2$。
3. [physicalControl_Conditional](LeanPML/PML/PhysicalControl.lean)：把同一两层能量用于实际 L² 重构场，得到 (6.10)、(8.4)–(8.8)。

读主声明时先看输入与结论，再沿 F12 回看所调用的具名 `have`。推荐文件顺序为：

`BalanceInterfaces → PrimitiveEvolution → SpatialBalance / BalanceBlocks → BalanceAbstract → Coercivity → PhysicalControl`。

若尚不熟悉实际空间，先回看 [WeightedL2](LeanPML/Analysis/WeightedL2.lean)、[State](LeanPML/PML/State.lean)、[Energy](LeanPML/PML/Energy.lean) 和 [EnergyIntegrals](LeanPML/PML/EnergyIntegrals.lean)。本轮沿用这些定义，没有另设任意实数 F、D、N。

## v0.3.2：怎样从演化得到真实能量律

| 文件 | 对应论文与实际工作 |
|---|---|
| [BalanceInterfaces](LeanPML/PML/BalanceInterfaces.lean) | (7.5) 的条件性梯度域、散度域、迹与独立边界双线性配对；空间/时间交换与两层零迹 |
| [PrimitiveEvolution](LeanPML/PML/PrimitiveEvolution.lean) | (6.1)、(6.3)：对邻域内的真实 L² 方程求导，证明导数层满足同样演化 |
| [SpatialBalance](LeanPML/PML/SpatialBalance.lean) | (7.1)–(7.2)：实际加权内积转成可积乘积积分，按正/零吸收分支抵消 |
| [BalanceBlocks](LeanPML/PML/BalanceBlocks.lean) | (7.3)–(7.4)：固定实系数乘子自伴，内积展开及极化约束消元；组合三个既有块 |
| [BalanceAbstract](LeanPML/PML/BalanceAbstract.lean) | (7.6) 的真实单层含边界/零迹求导；(7.8) 的同源两层恒等式 |

单层实际输入是

$$
\mu[\epsilon(v_{tt}+a v_t+bv)+R_t+aR+bz]=\operatorname{div}\Lambda,
\quad z_t=R,\quad z+\tau R=\kappa v,
$$

以及 $\Lambda=\nabla v+\psi$、$\psi_{x,t}=r\,\partial_xv-p\Lambda_x$、$\psi_{y,t}=p\,\partial_yv-r\Lambda_y$。代码里所有槽都属于已有实际 L²/加权空间；`StateHasDerivAt` 把导数槽绑定到真实空间范数中的导数。没有加入教学子系统的 $\epsilon E'=-P'$。

`fieldEnergyRate_blocks` 保留
$\langle \mathrm{primitiveMain},V+cv\rangle+
\sum_i\langle \partial_iV+c\partial_iv,\Lambda_i\rangle$。
随后用一般 Green 关系得到

$$
\operatorname{HasDerivAt}\!\left(t\mapsto F_c[U(t)],
-D_c[U]+\langle V+cv,\Lambda\cdot n\rangle_{\partial\Omega},t\right).
$$

Green 的边界配对独立给出，未定义成能量残差。零迹通过迹与配对的线性性消去。电块已经包含 $\epsilon/2$，极化块包含 $1/(2\kappa)$；两者外乘 $\mu$，空间块不外乘 $\mu$。低层恒等式只需 $\kappa\ne0$，不需要全部小量或材料正性条件。

`primitive_first_Conditional` 从时间集合 I 内原层方程推出内部时刻的导数层方程。使用邻域等式、真实导数唯一性、固定系数乘法以及明确的梯度/散度交换，不能只对单点等式求导。第二层极化与空间约束在开集 `interior I` 上再次求导，因而所需高阶条件没有省略。原层的 $u,E$ 和导数层的 $E,E_t$ 零迹各自使用。

最终 `hasDerivAt_energy7_Conditional` 复用 `hasDerivAt_energy7`，由两层真实单层结论识别其导数值，固定同一个 $K=8\mu(\epsilon+2\kappa)C_P^2$，得到

$$
\operatorname{HasDerivAt}(\mathcal E_7,-\mathcal D_7(t),t).
$$

这个定理没有假设或证明 $\mathcal D_7\ge0$。因此现在仍不能宣布 $\mathcal E_7$ 单调不增。

## 哪些空间内容仍是条件接口

| 接口 | 数学内容与使用处 | 当前状态／后续 |
|---|---|---|
| `ConditionalSpatialDomain.domain`、`componentX/Y` | 受限梯度定义域和线性分量，连接 $\Lambda=\nabla v+\psi$ | 具体矩形弱/光滑梯度待 v0.4.1 |
| `ConditionalGreenDomain.fluxDomain/divergence` | 受限散度定义域及线性散度，主方程右侧 | 具体 H(div) 或光滑通量待 v0.4.1 |
| `trace/boundary/green` | 一般测试函数与通量的 Green 公式，边界空间及独立双线性配对 | 当前输入；具体矩形迹与 Green 待 v0.4.1–2 |
| `ConditionalSpatialPath` 的域成员及匹配等式 | 域内路径在 I 内对应实际 $u,E,E_t,\lambda,\lambda_t$ | 当前正则性输入，不能从路径名称推断 |
| `grad_baseX/Y, grad_firstX/Y, div_base` | 实际 L² 的梯度/散度与时间求导交换 | 当前输入；v0.4.3 从具体正则性证明 |
| `trace_base_v/V, trace_first_v/V` | 原层 $u,E$、导数层 $E,E_t$ 各自零迹 | 当前输入；v0.4.3 从提升、PEC 及时间正则性证明 |
| `ConditionalPoincare.estimate` | 零迹梯度定义域上的 $\|v\|^2\le C_P^2\|\nabla v\|^2$ | 当前输入；精确矩形常数待 v0.4.2 |

已证明的是这些接口**成立时的结论**，不是接口字段本身。梯度和散度没有被当作整个 L² 上的有界算子。`ConditionalPoincare.ofGreenTrace` 明确取 `ker G.trace` 为零迹子域，桥接两阶段同一套边界含义；它不从 Green 推出 Poincaré。

## v0.3.3：空间约束为什么不可省

令 $B_{\rm sp}=\|\Lambda\|^2+\|\psi\|_w^2$。已有加权恢复映射给出 $\|\psi\|_2^2\le\|\psi\|_w^2$，再用 $\nabla v=\Lambda-\psi$ 得到 (8.3)：

$$
\|\nabla v\|^2\le 2B_{\rm sp},\qquad
\|v\|^2\le2C_P^2B_{\rm sp}.
$$

第二条还需要上述零迹 Poincaré 接口。正吸收处的 $w_i\ge1$ 不被错误地搬到零区；零区由加权恢复的 a.e. 零延拓处理。无界 w 只由加权空间承载，所有普通 L² 系数乘子都是已证有界的 a、b 等。

`CoercivityParameters` 只记录材料正性、$C_P>0$ 和原阈值 $c\le c_*$；吸收非负及幅度条件来自 `SpatialAbsorption`。主定理依次调用 (8.1) 极化消元、(8.2) 系数界、Young 估计、实际可积密度的积分序关系，以及 $c^2K\le1$。不利项
$2\mu(\epsilon+2\kappa)c^2\|v\|^2$ 被吸收到 $B_{\rm sp}/2$，得到精确的

$$
\frac14N(U)^2\le F_c[U]\le N(U)^2,\qquad
\frac14(N_0^2+KN_1^2)\le\mathcal E_7\le N_0^2+KN_1^2.
$$

**原文细节：** §8.2 最后写的严格 $3(\epsilon+\kappa)B_{\rm sp}/(4A)<B_{\rm sp}$ 在 $B_{\rm sp}=0$ 时不成立。代码使用目标所需的非严格估计，保留零状态和原常数；源文未改。

`graphSquare_zero_Conditional`、`fieldEnergy_zero_Conditional`、`energy7_zero_Conditional` 分别说明图平方、单层能量、两层能量为零时，受约束状态的八个实际坐标为零。其中 v 的零性要用 Poincaré，z 的零性要用极化约束。这不是任意独立点态分量的矩阵正定，也没有为候选平方表达式安装未经证明的 Norm 实例。

## 原八变量及辅助变量受到什么控制

`PhysicalControl.lean` 的重构使用真实 L² 标量乘法与有界空间系数乘子：

$$
E=U_0.V,\quad P=U_0.R,\quad
H_x=-\Lambda_y/\mu,\quad H_y=\Lambda_x/\mu,\quad
q=\kappa u-\tau P,
$$
$$
Z_1=-\epsilon bu,\quad Z_2=-bq,\quad
Q_x=p\phi_y,\quad Q_y=-r\phi_x.
$$

在极化兼容下另证重构 q 等于状态坐标 z；磁场缩放关系也实际核验。`physicalControl_Conditional` 的输出 `PhysicalControlBounds` 逐项为：

| 论文 | 输出字段与精确结论 |
|---|---|
| (6.10) | `physical`：$\epsilon\|E\|^2+\mu(\|H_x\|^2+\|H_y\|^2)+\kappa^{-1}\|P\|^2\le(4/\mu)\mathcal E_7$ |
| (8.4) | `displacement/auxiliary`：$\|u\|^2\le8C_P^2\mathcal E_7$，$\|\phi\|^2\le4\mathcal E_7$ |
| (8.5) | `primitivePolar`：$\|q\|^2\le(16\kappa^2C_P^2+8\kappa\tau^2/\mu)\mathcal E_7$ |
| (8.6) | `electricMemory`：$\|Z_1\|^2\le8\epsilon^2S^4C_P^2\mathcal E_7$ |
| (8.7) | `polarMemory`：$\|Z_2\|^2\le S^4(16\kappa^2C_P^2+8\kappa\tau^2/\mu)\mathcal E_7$ |
| (8.8) | `magneticAuxiliary`：$\|Q_x\|^2+\|Q_y\|^2\le4S^2\mathcal E_7$ |

这是给定兼容提升的单向 L² 控制。原八变量 PDE 与 primitive 的完整双向等价、全部五不变量的场层证明、提升规范唯一性、解存在唯一性仍未完成。也没有反向的任意裸八变量 L² 上界。

## 学习操作与复现

在 VS Code 中打开整个工程。保存 Lean 文件，把光标依次放在 `have`、`rw`、`filter_upwards`、`calc` 前后，在 InfoView 看上下文和 `⊢`；如果未显示，执行 `Lean 4: InfoView: Display Goal`。F12 跳转到声明，悬停核对隐式参数。构建后导入未刷新时执行 `Lean 4: Server: Restart File`，必要时重新打开文件；不要更新依赖来处理缓存。

关键固定版 mathlib 位置：

- `HasDerivAt.unique`、`HasDerivAt.congr_of_eventuallyEq`：`.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`。
- `HasFDerivAt.comp_hasDerivAt`：`.../Analysis/Calculus/Deriv/Comp.lean`。
- `HasDerivAt.inner / norm_sq`：`.../Analysis/InnerProductSpace/Calculus.lean`。
- `integral_mono_ae`（当前第 617 行）、`integral_add`、`integral_congr_ae`：`.../MeasureTheory/Integral/Bochner/Basic.lean`。
- `Lp.coeFn_add / coeFn_smul / ext`：`.../MeasureTheory/Function/LpSpace/Basic.lean`。

mathlib 提供微积分与测度基础；本项目 v0.3.1 提供具体加权空间、合法积分和能量求导；本轮新增的是 primitive/Green 抵消、约束下能量上下界与重构控制。`ring` 整理代数，`linarith/nlinarith` 合并已建立的等式或不等式，不能替代空间分析接口。

~~~sh
cd '/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML'
python3 scripts/run_logged.py --stage v0.3.2 lake_build lake build
python3 scripts/run_logged.py --stage v0.3.2 axioms_audit lake env lean Audit.lean
python3 scripts/run_logged.py --stage v0.3.3 lake_build lake build
python3 scripts/run_logged.py --stage v0.3.3 axioms_audit lake env lean Audit.lean
~~~

当前树包含两个阶段；重新运行会检查完整当前工程。每次生成独立日志和 JSON，不覆盖历史。主要定理均由 `LeanPML.lean` 的正式导入链进入默认构建，`Audit.lean` 保留旧审计并增加本轮声明。标准 `propext`、`Classical.choice`、`Quot.sound` 允许，检查没有 `sorryAx` 或自定义占位公理。

[v0.3.2 构建](logs/v0.3.2/20261013T095839_225389_lake_build.log)／[独立审计](logs/v0.3.2/20261013T100104_046897_axioms_audit.log)；[v0.3.3 构建](logs/v0.3.3/20261013T100156_159842_lake_build.log)／[独立审计](logs/v0.3.3/20261013T100321_602582_axioms_audit.log)。四条命令均退出 0。v0.3.2 审计 288 条，v0.3.3 审计 316 条（保留旧 263 条，分别增加 25、28 条）；仅标准基础公理。失败及修复过程保存在对应 logs 目录。

## PDF 与下一阶段

[指定 PDF 副本](../results/V7_Maxwell_Debye_PML/V7_global_energy_副本.pdf)已更新：第 10–13 页新增 12 个带范围红勾、6 条说明。18 页、150 项既有批注与正文保留，共 168 项批注；四页渲染检查通过，见 [PDF 验收](logs/v0.3.3/pdf/verification.json)。标记分别覆盖 (6.7)、(6.10)、(7.6)、(7.8)、(8.3)、§8.1–§8.2 与 (8.4)–(8.8) 的条件性结论。Green 本身只作接口说明，旧“待完成”文字保留并说明历史属性。

[定理与接口清单](docs/theorem_inventory.md)、[结论账本](docs/claim_ledger.md)、[PDF 标注账本](docs/pdf_formalization_marks.md)逐项登记当前条件性范围，不覆盖旧历史。具体矩形空间分析尚待 v0.4，原模型完整对应亦未完成。

下一阶段 **v0.3.4** 入口是现有 primitive 辅助演化、同源导数层、实际空间耗散以及 `θ_x,θ_y` 分配权重。目标为 (9.5) 的
$\|\nabla E\|^2\le3J(U_1)+3S^2J(U_0)$，
并证明 $\mathscr S[U]\ge(c-S)J(U)\ge3cJ(U)/4$；本轮没有实现这些结果。之后 v0.3.5 才闭合耗散预算并证明单调性和积分平衡。
