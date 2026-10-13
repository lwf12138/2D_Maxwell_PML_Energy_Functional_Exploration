# 单层能量不是终点：v0.2.4

用途：沿 V7 §11.1 的计算理解单层候选的限制，以及第二层为何需要出现。本阶段处理初始兼容、单层负耗散、真实局部时间求导和特殊初值的实际积分，没有构造完整二维 PDE 解。

代码见 [SingleLayer.lean](../LeanPML/PML/Obstructions/SingleLayer.lean)。来源是 [V7 正文](../../results/V7_Maxwell_Debye_PML/V7_global_energy.md) 的 (2.1)、(2.4)、(6.1)–(6.2)、(7.2)–(7.7) 和 **§11.1 未编号公式**。本文件兼作学习说明与范围记录。

## 1. 公式号和证据范围

§11.1 位于 PDF 实际第 15 页，印刷页码也是 15。原段落“单层精确导数已在式 (7.7) 给出”存在交叉引用笔误：**(7.6) 是能量导数关系，(7.7) 是耗散定义**。本阶段按实际公式用途引用，原文保持不变。§11.2 的 (11.1) 是另一项椭圆修正公式，不能用来指称本阶段的负耗散式。

本轮 V7 的 MD、TEX、原 PDF 均与已登记版本一致。路线图相比旧阶段快照仅有 v0.2.3 四个复选项已勾选，数学要求未改；其中旧“待实现”文字仍存在，不以该文字代替真实构建证据。详见 [来源核对记录](../logs/v0.2.4/pdf/source_review.md)。

| 证据层次 | 本阶段对象 | 不随之得到的结论 |
|---|---|---|
| 点态代数 | 一个空间点的取值 $\xi$、系数和导数数值槽 | 函数实际可导、空间可积或解存在 |
| 真实局部时间 | 实函数与 `HasDerivAt` 证据 | 路径已经来自同一组二维空间场 |
| 特殊初值积分 | 实际函数、测度、平方可积和支撑 | 一般积分求导、Green/PEC |
| 完整 PDE | 留作后续接口 | 本轮未证明存在性、两层闭合或最终单调性 |

## 2. 复用三块组合单层密度

沿用 $a=p+r,\ b=pr$。固定空间点后，它们是时间常数，不要求整个空间吸收为常数。新定义 `singleLayerEnergy`、`singleLayerDissipation` 直接组合已有块：

$$
F_{\mathrm{loc}}=\mu F_e+\mu F_D+F_{\mathrm{sp}},\qquad
D_{\mathrm{loc}}=\mu D_e+\mu D_D+D_{\mathrm{sp}}.
$$

它们整理 (6.2)、(7.7) 的**密度**，尚不是空间能量律。

| 块 | 复用定义 | 已含因子 | 组合时再乘 |
|---|---|---|---|
| 电块 | `electricEnergy`、`electricRemainder` | 能量含 $\epsilon/2$，余项含 $\epsilon$ | $\mu$ |
| 极化块 | `polarEnergy`、`polarRemainder` | 能量除以 $2\kappa$，余项除以 $\kappa$ | $\mu$ |
| 空间块 | `spatialEnergy2D`、`spatialDissipation2D` | 能量含 $1/2$；耗散保留独立零区分支 | 不额外乘 $\mu$ 或 $1/2$ |

其中

$$
D_e=\epsilon\bigl[(a-c)v_t^2+bcv^2\bigr],
$$

$$
D_D=\frac{\tau R_t^2+\bigl(a-c+\tau(ac-b)\bigr)R^2+bcz^2}{\kappa}.
$$

$a=0,c>0$ 时 $a-c=-c<0$，所以 $D_{\mathrm{sp}}\ge0$ 不保证总耗散非负。能量正定也不自动推出沿时间单调；还须另外控制导数。

## 3. 初值与五项兼容代数

§11.1 选取非零 $f\in C_c^\infty(\Omega_{\mathrm{phys}})$，令

$$
u_0=0,\quad H_0=0,\quad\phi_0=0,\quad
E_0=f,\quad P_0=\kappa f,\quad q_0=-\tau\kappa f,
$$

原 PML 辅助变量 $Z_{1,0},Z_{2,0},Q_{x,0},Q_{y,0}$ 全为零。

点态证明用实数 $\xi=f(x)$，支撑输入写成

$$
\xi\ne0\Longrightarrow p=r=0.
$$

于是 $a\xi=b\xi=0$：$\xi=0$ 时乘积直接为零，$\xi\ne0$ 时由支撑消去吸收。`absorption_mul_initial_zero` 证明这个分支结论，供兼容与原方程化简调用。

`initial_compatibility` 核验 (2.4) 的五项**初始数值**：

$$
\begin{aligned}
q_0+\tau P_0-\kappa u_0&=-\tau\kappa\xi+\tau\kappa\xi=0,\\
Z_{1,0}+\epsilon bu_0&=0,\\
Z_{2,0}+bq_0&=-\tau\kappa(b\xi)=0,\\
Q_{x,0}-p\phi_{y,0}&=0,\\
Q_{y,0}+r\phi_{x,0}&=0.
\end{aligned}
$$

第三项需要支撑关系；不能只看到 $Z_{2,0}=0$ 就省略 $bq_0$。最后两项只是初始零数值代入，不表示两个磁不变量的时间保持已证明。实际 $\lambda_0=(\mu H_{y,0},-\mu H_{x,0})$、$\phi_0=\lambda_0-\nabla u_0$、提升构造、迹及加权成员资格仍需空间接口。

v0.1.3 已有三个标量不变量的真实时间保持，本阶段补充特殊初值检查，不把完整五不变量条目整体标为完成。

## 4. 初始导数为什么为零

Debye 方程在初值处给出

$$
\tau P_t(0)+\kappa\xi=\kappa\xi.
$$

由 $\tau\ne0$ 得 $P_t(0)=0$。原电方程在零磁初值、零辅助初值下为

$$
\epsilon E_t(0)=-\epsilon a\xi-P_t(0)-a\kappa\xi.
$$

再用 $a\xi=0$、$\epsilon\ne0$，得到 $E_t(0)=0$。因此 $\epsilon E_t(0)=-P_t(0)$ 是原方程**在这组数据处的化简**，不是给一般 PML 添加 v0.1.2 的教学方程。代码输入已把零磁初值的旋度值填零；从真实空间磁场推出该输入仍需空间对应。

两条定理刻意分开：

- `initial_derivative_values`：`dE`、`dP` 只是实数，从初始代数方程推出它们为零。
- `hasDerivAt_initial_fields_zero`：再输入 `HasDerivAt E dE 0`、`HasDerivAt P dP 0`、函数初值及初始方程，才输出两份真实零导数证据。

`HasDerivAt E dE 0` 的三个位置依次是函数、导数值、求导点。`congr_deriv` 用已证 `dE = 0` 改写导数值，不会凭空产生可导性。本局部版本使用普通双侧导数；PDE 初始端点的单侧导数或延拓接口尚未处理。

## 5. 负耗散怎样由三块得到

$\xi\ne0$ 的点由支撑得到 $a=b=0$。第一层 $U_0$ 的初始槽为

$$
v=0,\quad v_t=\xi,\quad R=\kappa\xi,\quad
z=-\tau\kappa\xi,\quad R_t=0,\quad
(h_x,h_y)=(l_x,l_y)=(0,0).
$$

代入已有定义：

$$
D_e=\epsilon(0-c)\xi^2=-\epsilon c\xi^2,
$$

$$
D_D=\frac{(0-c)(\kappa\xi)^2}{\kappa}=-\kappa c\xi^2,
\qquad D_{\mathrm{sp}}=0.
$$

极化约分需要 $\kappa\ne0$：先给 `hκ_ne`，再以 `field_simp [hκ_ne]` 消分母，最后用 `ring` 整理多项式。因此

$$
D_{\mathrm{initial}}(\xi)
=\mu(-\epsilon c\xi^2)+\mu(-\kappa c\xi^2)+0
=-\mu c(\epsilon+\kappa)\xi^2.
$$

`initialDissipation_eq` 也处理 $\xi=0$：所有初值槽为零，密度为零，但该点的 $p,r$ 仍允许非零。等式因而覆盖全域，没有把积分域缩成物理区。

恒等式仅需支撑与 $\kappa\ne0$。符号另证：`initialDissipation_nonpos` 在 $\epsilon,\kappa,\mu,c>0$ 下给非正性；`initialDissipation_neg` 再用 $\xi\ne0$ 得 $\xi^2>0$，给严格负性。$\tau>0$ 属于物理范围，但不参与这个初始耗散的最终符号，故符号定理没有多余地要求它。

`singleLayerEnergy_initial` 另核验物理区的初始能量数值

$$
F_{\mathrm{initial}}(\xi)=
\frac{\mu}{2}\bigl[\epsilon+\kappa(1-c\tau)\bigr]\xi^2.
$$

该式包括 $\kappa=0$ 的 Lean 总函数分支，不需非零假设；物理合同仍保持 $\kappa>0$。这只是数值核对，不是一般正定性或时间单调性定理。

## 6. 从点态等式到实际积分

`initialDissipation_integral` 中 $f,p,r:X\to\mathbb R$ 是实际函数，$m$ 是实际测度。输入为几乎处处支撑条件与平方可积：

$$
f(x)\ne0\Longrightarrow p(x)=r(x)=0
\quad\text{对 }m\text{ 几乎处处的 }x,\qquad f^2\in L^1(m).
$$

Lean 使用 `Integrable (fun x => (f x)^2) m`。定理同时证明密度可积与

$$
\int_X D_{\mathrm{initial}}(f(x))\,dm
=-\mu c(\epsilon+\kappa)\int_X f(x)^2\,dm.
$$

证明依次完成：`filter_upwards` 在几乎处处支撑成立的点调用点态定理；证明密度几乎处处等于常数乘 $f^2$；推出密度可积；用 `integral_congr_ae`、`integral_const_mul` 计算积分。没有用普通实数冒充范数平方。

`initialDissipation_rectangle_integral` 将它实例化到

$$
X=\mathbb R\times\mathbb R,\quad
\Omega=(x_0,x_1)\times(y_0,y_1),\quad
m=\mathrm{volume}\!\restriction_\Omega.
$$

代码用 `Set.Ioo x₀ x₁ ×ˢ Set.Ioo y₀ y₁` 表示全开矩形，`volume` 是二维 Lebesgue 测度。积分始终覆盖整个计算域；仅在 $f\ne0$ 处要求零吸收。$\int_\Omega f^2$ 对应论文 $\|f\|^2$ 的平方积分表达，本轮尚未构造 `Lp` 等价类及其范数识别接口。

严格积分负性 `initialDissipation_integral_neg` 另外要求

$$
0<\int_X f^2\,dm.
$$

一般测度空间中，“$f$ 不是处处零函数”不足以保证这一点，它可能只在零测集上非零。本阶段没有构造原文的光滑紧支撑 $f$ 并证明其正平方积分；光滑性、非平凡性、支撑及正积分证据是待兑现的具体空间接口。

## 7. 真实局部能量率与 PDE 初始增长

`singleLayerEnergyAlong` 让三块沿真实时间路径取值，速度位置使用 `deriv v`。`hasDerivAt_initial_localEnergy` 输入以下实际导数的 `HasDerivAt` 证据：

$$
v'(0)=\xi,\quad v''(0)=0,\quad
R'(0)=0,\quad z'(0)=\kappa\xi,
$$

以及初值；空间分量还输入

$$
h_x'(0)=l_x'(0)=g_x,\qquad
h_y'(0)=l_y'(0)=g_y,\qquad h_x(0)=h_y(0)=l_x(0)=l_y(0)=0.
$$

$g_x,g_y$ 仍是导数值参数，不是已经构造的 $\partial_x f,\partial_y f$。证明调用已有真实求导结果：

1. `hasDerivAt_electricEnergyAlong` 接收 $v$ 的一、二阶导数证据。
2. `hasDerivAt_polarQuadratic` 逐项求导，再除以 $2\kappa$。这是直接计算二次型，未对单点兼容关系求导，也未假设它在邻域成立。
3. `hasDerivAt_spatialEnergy2D` 使用零吸收分支。由于 $l_x(0)=l_y(0)=0$，初始空间能量导数为零。
4. 电块、极化块乘 $\mu$ 后相加，得到实际 `HasDerivAt` 结论：

$$
F_{\mathrm{loc}}'(0)=\mu c(\epsilon+\kappa)\xi^2.
$$

`initial_localEnergy_rate_pos` 在正参数与 $\xi\ne0$ 下证明右端为正。此定理没有输入目标能量导数，也没有声称所给路径已满足完整 PDE。调用者仍须提供初始导数证据；前面的初始场导数定理说明其中 $E_t(0),P_t(0)$ 如何从原方程初值获得。

| 层次 | 结论与限制 |
|---|---|
| 初值耗散的计算 | 点态等式、符号和实际积分；严格积分负性需正平方积分 |
| 正则 PDE 解的 $\mathcal F_c'(0)>0$ | 条件性解释：需完整 (7.6)、其适用正则性和 PEC 消去边界项 |
| 存在这样的 PDE 解 | 本阶段未证明 |

局部密度求导与特殊初值积分都不包含一般路径的积分求导交换。因此不能把第二、三层合并称为“已构造完整二维 PDE 反例”。这个障碍针对 V7 的单层候选，不否定两层能量或所有能量。

## 8. 第二层补入的控制

v0.2.3 的单方向辅助演化是

$$
l_t=V+\sigma_jh-\sigma_i l.
$$

`hasDerivAt_initial_flux` 从真实演化证据及 $h(0)=l(0)=0$ 得到 `HasDerivAt l V 0`，对任意吸收值成立。只有另证 $V=\partial_i f$，才能将它解释为完整场关系 $\lambda_t(0)=\nabla f$。

第二层分量初值取 $h_1=\Lambda_1=(g_x,g_y)$，从零吸收空间耗散得到

$$
S_{1,\mathrm{initial}}=c(g_x^2+g_y^2).
$$

`secondLayerSpatialInitial` 复用 `spatialDissipation2D`；`secondLayerSpatialInitial_zero` 调用 v0.2.3 独立零区公式，没有除以吸收或删除 $c|\nabla f|^2$ 对应项。

全域版本 `secondLayerSpatialInitial_eq` 需要独立的分量支撑条件：

$$
g_x\ne0\ \text{或}\ g_y\ne0\Longrightarrow p=r=0.
$$

不能直接用 $f$ 的支撑代替它，因为当前 $g_x,g_y$ 是独立参数。真实光滑紧支撑函数的梯度支撑性质，以及梯度与这两个参数的对应，均须另证。

`secondLayerSpatialInitial_integral` 对实际分量函数和测度，在分量支撑几乎处处成立、两份平方可积的条件下，证明密度可积及

$$
\int S_{1,\mathrm{initial}}\,dm
=c\left(\int g_x^2\,dm+\int g_y^2\,dm\right).
$$

这是分量的实际积分，尚不是已构造真实梯度的定理。第一层缺少抵住 $\|f\|^2$ 负项的空间贡献；第二层预期提供 $\|\nabla f\|^2$。后续 Poincaré 将以 $\|f\|^2\le C_P^2\|\nabla f\|^2$ 联系两者，还需参数预算、Debye 耗散和完整两层恒等式才能闭合。本阶段未证明这些闭合步骤。

## 9. 声明索引与阅读方法

以下是当前文件的完整定理名，可直接用于 `#check`。

| 完整声明名 | 层次与主要条件 |
|---|---|
| `LeanPML.PML.Obstructions.absorption_mul_initial_zero` | 点态；支撑推出 $a\xi=b\xi=0$ |
| `LeanPML.PML.Obstructions.initial_compatibility` | 点态；支撑保证五项初始兼容代数 |
| `LeanPML.PML.Obstructions.initial_derivative_values` | 代数；初始方程、$\epsilon,\tau\ne0$ |
| `LeanPML.PML.Obstructions.hasDerivAt_initial_fields_zero` | 真实时间；导数证据、初值与初始方程 |
| `LeanPML.PML.Obstructions.electricRemainder_initial` | 点态；电块多项式计算 |
| `LeanPML.PML.Obstructions.polarRemainder_initial` | 点态；$\kappa\ne0$ 下的极化计算 |
| `LeanPML.PML.Obstructions.spatialDissipation_initial` | 点态；零空间初值 |
| `LeanPML.PML.Obstructions.initialDissipation_eq` | 点态；三块相加、支撑、$\kappa\ne0$ |
| `LeanPML.PML.Obstructions.initialDissipation_nonpos` | 点态符号；$\epsilon,\kappa,\mu,c>0$ |
| `LeanPML.PML.Obstructions.initialDissipation_neg` | 点态严格符号；再加 $\xi\ne0$ |
| `LeanPML.PML.Obstructions.singleLayerEnergy_initial` | 点态；初始能量数值，允许任意实参数 |
| `LeanPML.PML.Obstructions.hasDerivAt_initial_localEnergy` | 真实时间；真实导数与初值、$\kappa\ne0$ |
| `LeanPML.PML.Obstructions.initial_localEnergy_rate_pos` | 导数值符号；正参数、$\xi\ne0$ |
| `LeanPML.PML.Obstructions.initialDissipation_integral` | 实际积分；支撑、平方可积、$\kappa\ne0$ |
| `LeanPML.PML.Obstructions.initialDissipation_integral_neg` | 实际积分负性；再加正参数、正平方积分 |
| `LeanPML.PML.Obstructions.initialDissipation_rectangle_integral` | 全开矩形 Lebesgue 积分入口 |
| `LeanPML.PML.Obstructions.hasDerivAt_initial_flux` | 真实时间；辅助演化、零空间初值 |
| `LeanPML.PML.Obstructions.secondLayerSpatialInitial_zero` | 零吸收点态分量 |
| `LeanPML.PML.Obstructions.secondLayerSpatialInitial_eq` | 全域点态分量；独立分量支撑 |
| `LeanPML.PML.Obstructions.secondLayerSpatialInitial_integral` | 实际分量积分；分量支撑、平方可积 |

建议先读 `initial_compatibility` → `initialDissipation_eq` → `initialDissipation_rectangle_integral`（它调用一般积分定理），再读真实局部时间率与第二层。先弄清初值、三块相加和积分，再区分导数与空间接口。

在 VS Code 中，将光标放在 `by` 后或每个 `have`、`calc` 的下一行，InfoView 会显示当前假设与目标。读 `initialDissipation_eq` 时观察 `by_cases` 两支：一支值为零但吸收任意，另一支用支撑消去吸收。读积分证明时，先看 `hdensity_ae` 的函数几乎处处相等，再看它如何进入积分。F12 可跳到旧块或 mathlib 引理，区分本项目的初值证明与库提供的积分规则。

积分计算主要调用以下 mathlib 引理；位置对应项目当前锁定的 mathlib，可用 F12 查看完整假设。三块定义与求导来自旧阶段模块，初值组合与本节 20 条结论则是本阶段新增。

| mathlib 完整名称 | 当前依赖中的源码位置 |
|---|---|
| `MeasureTheory.integral_add` | [Bochner/Basic.lean:241](../.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:241) |
| `MeasureTheory.integral_const_mul` | [Bochner/Basic.lean:292](../.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:292) |
| `MeasureTheory.integral_congr_ae` | [Bochner/Basic.lean:303](../.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:303) |
| `MeasureTheory.Integrable.congr` | [L1Space/Integrable.lean:122](../.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:122) |
| `MeasureTheory.Integrable.add` | [L1Space/Integrable.lean:420](../.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:420) |
| `MeasureTheory.Integrable.const_mul` | [L1Space/Integrable.lean:1037](../.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:1037) |

## 10. 验证记录与下一步

本阶段最终源码已实际构建与独立公理审计通过；命令工作目录均为本工程根目录：

| 命令 | 退出码 | 完整输出及执行元数据 |
|---|---|---|
| `lake build` | 0 | [构建输出](../logs/v0.2.4/20261011T231924_138774_lake_build.log)、[命令/目录/时间记录](../logs/v0.2.4/20261011T231924_138774_lake_build.json) |
| `lake env lean Audit.lean` | 0 | [审计输出](../logs/v0.2.4/20261011T231954_467990_axioms_audit.log)、[命令/目录/时间记录](../logs/v0.2.4/20261011T231954_467990_axioms_audit.json) |

构建输出明确包含 `LeanPML.PML.Obstructions.SingleLayer`。独立审计覆盖全部 154 条定理，其中本阶段新增 20 条；依赖仅见 `propext`、`Classical.choice`、`Quot.sound`，未出现 `sorryAx`。这些是 Lean/mathlib 使用的标准基础公理，不是本项目引入的证明占位。PDF 标注的版本、范围和视觉验收另以标注账本及其实际记录为准。

在工程根目录复现：

```sh
python3 scripts/run_logged.py --stage v0.2.4 lake_build lake build
python3 scripts/run_logged.py --stage v0.2.4 axioms_audit lake env lean Audit.lean
```

正式导入入口须包含新模块，`Audit.lean` 须保留全部旧审计并加入新增定理；标准基础公理允许出现，`sorryAx` 和自定义占位公理不得出现。失败及修复记录保存在 `logs/v0.2.4`，不覆盖历史。

仍缺的接口包括：真实梯度与混合微分交换、磁场到通量映射、完整提升和五不变量保持、光滑紧支撑数据的正积分与空间资格、加权状态空间、一般积分求导、Green/PEC、Poincaré、完整两层闭合和解存在性。PDF 的红勾按点态、局部时间和特殊初值积分分别限定，详见 [标注账本](pdf_formalization_marks.md)。

下一阶段 **v0.3.1** 进入实际内积、加权状态与能量定义，计划模块是 `Analysis/EnergyCalculus.lean`、`PML/State.lean`、`PML/Energy.lean`。需将 $v,v_t,R,z,\psi,\Lambda$ 放入真实路径/场空间，明确梯度、散度及定义域接口；无界权重不能当成普通 $L^2$ 上的有界乘子。本轮不提前实现这些模块。
