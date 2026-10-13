# V7 公式与拟建 Lean 定理清单

用途：把纸面公式拆成可逐项检查的数学命题，说明每条结论究竟需要哪些假设、前置引理和分析接口，避免只形式化一个容易通过却弱于原问题的命题。本文是 **v0.0.2 的语义设计文档**，不是证明源码或编译报告。

核查日期：2026-10-06（Asia/Shanghai）。配套阅读：[模型合同](model_contract.md)、[范围与待核验事项](scope.md)、[来源清单](source_inventory.md)、[历史结论状态表](claim_ledger.md)。本文件不改写 v0.0.1 的历史状态。

## 1. 来源、证据层次和记号

来源编号沿用来源清单：

- **R**：[路线图](../ROADMAP_lean_PML_revised.md)，主要使用 §§4–5、v0.0.2，以及后续阶段中已写明的模块边界。
- **S1**：[原问题](../../sources/energy_functional_problem.tex)，原八变量、Debye 特例、PEC 与总体目标。
- **S2**：[V7 正文](../../results/V7_Maxwell_Debye_PML/V7_global_energy.md)，下文未另注明来源的公式编号均指此文件。
- **S3a**：[V7 证明审查](../../results/V7_Maxwell_Debye_PML/proof_audit.md)，用于定位假设用途；它是作者自审，不是独立机器证明。
- **S5**：[旧 Lean 覆盖审查](../../results/lean_core_theorem_coverage_review_20260924.md)，说明旧代数代码不能替代完整 PDE 证明。
- **S7**：[V7 符号脚本](../../results/V7_Maxwell_Debye_PML/verify_v7.py)，本轮只读源码；**H1**：[其历史输出](../../results/V7_Maxwell_Debye_PML/verification_output.txt)，本轮未复跑。

本轮按文件字节复核 S1、S2、S3a、S7 的 SHA-256，四者分别仍为来源清单中的 `1e09c1b7…`、`0a7f73a2…`、`a2b2ac0a…`、`b7574163…`，完整值见来源清单；未发现这四份来源版本变化。R 的本轮哈希已由 `a11280c6…` 变为 `16c14617…`，无法仅凭旧哈希重建具体文本差异；本轮重新阅读其 §§4–5、v0.0.2 并核对 S1/S2，完整版本记录见 [scope.md](scope.md)。相同哈希仅确认版本，没有把历史符号运行或纸面主张升级为本轮数学验证。

**全部 Lean 名称、命名空间、模块路径均为计划，未创建、未实现、未编译。** 条目中的 `PML.X` 为建议命名空间，模块路径相对未来 `LeanPML/` 源码目录；名称可以在未来 API 设计中调整，数学语义不得随之悄悄减弱。

| 类别 | 本文中的准确含义 |
|---|---|
| `SPEC` | 模型、空间、能量或假设的定义规格，不是证明成果 |
| `ALG` | 实数／系数／二次型的代数结论；出现 `Pt` 等名字不代表实际导数 |
| `TIME` | 对真实时间函数或函数空间路径求导、积分、推导不变量与区间单调性 |
| `ABSTRACT` | 使用显式 Green、Poincaré、空间定义域等接口的条件性分析定理 |
| `PDE-SMOOTH` | 在真实矩形、明确光滑解类上兑现必要接口的具体 PDE 先验定理 |
| `PDE-V7` | 兑现 S2 所声明加权 Sobolev／图空间范围的具体先验定理 |

下文的类别描述**目标命题的层次**，不表示当前达到了该层次。`ABSTRACT → PDE-SMOOTH/PDE-V7` 表示后续应分别给出条件性版本和兑现空间接口的版本。`PDE-V7` 并不表示另证了解存在、唯一性或最小正则性。

统一记号：$\sigma_x=p,\sigma_y=r$，$a=p+r,b=pr$，$A=\epsilon+2\kappa$，$Z=\{a=0\}$，$\Omega_+=\{a>0\}$。$S$ 是吸收幅度上界，$\mathscr S_j$ 是空间耗散，二者不可混用。$\psi$ 在一层状态 $U=(v,R,z,\psi)$ 中是二维辅助场；S2 反例中的同名标量测试函数在本文改记 $\xi$，不改变反例。全部范数未另注明时均为 $L^2(\Omega)$ 范数。$\mathcal N_7^2=N_0^2+KN_1^2$ 是方便跨文档使用的记号，S2 (6.5)–(6.7) 写的是其右侧展开式。

S2 把 N 写作 N(U)，但其中含实际 v_t；实现时所用图状态必须包括这个时间导数坐标及其与路径的联系，不能假定任意瞬时四元组自动确定 v_t。导数恒等式先以 $0<t<T$ 的真实导数为目标；端点采用何种单侧／区间导数表达留待接口设计，时间单调性与积分平衡仍覆盖整个闭区间及 T=0。此处是语义展开，不是新增 PDE 限制。

## 2. 模型对应、兼容类和参数

表中依赖使用稳定条目编号 T01–T37；这是预期证明依赖，不是已存在的 Lean 导入关系。

### T01：S1 原模型；S2 (1.1)、(2.1)、(2.2)

**类别：**

SPEC／ALG

**输入假设与数学结论：**

正材料参数，$\alpha=1$，

$$
p=\sigma_x^{old}/\epsilon_0,r=\sigma_y^{old}/\epsilon_0
$$

 → 原八变量方程逐项等价于归一化方程，外边界仍为整个矩形 PEC

**依赖条目与基础引理：**

常数代数替换

**现有证据：**

S1、S2 §2.1 的纸面对应

**未完成接口：**

真实场及原方程定义；每条辅助方程符号核对；不能删 $P$

**拟建名称及模块（全部计划）：**

`PML.normalizedSystem_iff_original`；`PML/OriginalSystem.lean`

### T02：(2.3)

**类别：**

SPEC／TIME

**输入假设与数学结论：**

给定原场、初始原函数及时间可积／连续性 → 因果提升 $u=u_0+\int_0^tE$、$q=q_0+\int_0^tP$，实际 $u_t=E,q_t=P$，

$$
\lambda=(\mu H_y,-\mu H_x),\phi=\lambda-\nabla u
$$

**依赖条目与基础引理：**

T01；微积分基本定理

**现有证据：**

S2 §2.2 纸面定义

**未完成接口：**

函数空间积分、梯度定义域、时间与梯度交换

**拟建名称及模块（全部计划）：**

`PML.lift_hasTimeDerivatives`；`PML/PrimitiveSystem.lean`

### T03：**(2.4)**

**类别：**

TIME → PDE-SMOOTH/PDE-V7

**输入假设与数学结论：**

原 PDE、T02 真实导数、系数时间不变 → 五个不变量各自等于初值；若五个初值为零，则全时段为零

**依赖条目与基础引理：**

T01–T02；导数为零推出区间常数；磁场时间／空间交换

**现有证据：**

S2 §2.2 推导；S7 的 `Qxt-p*phiyt`、`Qyt+r*phix_t` 两个展开检查；H1 历史记录

**未完成接口：**

三个标量时间不变量和两个磁辅助不变量的真实场证明；端点连续性

**拟建名称及模块（全部计划）：**

`PML.fiveInvariants_eq_initial`；`PML/TimeInvariants.lean`、`PML/Equivalence.lean`

### T04：**(2.5)、(2.6)**；命题 2.1

**类别：**

TIME → PDE-SMOOTH/PDE-V7

**输入假设与数学结论：**

原 PDE、兼容初值、T03 → 四个辅助变量重构及齐次 primitive 系统；反向从正则 primitive 解重构出全部原方程

**依赖条目与基础引理：**

T01–T03；重构代入；

$$
\operatorname{div}\lambda=\mu(\partial_xH_y-\partial_yH_x)
$$

**现有证据：**

S2 命题 2.1 纸面证明；S7 仅支持部分磁辅助展开

**未完成接口：**

双向场层映射、四个辅助方程反向核对；非零不变量的附加源项不能省略

**拟建名称及模块（全部计划）：**

`PML.original_iff_primitive_onCompatibleData`；`PML/Equivalence.lean`

### T05：定义 5.1；(6.5)–(6.6) 的初值要求

**类别：**

SPEC

**输入假设与数学结论：**

存在 $u_0\in H_0^1$，定义 $q_0,\lambda_0,\phi_0$，满足四个初值重构、$\phi_0\in L_w^2$ → 定义 $\mathfrak C_c$；另登记主定理追加的 PDE 生成一阶时间层有限及 PEC 迹相容要求

**依赖条目与基础引理：**

T01–T02、T10–T11；初始导数由 PDE 计算

**现有证据：**

S2 §5.2 明确要求；S3a 记录用途

**未完成接口：**

存在提升的谓词、时间导数初值与实际 PDE 的联系；不得把导数层当自由数据

**拟建名称及模块（全部计划）：**

`PML.CompatibleInitialData`（拟定义）；`PML/CompatibilitySpace.lean`

### T06：(5.7)、(5.8) 及其后未编号估计

**类别：**

TIME → PDE-SMOOTH/PDE-V7

**输入假设与数学结论：**

初始加权有限、辅助 ODE、所需未加权正则性及 $\int_0^t\Vert \nabla u(s)\Vert ^2ds<\infty$（导数估计另需 $\lambda\in L^2$）→ 零吸收区 $\phi=0$ 保持，记忆公式、$L_w^2$ 保持与 $\phi_t$ 加权估计

**依赖条目与基础引理：**

T03–T05、T10；变参数公式、时间 Cauchy–Schwarz、积分估计

**现有证据：**

S2 §5.2 纸面公式；S7 未覆盖

**未完成接口：**

实际 ODE 解公式及加权积分合法性；不得先假设待证的全时段加权保持，也不能由普通光滑性直接宣称奇异权重可积

**拟建名称及模块（全部计划）：**

`PML.weightedCompatibility_preserved`；`PML/CompatibilitySpace.lean`、`PML/WeightedCalculus.lean`

### T07：§5.3（无公式编号）

**类别：**

PDE-V7；可先作光滑版

**输入假设与数学结论：**

同一原状态的两个兼容提升、分离系数、零迹 → 提升唯一；能量不依赖未固定的原函数规范

**依赖条目与基础引理：**

T04–T05、T08；Sobolev 切片、零水平集上的弱梯度结论

**现有证据：**

S2 §5.3 纸面论证；S3a 状态与规范段

**未完成接口：**

切片零迹与 a.e. 代表元；$g=0$ 的推导；此处“唯一”不是 PDE 解唯一性

**拟建名称及模块（全部计划）：**

`PML.compatibleLift_unique`；`PML/LiftUniqueness.lean`

### T08：(5.1)

**类别：**

ABSTRACT → PDE-SMOOTH/PDE-V7

**输入假设与数学结论：**

$L_x,L_y>0,v\in H_0^1(\Omega)$ → 

$$
\Vert v\Vert ^2\le C_P^2\Vert \nabla v\Vert ^2
$$

，$C_P^2=(\pi^2/L_x^2+\pi^2/L_y^2)^{-1}$

**依赖条目与基础引理：**

一维 Wirtinger、Fubini、必要的密度推广

**现有证据：**

S2 §5.1 给出证明路线；S7 未覆盖

**未完成接口：**

精确矩形常数；较保守常数只能形成另行登记的参数版本

**拟建名称及模块（全部计划）：**

`Rectangle.poincare_exact`；`Rectangle/Poincare.lean`

### T09：**(5.3)**，连同 (5.2)、(5.4)

**类别：**

SPEC／ALG

**输入假设与数学结论：**

正材料及 $C_P,K$；$0<c\le c_*$、$S\le c/4$ → 等价小量条件及 $a\le c/2,b\le c^2/16,ac-b\ge0,c\tau<1/16$

**依赖条目与基础引理：**

T08 给常数语义；有序域、平方根／最小值等价

**现有证据：**

S2 §5.1；R v0.2.1；S7 只算一个参数例子

**未完成接口：**

一般参数证明；必须包含 $p=r=0$、单轴零吸收，不额外加正下界

**拟建名称及模块（全部计划）：**

`PML.smallness_iff_explicitBounds`、`PML.smallness_consequences`；`PML/Coefficients.lean`

### T10：(5.5)–(5.6)，(7.2)，(9.2) 的分支权重

**类别：**

SPEC／ALG → PDE-V7

**输入假设与数学结论：**

T09；在 $a>0$ 与 $a=0$ 分支定义权重 → $w_i\ge3/2$ 于 $\Omega_+$，$L_w^2\hookrightarrow L^2$，耗散系数有界；$\theta_x+\theta_y=1$

**依赖条目与基础引理：**

T09；可测性、加权积分、范数性质

**现有证据：**

S2 §§5.1、7.1、9.2；R v0.2.1

**未完成接口：**

构造真正加权空间及等价类；$w_i$ 可无界；$\theta_i=1/2$ 于 Z，不是零

**拟建名称及模块（全部计划）：**

`PML.weightedL2_embedding`、`PML.weights_branch_bounds`；`PML/Weights.lean`、`PML/CompatibilitySpace.lean`

T03 的五个时间不变量（可为空间函数）必须是

$$
C_D=q+\tau P-\kappa u,\quad C_{z1}=Z_1+\epsilon bu,\quad
C_{z2}=Z_2+bq,\quad C_x=Q_x-p\phi_y,\quad C_y=Q_y+r\phi_x.
$$

T04 在五个初值不变量为零时应推出的重构是

$$
Z_1=-\epsilon bu,\quad Z_2=-bq,\quad Q_x=p\phi_y,\quad Q_y=-r\phi_x.
$$

其 primitive 结论包括

$$
\begin{aligned}
\mu[\epsilon(u_{tt}+au_t+bu)+P_t+aP+bq]&=\operatorname{div}\lambda,\\
\phi_{x,t}+p\phi_x&=(r-p)\partial_xu,\\
\phi_{y,t}+r\phi_y&=(p-r)\partial_yu,\\
\lambda&=\nabla u+\phi,\quad q_t=P,\quad q+\tau P=\kappa u,\quad u_t=E.
\end{aligned}
$$

这些是从原模型推出的结论。最终从原八变量出发的主定理不能只收一个没有证明来历的 primitive 状态。（来源：S2 (2.4)–(2.6)，R v0.4.4。）

T09 对应的显式条件为

$$
K=8\mu A C_P^2>0,\quad 0<c,\quad c^2K\le1,\quad
8cAK\le\kappa\tau,\quad8cA\tau\le\kappa,\quad
0\le p,r\le S\le c/4\quad\text{a.e.}
$$

在参数正性的前提下，需另证其与 S2 的 $c_*$ 最小值表达式等价；本轮只登记拟验证命题。$S=\max(\Vert p\Vert _\infty,\Vert r\Vert _\infty)$ 的范数界是本质上确界意义。量词不要求任何 $p,r$ 的严格正下界。（来源：S2 (5.2)–(5.4)，R v0.2.1。）

## 3. 实际能量、局部导数和两层恒等式

### T11：(6.1)–(6.5)

**类别：**

SPEC／ABSTRACT → PDE-V7

**输入假设与数学结论：**

受约束路径 $z_t=R,z+\tau R=\kappa v,\Lambda=\nabla v+\psi$，$v\in H_0^1,\psi\in L_w^2$ → 定义实际 $\mathcal F_c,\mathcal E_7,N,\mathcal N_7$，并验证 N 在声明状态空间上为范数

**依赖条目与基础引理：**

T08–T10；实内积空间及零范数分离

**现有证据：**

S2 §6 纸面定义与说明

**未完成接口：**

路径导数／状态坐标关系；真实积分及可积性；不能仅命名 `WeightedL2`

**拟建名称及模块（全部计划）：**

`PML.singleLayerEnergy`、`PML.twoLayerEnergy`（拟定义），`PML.graphNorm_eq_zero_iff`；`PML/State.lean`、`PML/Energy.lean`

### T12：(6.3)、(6.6)，§7.3 两层迹

**类别：**

TIME／ABSTRACT → PDE-SMOOTH/PDE-V7

**输入假设与数学结论：**

同一个 primitive 解、系数时间不变、明确正则性与 PEC → U1 是 U0 的时间导数层，仍满足 primitive 型系统；$u,E,E_t$ 的零迹及两层通量合法

**依赖条目与基础引理：**

T02–T06；时间求导、梯度／散度交换、零迹空间闭性

**现有证据：**

S2 §§6–7、S3a 正则性用途；S7 未覆盖

**未完成接口：**

$\lambda_t\in H(\mathrm{div})$、实际高阶导数；两层各自的边界证据

**拟建名称及模块（全部计划）：**

`PML.timeDerivativeLayer_satisfies_primitive`；`Rectangle/TimeSpace.lean`、`PML/WeightedCalculus.lean`

### T13：(7.3)

**类别：**

ALG + TIME

**输入假设与数学结论：**

时间不变的空间系数（固定空间点下作为代数参数）与实际 $v,v_t,v_{tt}$ → 电块乘积等于指定二次型导数加余项

**依赖条目与基础引理：**

T09、T11；链式／乘积法则

**现有证据：**

S2 §7.2；S7 `general constant-shift electric identity`；H1 历史记录

**未完成接口：**

从独立代数变量到真实时间路径，随后接内积积分

**拟建名称及模块（全部计划）：**

`PML.electricBlock_algebra`、`PML.electricBlock_hasDerivAt`；`PML/LocalElectric.lean`

### T14：(7.4)

**类别：**

ALG + TIME

**输入假设与数学结论：**

$z_t=R,z+\tau R=\kappa v$，$\kappa>0$，真实导数 → Debye 块精确导数和耗散表达

**依赖条目与基础引理：**

T11；对约束求导；乘积法则

**现有证据：**

S2 §7.2；S7 `general constant-shift Debye identity`；H1 历史记录

**未完成接口：**

$R_t$ 与 $v_t$ 关系及内积求导；不得直接假设耗散非负

**拟建名称及模块（全部计划）：**

`PML.debyeBlock_algebra`、`PML.debyeBlock_hasDerivAt`；`PML/LocalDebye.lean`

### T15：(7.1)–(7.2)

**类别：**

ALG + TIME → ABSTRACT

**输入假设与数学结论：**

辅助演化、$l=h+f$、实际导数；a>0 用有理权重，a=0 用 f=0,l=h → 空间块导数、完整非负 $\mathscr S[U]$

**依赖条目与基础引理：**

T04、T10–T12；两个分支平方项求导

**现有证据：**

S2 §7.1；S7 `general constant-shift spatial identity` 仅正分母代数；H1 历史记录

**未完成接口：**

零吸收分支、实际 $h=\partial_i v$ 与 $V=\partial_i v_t$；加权路径链式法则

**拟建名称及模块（全部计划）：**

`PML.spatialBlock_positiveAbsorption`、`PML.spatialBlock_zeroAbsorption`；`PML/LocalSpatial.lean`

### T16：(7.5)，§7.3 边界讨论

**类别：**

ABSTRACT → PDE-SMOOTH/PDE-V7

**输入假设与数学结论：**

$v_t+cv$ 有零迹、$\Lambda\in H(\mathrm{div};\Omega)$ → 全域 Green 配对及边界消去；若分区则证明成对界面相消

**依赖条目与基础引理：**

T08 的域与迹表示、T12；Green／分部积分

**现有证据：**

S2 §7.3、S3a 零吸收与界面段；S7 未覆盖

**未完成接口：**

真矩形积分、四边边界、弱法向迹；不在可能不规则的 $\Omega_+$ 上强加 Green

**拟建名称及模块（全部计划）：**

`Rectangle.green`、`PML.layer_boundaryFlux_zero`；`Rectangle/Green.lean`、`Rectangle/Boundary.lean`

### T17：(7.6)–(7.7)

**类别：**

ABSTRACT → PDE-SMOOTH/PDE-V7

**输入假设与数学结论：**

一层 primitive PDE、T13–T16 及合法积分求导 → $\mathcal F_c'=-\mathcal D_c+$边界配对

**依赖条目与基础引理：**

T11、T13–T16；实际积分／内积求导

**现有证据：**

S2 §7.3 纸面组合；S7 只检查局部代数块

**未完成接口：**

各项可积、导数合并、PDE 与 Green 的实际调用；不声明 $\mathcal D_c\ge0$

**拟建名称及模块（全部计划）：**

`PML.singleLayer_balance_Abstract`；`PML/BalanceAbstract.lean`

### T18：**(7.8)**

**类别：**

ABSTRACT + TIME → PDE-SMOOTH/PDE-V7

**输入假设与数学结论：**

T12 同源两层、两层 T17、两层零迹、常数 K → $\mathcal E_7'=-\mathcal D_7$，其中 

$$
\mathcal D_7=\mathcal D_c[U_0]+K\mathcal D_c[U_1]
$$

**依赖条目与基础引理：**

T11–T12、T16–T17；和与常数倍求导

**现有证据：**

S2 (7.8)、S3a；无完整 Lean 证据

**未完成接口：**

完整场空间求导链；本恒等式是结论，不能放进最终主定理假设

**拟建名称及模块（全部计划）：**

`PML.twoLayer_balance_Abstract`；`PML/BalanceAbstract.lean`

实际一层耗散必须保留 S2 (7.7) 的全部项：

$$
\begin{aligned}
\mathcal D_c[U]=\mathscr S[U]
&+\mu\epsilon\int_\Omega[(a-c)v_t^2+bcv^2]\\
&+\frac\mu\kappa\int_\Omega[\tau R_t^2+(a-c+\tau(ac-b))R^2+bcz^2].
\end{aligned}
$$

其中 $a-c$ 可能为负。T18 仅给出精确恒等式，**还没有推出单调性**。另须注意 T15 在 Z 上的 $c|\nabla v|^2$ 项必须纳入 $\mathscr S$；不能因为吸收为零就把整个空间耗散密度设成零。（来源：S2 (7.1)–(7.8)、§11.1。）

## 4. 正定性、跨边层控制与耗散闭合

### T19：(8.1)–(8.2)

**类别：**

ALG

**输入假设与数学结论：**

$z=\kappa v-\tau R$、小量条件 → 极化二次型约束消元；$3/4\le A_R\le5/4$、$0\le1-a\tau-b\tau^2\le1$、G 与 $b+ac$ 上界

**依赖条目与基础引理：**

T09、T11；多项式恒等式及有序代数

**现有证据：**

S2 §8；S7 `compatibility-reduced polarization quadratic` 仅检查 (8.1) 展开

**未完成接口：**

一般系数界 (8.2)；不能以展开为零替代正定性

**拟建名称及模块（全部计划）：**

`PML.polarization_reduced`、`PML.reducedCoefficients_bounds`；`PML/LocalDebye.lean`

### T20：(8.3)，§§8.1–8.2

**类别：**

ABSTRACT → PDE-SMOOTH/PDE-V7

**输入假设与数学结论：**

约束状态、权重嵌入、Poincaré、小量界 → $\Vert \nabla v\Vert ^2\le2B_{sp}$、$\Vert v\Vert ^2\le2C_P^2B_{sp}$；$N(U)^2/4\le\mathcal F_c[U]\le N(U)^2$

**依赖条目与基础引理：**

T08–T11、T19；积分 Young 不等式

**现有证据：**

S2 §8 纸面估计；S7 未覆盖空间吸收

**未完成接口：**

真实 L² 内积／积分与 Poincaré；同一组 c,K；不要求任意独立点态变量正定

**拟建名称及模块（全部计划）：**

`PML.singleLayer_coercivity_Abstract`；`PML/Coercivity.lean`

### T21：**(6.7)**

**类别：**

ABSTRACT → PDE-SMOOTH/PDE-V7

**输入假设与数学结论：**

实际两层状态、K>0、每层 T20 → 

$$
\mathcal N_7^2/4\le\mathcal E_7\le\mathcal N_7^2
$$

，特别是能量非负

**依赖条目与基础引理：**

T11–T12、T20；非负倍数相加

**现有证据：**

S2 §8 末对应 (6.7)；无完整 Lean 证据

**未完成接口：**

每层确实处于相同约束空间；提升规范另由 T07 负责

**拟建名称及模块（全部计划）：**

`PML.twoLayer_graphNorm_bounds_Abstract`；`PML/Coercivity.lean`

### T22：(9.2)–(9.4)

**类别：**

ALG／TIME／ABSTRACT

**输入假设与数学结论：**

分支 $\theta_i$、小量条件、辅助演化及 $\lambda=\nabla u+\phi$ → 定义 J，$\mathscr S[U]\ge(c-S)J(U)\ge3cJ(U)/4$，并推出梯度 E 的精确关系

**依赖条目与基础引理：**

T04、T09–T12、T15；时间／梯度交换

**现有证据：**

S2 §9.2 纸面逐项推导；S7 未覆盖

**未完成接口：**

J 的可积性、Z 分支；梯度关系从 PDE 推导，不能假定全部场分量独立

**拟建名称及模块（全部计划）：**

`PML.spatialDissipation_ge_J`、`PML.gradientE_identity`；`PML/GradientControl.lean`

### T23：**(9.5)**

**类别：**

ABSTRACT → PDE-SMOOTH/PDE-V7

**输入假设与数学结论：**

T22 梯度关系、$\theta_i+\theta_j=1$、系数上界及同源两层 → $\Vert \nabla E\Vert ^2\le3J(U_1)+3S^2J(U_0)$

**依赖条目与基础引理：**

T10–T12、T22；三项平方和、权重比较、积分单调性

**现有证据：**

S2 §9.2 纸面证明；S3a 标为关键闭合；S7 未覆盖

**未完成接口：**

点态关系到真实积分；所有零／单轴／双轴吸收分支；不得收作“解”的公理

**拟建名称及模块（全部计划）：**

`PML.gradientE_bound_Abstract`；`PML/GradientControl.lean`

### T24：(9.1)

**类别：**

ABSTRACT

**输入假设与数学结论：**

$R=\kappa v_t-\tau R_t$、$ac-b\ge0,c\tau\le1/4$ 及显式 $\mathcal D_c$ → 两层下界，明确剩余两个负项

**依赖条目与基础引理：**

T09、T11–T12、T17–T18；平方和与积分估计

**现有证据：**

S2 §9.1 纸面计算；S7 未覆盖完整不等式

**未完成接口：**

对实际 Debye 路径推导 R 关系；两个耗散预算不可重复扣除

**拟建名称及模块（全部计划）：**

`PML.twoLayer_dissipation_preliminary`；`PML/DissipationClosure.lean`

### T25：**(9.6)**

**类别：**

ABSTRACT → PDE-SMOOTH/PDE-V7

**输入假设与数学结论：**

E 零迹、Poincaré、T22–T23、$K=8\mu AC_P^2$ → 

$$
\mu cA\Vert E\Vert ^2\le(K/2)(\mathscr S_1+S^2\mathscr S_0)
$$

**依赖条目与基础引理：**

T08–T09、T12、T22–T23

**现有证据：**

S2 §9.2 纸面估计；S7 只输出某参数下 $KS^2$ 数值

**未完成接口：**

E 的具体零迹与 Poincaré 接口；$KS^2\le1/16$ 对一般参数的精确证明

**拟建名称及模块（全部计划）：**

`PML.absorb_electric_lowerLayer`；`PML/DissipationClosure.lean`

### T26：**(9.7)**

**类别：**

TIME／ALG → ABSTRACT

**输入假设与数学结论：**

实际 Debye 导数 $\kappa E_t=P_t+\tau P_{tt}$ 与两条材料小量界 → 最高时间负项被 Debye 耗散吸收

**依赖条目与基础引理：**

T09、T12、T14；平方和及系数比较

**现有证据：**

S2 §9.3 纸面逐项估计；S7 的两个吸收比值是具体例子的浮点比较

**未完成接口：**

真实二阶极化导数；$\kappa,\tau,K>0$ 及两个不同小量条件逐一使用

**拟建名称及模块（全部计划）：**

`PML.absorb_electric_timeDerivative`；`PML/DissipationClosure.lean`

### T27：**(6.8)**

**类别：**

ABSTRACT → PDE-SMOOTH/PDE-V7

**输入假设与数学结论：**

T18 精确导数、T24 下界、T25–T26 吸收 → 显式剩余耗散下界及 $\mathcal D_7\ge0$

**依赖条目与基础引理：**

T09、T15、T18、T24–T26；非负积分与合并估计

**现有证据：**

S2 §9 末和定理 6.1；S3a；无完整 Lean 证据

**未完成接口：**

合并证明、预算核对；非负性是结论，禁止以 `hDiss : ∀ t, 0 ≤ D7 t` 代替

**拟建名称及模块（全部计划）：**

`PML.twoLayer_dissipation_lowerBound_Abstract`；`PML/DissipationClosure.lean`

### T28：**(6.9)**

**类别：**

TIME → ABSTRACT/PDE-SMOOTH/PDE-V7

**输入假设与数学结论：**

闭区间连续、内部实际导数 T18、时间可积／足够连续的 D7、T27 → 任意两时刻积分平衡及单调不增

**依赖条目与基础引理：**

T18、T27；区间微积分基本定理／导数符号与单调性；T=0 单独处理

**现有证据：**

S2 §9 末纸面时间积分；外部标量工程仅提供可参考方法

**未完成接口：**

仅在 [0,T] 的导数与端点接口；积分平衡不能由“已证单调”直接推出

**拟建名称及模块（全部计划）：**

`PML.energy_balance_onInterval`、`PML.energy_antitoneOn_Abstract`；`Analysis/EnergyCalculus.lean`、`PML/MainAbstract.lean`

### T29：**(6.10)**；(8.4)–(8.8)

**类别：**

ABSTRACT → PDE-SMOOTH/PDE-V7

**输入假设与数学结论：**

T21、原变量重构、系数上界 → 原电磁／极化及四辅助变量 L² 控制；同时控制 u,q,φ

**依赖条目与基础引理：**

T04、T08–T11、T20–T21；有界系数乘法、平方和

**现有证据：**

S2 §8.3 的显式常数；S7 未覆盖

**未完成接口：**

各项真实范数和 a.e. 重构；不得推反向裸八变量 L² 上界

**拟建名称及模块（全部计划）：**

`PML.physicalFields_controlled`、`PML.auxiliaryFields_controlled`；`PML/PhysicalControl.lean`

### T30：定理 6.1 的明确光滑解类版本

**类别：**

PDE-SMOOTH

**输入假设与数学结论：**

实际原八变量 PDE、真实 PEC、兼容初值、显式系数条件与足够光滑且加权可微的解 → T21、T27–T29 全部结论

**依赖条目与基础引理：**

T01–T29 中全部必要链条；具体矩形实例化

**现有证据：**

R v0.5.1 给开发目标；目前没有此新 Lean 定理

**未完成接口：**

兑现 Green、Poincaré、时间—空间交换与可积性；逐项登记比 (6.6) 强的假设

**拟建名称及模块（全部计划）：**

`PML.main_smoothRectangle`；`PML/MainSmoothRectangle.lean`

### T31：定理 6.1 的 S2 (6.6) 范围

**类别：**

PDE-V7

**输入假设与数学结论：**

S2 原参数与初值类、已存在的 (6.6) 正则解 → 原样或明确登记差异的 (6.7)–(6.10)，加规范独立性与原辅助变量控制

**依赖条目与基础引理：**

T01–T29；加权 Hilbert/Sobolev 对象、弱梯度／散度、迹、T07

**现有证据：**

S2 §§5–9 纸面主张；R v1.0；S5 说明旧 Lean 未覆盖

**未完成接口：**

真实弱空间接口；T30 的光滑版本不能自行升级；不得残留未证能量律／耗散／Green／Poincaré 假设

**拟建名称及模块（全部计划）：**

`PML.main_V7_apriori`；`PML/MainV7.lean`

关键闭合公式按 S2 原编号明确登记如下，作为日后检查 Lean 定理类型的数学目标：

$$
\underbrace{\mathcal D_7}_{\text{由 (7.7)–(7.8) 定义}}
\ge\mathscr S_0+K\mathscr S_1
+\frac{\mu\tau}{2\kappa}(\Vert P_t\Vert ^2+K\Vert P_{tt}\Vert ^2)
-\mu cA\Vert E\Vert ^2-\mu cAK\Vert E_t\Vert ^2.\qquad\text{S2 (9.1)}
$$

$$
\Vert \nabla E\Vert ^2\le3J(U_1)+3S^2J(U_0).\qquad\text{S2 (9.5)}
$$

$$
\mu cA\Vert E\Vert ^2\le3\mu cAC_P^2[J(U_1)+S^2J(U_0)]
\le\frac K2(\mathscr S_1+S^2\mathscr S_0).\qquad\text{S2 (9.6)}
$$

$$
\mu cAK\Vert E_t\Vert ^2\le\frac{\mu\tau}{4\kappa}
(\Vert P_t\Vert ^2+K\Vert P_{tt}\Vert ^2).\qquad\text{S2 (9.7)}
$$

$$
\mathcal E_7'=-\mathcal D_7,\qquad
\mathcal D_7\ge\frac12(\mathscr S_0+K\mathscr S_1)
+\frac{\mu\tau}{4\kappa}(\Vert P_t\Vert ^2+K\Vert P_{tt}\Vert ^2)\ge0.
\qquad\text{S2 (6.8)}
$$

$$
\forall\,0\le t_1\le t_2\le T,\quad
\mathcal E_7(t_2)+\int_{t_1}^{t_2}\mathcal D_7(t)\,dt=\mathcal E_7(t_1),\quad
\mathcal E_7(t_2)\le\mathcal E_7(t_1).\qquad\text{S2 (6.9)}
$$

$$
\epsilon\Vert E\Vert ^2+\mu(\Vert H_x\Vert ^2+\Vert H_y\Vert ^2)+\kappa^{-1}\Vert P\Vert ^2
\le\frac4\mu\mathcal E_7.\qquad\text{S2 (6.10)}
$$

这里的 $J$ 是 S2 (9.2) 的实际积分：

$$
J(U)=\int_\Omega\sum_{i\in\{x,y\}}
[\theta_i\Lambda_i^2+\theta_j(\partial_i v)^2],\quad j\ne i,
\qquad
\theta_i=\begin{cases}\sigma_i/a,&a>0,\\1/2,&a=0.\end{cases}
$$

不能用一个未解释的非负实数替代 J，然后把 (9.5) 当输入。T23 必须调用 T22 从实际 PDE 得到的梯度关系；T25 才能把这个结果用于吸收。空间耗散与 Debye 耗散各自保留一部分，不能把同一个正项在两处全部用掉。（来源：S2 §9，R v0.3.4–5。）

## 5. 值得保留的非空性、退化和范围检查

以下条目防止后续实现通过收窄模型或扩大结论来“修好”证明。T32–T35 与主线相关，T36–T37 是边界澄清／研究记录，**不因此成为 v0.0.2 的证明任务，也不要求提前开发这些模块**。

### T32：(5.9)、(10.1)–(10.2)

**类别：**

ALG／PDE-SMOOTH 数据证书

**输入假设与数学结论：**

指定单位材料、$(-1,1)^2$、正整数 m≥2 与有理幅度；非零光滑紧支初始场 → 存在满足小量条件且有物理区、四边层、四角层的剖面，并有可容许初值

**依赖条目与基础引理：**

T01、T05、T08–T10；$\pi$ 严格界、正部函数可微／W¹∞、支集与 PEC

**现有证据：**

S2 §§5.2、10；S7 的具体参数同时含精确有理检查和 `float` 比较

**未完成接口：**

全域剖面正则性、初始图层、严格参数证书；数据证书不证明对应解存在

**拟建名称及模块（全部计划）：**

`Examples.fullDomainProfile_admissible`、`Examples.physicalPulse_compatible`；`Examples/FullDomainProfile.lean`、`Examples/CompatibleData.lean`

### T33：命题 2.2（无编号公式）

**类别：**

PDE-SMOOTH 范围反例

**输入假设与数学结论：**

物理区含非空开集；非恒定 $\xi\in C_c^\infty$；允许任意八变量初值 → $H=t\nabla\xi,Q=\mu\nabla\xi$ 是增长解，从而不存在对该整个初值类有限、统一控制 H 且单调的能量

**依赖条目与基础引理：**

T01；混合偏导交换；明确全时段及统一控制常数

**现有证据：**

S2 §2.3 给显式解和纸面反证；S7 未覆盖

**未完成接口：**

具体场解逐方程验证、非零梯度、量词；不能套到兼容类或另加磁约束的类

**拟建名称及模块（全部计划）：**

`PML.unrestrictedData_growthObstruction`；`PML/Obstructions/ArbitraryData.lean`

### T34：§11.1（无编号公式）

**类别：**

ALG／TIME；对已有解的 PDE 条件结论

**输入假设与数学结论：**

指定兼容数据 

$$
u_0=H_0=\phi_0=0,E_0=f,P_0=\kappa f,q_0=-\tau\kappa f
$$

，非零物理区紧支 f → 

$$
\mathcal D_c[U_0](0)=-\mu c(\epsilon+\kappa)\Vert f\Vert ^2<0
$$

；任何经过该数据的正则解，其单层初始导数为正

**依赖条目与基础引理：**

T01、T05、T17；PDE 确定 $P_{t0}=E_{t0}=0$

**现有证据：**

S2 §11.1 纸面初始计算；S7 未直接覆盖此例

**未完成接口：**

导数／端点解释；是否存在这样的正则解另列；只否定此单层候选

**拟建名称及模块（全部计划）：**

`PML.singleLayer_initialGrowth`；`PML/Obstructions/SingleLayer.lean`

### T35：§11.3（无编号公式）

**类别：**

PDE-SMOOTH 退化例

**输入假设与数学结论：**

$r=0$，非零 F(x) 光滑紧支于 p>0 且远离零界面；其余参数仍满足主定理条件 → 原兼容静态解、$\mathcal E_7>0,\mathcal D_7=0$

**依赖条目与基础引理：**

T01、T04–T05、T10–T11、T17–T18；支集上权重可积

**现有证据：**

S2 §11.3 给显式状态；S7 未覆盖

**未完成接口：**

非零 F 与有限加权范数、原方程及边界逐项验证；不加额外磁场约束

**拟建名称及模块（全部计划）：**

`PML.nonzeroCompatibleStaticMode`；`PML/Obstructions/StaticModes.lean`

### T36：(3.1)–(3.4)

**类别：**

可选 TIME／变换分析

**输入假设与数学结论：**

Laplace 变换在声明半平面存在、明确初值／历史与分离系数 → 保留初值项的变换关系及原磁场和拉伸坐标磁场的滤波映射

**依赖条目与基础引理：**

T02–T04；变换存在性、卷积、空间导数与变换交换

**现有证据：**

S2 §3 纸面推导；主定理不依赖本节

**未完成接口：**

所有变换分析均未形式化；一般记忆初值不能套 (3.4)；不据此自动声称反射率为零

**拟建名称及模块（全部计划）：**

`PML.laplaceMapping_withInitialTerms`；`PML/LaplaceMapping.lean`（可选新增模块建议）

### T37：(4.3)–(4.4)、§4.2、(11.1)

**类别：**

历史对照／ABSTRACT；可选具体分析

**输入假设与数学结论：**

V6 能量及正则解 → 梯度余项保留；连续零起点与点态 Schur 充分条件冲突；指定非局部修正完整导数仍有额外项

**依赖条目与基础引理：**

T01–T04、T16；V6 权重、绝对连续／Gronwall、椭圆解算子（依具体子命题）

**现有证据：**

S2 §§4、11.2 纸面论证；S7 只验证 V6 极化行列式；S5 审查旧代理引理范围

**未完成接口：**

真实梯度、算子及全域分析；不把“这一充分条件失效”升级为“所有能量不存在”

**拟建名称及模块（全部计划）：**

`PML.v6_balance_withGradientRemainder`、`PML.schur_zeroStart_obstruction`、`PML.nonlocalCorrection_derivative`；`PML/Obstructions/V6Candidates.lean`（可选新增模块建议）

T35 的非零静态状态按 S2 原式为

$$
u=E=P=q=0,\quad\lambda=\phi=(0,F(x)),\quad
H_x=-F(x)/\mu,\quad H_y=0,\quad Q_x=pF,
$$

其余原辅助变量为零，目标计算为

$$
\mathcal E_7=\frac12\int_\Omega\frac{c}{p(x)}F(x)^2>0,\qquad\mathcal D_7=0,
$$

积分被积式在 F 的支集外可按零解释，不在 p=0 上直接除法。这个例子用于阻止把主定理改写为“所有非零状态都严格递减”。（来源：S2 §11.3。）

## 6. 依赖关系和禁止的循环

主要依赖按逻辑组织如下；定义可以预先声明，证明实施顺序不必与编号顺序相同。

```text
T01 原八变量 + T02 真实提升 + T05 兼容初值
  → T03 五不变量 → T04 双向模型对应 → T06 兼容保持

T08 矩形 Poincaré + T09 小量条件 + T10 分支权重
  → T11 真实加权状态与能量

T04 + T11 + T12 同源时间导数层
  → T13/T14/T15 局部真实求导 + T16 全域 Green/PEC
  → T17 单层平衡 → T18 两层精确导数

T19 约束消元 + T08/T10/T11
  → T20 单层双边界 → T21 两层图范数界 → T29 原状态控制

T22 PDE 梯度关系 → T23 (9.5) → T25 (9.6)
T12 Debye 时间导数 + T09 → T26 (9.7)
T24 (9.1) + T25 + T26 → T27 非负耗散
T18 + T27 + 时间积分接口 → T28 任意两时刻单调性/平衡

兑现矩形具体接口 → T30 光滑兼容类先验定理
兑现 V7 加权弱空间接口及 T07 → T31 V7 范围先验定理
```

- T05 的“兼容”只允许包含初值关系、正则性及可积性；**不能包含 T18、T23、T27、T28 的待证结论**。
- T30/T31 的“解”必须满足 T01 的原 PDE；不能把能量恒等式、耗散非负、目标单调性，或一个与其等价而未证明的吸收条件放进解定义。
- 条件性 T18/T20/T23 等可以公开依赖抽象空间接口。具体 T30/T31 要有该矩形／函数空间的接口证明，不能把未证接口藏进一个名为 `PMLModel` 的结构。
- T07 的提升唯一性不依赖 T28 的时间单调性；它不能被用来宣称 PDE 解唯一性。T32 的初值非空性也不能被用来宣称解存在。
- T33–T35 是不同范围的例子；不能相互替代，不能因反例存在而增加原主定理未声明的磁场约束。

以上限制来自 R §§4–5、v0.3–v0.5，及 S2 定理 6.1 后的范围声明、S3a 核心依赖链。

## 7. 本轮核对结果和仍需核验的事项

已逐项把用户要求的 (2.4)–(2.6)、(5.3)、(6.7)–(6.10)、(7.8)、(9.5)–(9.7) 对应到 T03–T04、T09、T21、T27–T29、T18、T23、T25–T26。额外登记了参数、空间、局部导数、PEC、兼容保持、规范唯一性、显式数据和范围反例，防止主要证明链缺项。

仍待后续数学/API 核验的重点如下；这些是登记的任务，**本轮未执行新证明**：

1. S2 (6.6) 的每一条正则性怎样精确推出 T12/T16/T18 所需导数、迹与积分交换，尤其是导数层的 $E_t$ 零迹、$\lambda_t\in H(\mathrm{div})$ 及奇异权重内积求导。
2. T07 的 Sobolev 切片和零水平集梯度论证，以及 T08 的精确矩形 Poincaré 常数，仍是纸面分析内容。若实现先选更强光滑性或更大常数，必须登记与 V7 的差异。
3. S7 把 p,r 设为 `positive=True`；空间展开中直接出现除以 a。该证据没有覆盖 a=0 的全域分支，也未构造 $L_w^2$。T10/T15/T22 的退化区内容须独立完成。
4. S7 验证 (8.1) 的代数重写，没有验证 (8.3)、(9.5) 或完整空间闭合。不能把历史输出中的成功摘要当作 T21/T27 的形式化证据。
5. S7 示例的 `float` 比较不是严格参数证书；T32 需要精确不等式。S2 给出的解析参数式仍需在未来 Lean 中核验。
6. T33 的否定结论须量化“所有时刻／全时间解”和与时间无关的正控制常数。T34 必须保留“任何经过该数据的足够正则解”的条件，不能补出未证明的存在性。
7. 本轮没有为 T01–T37 创建任何新 Lean 声明；旧代码的范围与历史运行情况保持以 [claim_ledger.md](claim_ledger.md) 为准。

本文件完成的是公式、语义、来源和依赖的清点；三份语义文档的总体验收及 v0.0.2 状态记录见 [scope.md](scope.md)。


## v0.2.4 实现登记（2026-10-11，保留上述计划与历史）

本阶段文件：[SingleLayer.lean](../LeanPML/PML/Obstructions/SingleLayer.lean)。实际构建与审计见 [构建](../logs/v0.2.4/20261011T231924_138774_lake_build.log)、[审计](../logs/v0.2.4/20261011T231954_467990_axioms_audit.log)。说明集中在 [single_layer_failure.md](single_layer_failure.md)。下面记录的是实际覆盖的子结论，未整体关闭 PDE 条目。

| 条目 | 已实现部分 | 仍未完成 |
|---|---|---|
| T34：§11.1 未编号公式 | `LeanPML.PML.Obstructions.initial_compatibility` 核验五项初始数值；`initial_derivative_values` / `hasDerivAt_initial_fields_zero` 分开初始代数与真实导数；`initialDissipation_eq` / `_nonpos` / `_neg` 给点态精确值和符号 | 具体光滑非零紧支撑数据的全场资格、原解存在、PDE 初始端点解释 |
| T34：实际积分子结论 | `LeanPML.PML.Obstructions.initialDissipation_integral` / `initialDissipation_rectangle_integral`：实际测度/全开矩形平方可积与 a.e. 支撑下的等式；`initialDissipation_integral_neg` 明确要求正平方积分 | 从具体非零光滑函数证明正平方积分；完整 PDE 能量积分求导 |
| T34：局部时间子结论 | `LeanPML.PML.Obstructions.hasDerivAt_initial_localEnergy` 从真实局部导数和初值调用三块；`initial_localEnergy_rate_pos` 给导数值严格正性 | 不能据此将计划名 `PML.singleLayer_initialGrowth` 解释为已实现的完整 PDE 定理 |
| T34：第二层控制 | `LeanPML.PML.Obstructions.hasDerivAt_initial_flux`；`secondLayerSpatialInitial_zero` / `_eq` / `_integral`，含独立分量支撑条件 | 实际空间梯度、混合微分交换、梯度支撑、Poincaré 和两层闭合 |
| T02–T04：五不变量接口 | 仅新增上述特殊初始数值检查 | 两个磁不变量的时间保持和原 PDE / primitive 双向对应仍未完成 |
| T13–T18：局部块到单层 | `singleLayerEnergy`、`singleLayerDissipation` 复用三块组合 (6.2)/(7.7)，初始局部真实求导有调用证据 | (7.5) Green、(7.6) 一般空间能量律、(7.8) 两层 PDE 恒等式尚未完成 |

交叉引用核对：§11.1 原文将“精确导数”误指 (7.7)，实际为 (7.6)；(7.7) 是耗散表达式。§11.1 的负耗散式没有编号，§11.2 的 (11.1) 不属本阶段。原文与模型合同未改。


## v0.3.1 追加实现记录：实际空间、合法积分与时间求导（2026-10-13）

本节追加本轮证据，不回写旧条目的计划状态或覆盖历史。新增六个正式模块：
[EnergyCalculus](../LeanPML/Analysis/EnergyCalculus.lean)、[WeightedL2](../LeanPML/Analysis/WeightedL2.lean)、
[SpatialCoefficients](../LeanPML/PML/SpatialCoefficients.lean)、[State](../LeanPML/PML/State.lean)、
[Energy](../LeanPML/PML/Energy.lean)、[EnergyIntegrals](../LeanPML/PML/EnergyIntegrals.lean)。
下表短名在代码中的统一前缀为 `LeanPML.PML`，加权分析结论前缀为 `LeanPML.Analysis`。

| 条目 | 本阶段实际完成 | 输入、依赖及仍未完成的部分 |
|---|---|---|
| T10，(5.5)–(5.6) | 实际 L² 子空间 `WeightedL2`：保存 √wψ 的全域 a.e. 商类；`weightedSubspace_isClosed`、`weighted_completeSpace`、`physicalL2_injective`、`physicalL2_norm_sq_le`、精确加权积分公式 | 实际可测 w，零区为零及正区 w≥1 的条件。PML 通过旧 w≥3/2 推出该下界；无 w 上界。空间系数 a.e. 代表用 `SpatialAbsorption.ofAE_p_ae/ofAE_r_ae` 接通。两种分配权重与后续加权空间估计不得因此整体算完成 |
| T11，(6.1)–(6.5) | `FieldState` 的实际坐标、`PolarConstraint`、单层/两层能量定义及密度可积；`fieldEnergy_eq_integral` 精确对应旧块；`graphSquare/graphSquare7` 是候选平方 | 普通槽属于 L²，加权槽属于上述具体空间；系数由原始非负与幅度条件构造。真实弱梯度/零迹、图范数分离及双边估计仍待实现，不对任意状态安装范数 |
| T12，(6.3)、(6.6) | `StateHasDerivAt`、`SameSourcePath`；`sameSource_coordinates` 和 `sameSource_first_coordinates_of_mem_interior`，从真实路径导数与邻域等式得到两层时间坐标对应 | first.R=P_t、second.R=P_tt 有实际 L² 导数证据；内部条件用于对邻域恒等式求导。尚未由论文完整 Sobolev 正则性推导此接口，也未证明导数层满足同一 primitive 方程 |
| T15，(7.2) | 四个有界耗散系数方向正确；`fieldSpatialDissipation_integrable/eq_integral/nonneg`；`fieldSpatialDissipation_of_zeroAbsorption` 给出全零区 c(‖hₓ‖²+‖hᵧ‖²) 的实际积分 | h=Λ−ψ 是实际 L² 分量，尚需空间接口证明是 ∇v。全域分支未删除零区；未证明 Green/PEC、由辅助演化导出的空间块能量律或一般分区积分定理 |
| T17，(7.6)–(7.7) | `fieldDissipationDensity_integrable`、`fieldDissipation_eq_integral`；`hasDerivAt_fieldEnergy` 与 `hasDerivAt_integral_fieldEnergy` 给出真正空间能量求导 | 输入各实际空间分量（含加权分量）的 HasDerivAt。导数是明确内积表达式，不是 −D_c；primitive 演化与 Green 尚未代入，(7.6) 未完成 |
| T18，(7.8) | `energy7`、`dissipation7` 使用同源路径与同一 `scaleK`；`twoLayerDissipation_eq_integral`；`hasDerivAt_energy7` 为真实和式求导 | 定义与求导表达式已建立；两层同系统、零迹、完整 E₇′=−D₇、D₇≥0 和时间单调性均未完成 |

### 实际假设与接口账本

1. **已构造的空间**：`ScalarL2 ν = Lp ℝ 2 ν`；二维量由两个标量 L² 分量表示，平方和单独写出。加权平方根坐标为 L² 的闭子空间；使用完备性时可写 `letI := weighted_completeSpace ν w hw`。
2. **系数**：`SpatialAbsorption` 存 c>0、p/r 可测非负及 p,r≤S≤c/4。只记录原始条件，所有多项式乘子界、w 下界、零区识别及耗散界均由定理/构造证明。矩形入口 `rectangleMeasure` 使用整个开矩形二维 Lebesgue 限制测度；`separated` 保留 p(x)、r(y)。W¹∞ 的弱空间导数尚未实现。
3. **路径**：`StateHasDerivAt` 在普通/加权空间中分别给出导数。`SameSourcePath` 使用时间集合 I，不把内部条件变成整个实轴条件；只有 t∈interior I 才对层间坐标等式求导。未使用目标能量律作为输入。
4. **空间接口**：`ConditionalSpatialDomain` 仅有受限定义域与两个线性分量算子。`FieldSpatialConstraint` 固定采用真实零延拓映射表达 Λ=空间分量+ψ。尚无具体矩形 H₀¹、弱梯度、H(div)、零迹、Green 或 Poincaré 的实现。
5. **积分**：F_c、S、D_c、D₇ 的密度可积与内积对应均已证明。S 是实际分量积分非负；D_c/D₇ 只定义且可积，不附带非负结论。没有把不可积函数积分的总定义当作合法性依据。
6. **求导**：普通/加权内积规则直接在实际空间上使用，未假设点态导数可与积分交换。`hasDerivAt_integral_fieldEnergy` 是分析链式法则，不是 PDE 能量律。
7. **调用实例**：`SpaceExample.hasDerivAt_energy`、`SpaceExample.energy_nonconstant` 使用单位开矩形实际测度、非零加权 seed 和非恒定路径。实例不声称满足空间约束或完整 PDE。
8. **下一阶段接口**：v0.3.2 应在以上真实空间/路径基础上代入 primitive 演化与明确 Green/零迹条件，证明能量律；不得把最终导数关系放入模型结构。

### 验证与来源

新增 109 条定理进入审计，连同旧 154 条共 263 条。正式构建及独立公理审计均实际通过；最终日志链接见 [README](../README.md) 与 [PROGRESS](../PROGRESS.md)，新增声明完整清单见 [new_theorems.json](../logs/v0.3.1/new_theorems.json)。标准依赖为 propext、Classical.choice、Quot.sound，没有 sorryAx 或自设占位公理。

V7 md/tex/原 PDF、模型合同和锁定配置与上一阶段相同。路线图在进入本轮前只勾选 v0.2.4 四项，v0.3.1–v0.3.3 数学任务没有变化，本轮不改路线图。具体差异及哈希见 [来源核对](../logs/v0.3.1/pdf/source_review.md)。旧 T15/T17 中“积分待完成”等文字保留为历史；只有本表明确列出的积分/求导子结论更新状态，整个 T10/T11/T12/T15/T17/T18 不整体标为完成。


## v0.3.2–v0.3.3 追加记录：实际空间条件定理（2026-10-13）

保留上文各阶段当时的范围，不整体覆盖 T 条目。当前声明均以前缀 `LeanPML.PML` 给出；有界实系数算子辅助结果位于 `LeanPML.Analysis.BoundedCoefficient`。它们操作 v0.3.1 的实际 L²、WeightedL2、FieldState、energy7、graphSquare7、dissipation7，而非任意实数代理。

| 条目／来源 | 本轮实际定理及类别 | 原始输入、依赖与剩余接口 |
|---|---|---|
| T12，(6.3) | `primitiveMain_first_Conditional`、`primitive_first_Conditional`：真实空间时间求导 | 原层在 I 内的 primitive 方程；SameSourcePath 的真实普通/加权导数；显式梯度/散度交换。输出导数层同系统，仅用于 `interior I`。具体正则性推出交换仍待 v0.4.3 |
| T13–T15，(7.1)–(7.4) | `electricRate_add_remainder`、`polarRate_add_remainder`、`spatialRate_add_dissipation`、`fieldEnergyRate_blocks`：实际 L²/加权内积抵消 | 电/极化沿用旧块和已证积分定义；实有界乘子自伴和双线性。空间块经可积加权乘积与 a.e. 演化调用旧点态恒等式。零区由物理恢复映射处理，保留 c‖h‖²；没有除以全域吸收下界 |
| T16，(7.5) | `green_multiplier_Conditional`、`boundary_multiplier_zero_Conditional`：一般 Green 输入的测试/零迹推论 | Green 仍是输入，不是已证明矩形 Green；测试 v、V 在梯度域，Λ 在散度域，迹与边界双配对独立于能量 |
| T17，(7.6)–(7.7) | `hasDerivAt_fieldEnergy_boundary_Conditional`、`hasDerivAt_fieldEnergy_zeroTrace_Conditional`：真实条件性单层空间能量律 | StateHasDerivAt、primitive 主方程和辅助演化、兼容及其求导、空间关系；κ≠0。低层输入的已导关系在最终同源入口由邻域真实求导取得 |
| T18，(7.8) | `hasDerivAt_energy7_Conditional`：真实条件性两层能量恒等式 | 只输入原层系统，先调用 T12 导出 first 系统；原层 u/E 和导数层 E/E_t 零迹均使用。固定 K=scaleK。没有 D₇≥0、时间积分平衡或单调性结论 |
| T19，(8.1)–(8.2) | `polar_energy_bounds_pointwise`、`fieldPolar_bounds`：约束消元后的 Young 及实际积分估计 | 调用旧 `polarEnergy_eq_reduced`、`polar_coefficients_bounds_of_threshold`；原参数阈值推出系数界，兼容从商类转成 a.e. 等式，不直接假设待证界 |
| T20，(8.3)、§8.1–§8.2 | `gradient_square_le_spatialBudget`、`state_norm_sq_le_spatialBudget`、`fieldEnergy_bounds_Conditional` | 空间约束、已证加权嵌入与零区处理；后两者还用零迹 Poincaré。原材料正性、c≤c_* 推出 c²K≤1，得到精确 N²/4≤F_c≤N² |
| T21，(6.7) | `energy7_bounds_Conditional`、`graphSquare_zero_Conditional`、`fieldEnergy_zero_Conditional`、`energy7_zero_Conditional` | 同一参数/系数、同源两层分别满足约束。零能量推出全部受控场坐标为零；未安装完整 Norm 实例，不是任意独立点态分量正定 |
| T29，(6.10)、(8.4)–(8.8) | `physicalControl_Conditional` 的 `PhysicalControlBounds` 七个字段 | 由前述图界及空间控制推出，实际有界乘子重构 Q/Z、实际 L² 磁场缩放，常数逐项保持。原 PDE 双向等价及提升唯一性尚未完成 |

### 本轮空间接口账本（字段是条件，不计为已证分析定理）

| 当前接口 | 数学内容和定义域 | 用途 | 后续具体兑现 |
|---|---|---|---|
| `ConditionalGreenDomain.spatial` | 普通 L² 的子模定义域、两个线性梯度分量 | 主方程乘子、空间约束及(8.3) | v0.4.1 具体矩形梯度及零迹域 |
| `fluxDomain/divergence` | 两个 L² 通量分量组成的受限定义域、线性散度 | primitive 主方程；不要求全 L² 有界 | v0.4.1 H(div) 或光滑通量表示 |
| `trace/boundary/green` | 域上迹、独立边界数据空间及双线性配对；一般 $\langle v,\mathrm{div}\Lambda\rangle=-\langle\nabla v,\Lambda\rangle+\mathrm{boundary}$ | (7.5)→(7.6)；没有定义成能量残差 | v0.4.1–2 四边迹/Green/PEC |
| `ConditionalSpatialPath` 域内匹配 | 域内 v/V、通量路径仅在 I 内匹配同源状态；导数是实际 L² 意义 | 合法选择测试函数及散度域成员 | v0.4.3 从正则性构造 |
| `grad_baseX/Y,grad_firstX/Y,div_base` | 梯度/散度与时间导数的真实 HasDerivAt 交换 | 原层演化求导、导数层空间约束求导 | v0.4.3 |
| 四个 `trace_*` | u、E、E、E_t 零迹 | 两层边界分别为零 | v0.4.3 从提升初值与可微 PEC 证明 |
| `ConditionalPoincare.estimate` | 零迹子域上一般函数平方由梯度平方控制 | (8.3)、交叉项吸收、v 的零分离 | v0.4.2；精确 C_P 仍未证明 |

`ConditionalPoincare.ofGreenTrace` 用同一个迹算子的核建立零迹子域。`stateCoercivityConstraints_of_GreenTrace` 及 base/first 桥接使两个阶段的接口一致；它们没有证明一般矩形 Poincaré。

### 原状态控制的准确解释

`physicalControl_of_graph_bound` 是低层计算引理，可输入已经推得的中间图界；正式入口 `physicalControl_Conditional` 实际调用 `energy7_bounds_Conditional` 和 `state_norm_sq_le_spatialBudget`，没有永久把目标控制式作为输入。

`PhysicalControlBounds.physical` 对应 (6.10)，`displacement/auxiliary` 对应 (8.4)，`primitivePolar` 对应 (8.5)，`electricMemory` 对应 (8.6)，`polarMemory` 对应 (8.7)，`magneticAuxiliary` 对应 (8.8)。q 的重构值另证等于 z；Q_x 用 pφ_y，Q_y 用 −rφ_x。这里只控制给定兼容提升的重构，不关闭 T02–T07/T04 的完整原模型等价链。

### 来源细节与验证

V7 md/tex/原 PDF、模型合同及锁文件字节未变；本轮路线图入场仅有用户已有 v0.3.1 勾选差异。§8.2 最后严格 $<B_{\rm sp}$ 在 B_sp=0 时不成立；代码使用充分的非严格估计，保持原 1/4、1 常数和零状态。详见 [来源复核](../logs/v0.3.3/pdf/source_review.md)。

[v0.3.2 构建](../logs/v0.3.2/20261013T095839_225389_lake_build.log)／[独立审计](../logs/v0.3.2/20261013T100104_046897_axioms_audit.log)；[v0.3.3 构建](../logs/v0.3.3/20261013T100156_159842_lake_build.log)／[独立审计](../logs/v0.3.3/20261013T100321_602582_axioms_audit.log)。四条命令均退出 0。v0.3.2 审计 288 条，v0.3.3 审计 316 条（保留旧 263 条，分别增加 25、28 条）；仅标准基础公理。失败及修复过程保存在对应 logs 目录。

T22–T28 的 (9.5)–(9.7)、完整耗散非负、时间单调及积分平衡仍未实现；本轮止于 v0.3.3。


## v0.3.4–v0.3.5 追加记录：空间估计与条件性主结论闭合（2026-10-13）

本节保留上文的计划和历次状态，按当前实际声明追加 T22–T28 的实现范围。旧段落中“仍未实现”描述的是当时的阶段，不是本轮结论。路线图 v0.3.2–3 的已勾选项目与“当前状态：待实现”文字有出入；本轮没有修改路线图，以源码和实际验证为依据，见 [来源复核](../logs/v0.3.4/source_review.md)。原 V7、模型合同及固定依赖未变。

新增模块为 [GradientControl.lean](../LeanPML/PML/GradientControl.lean)、[DissipationClosure.lean](../LeanPML/PML/DissipationClosure.lean) 和 [MainAbstract.lean](../LeanPML/PML/MainAbstract.lean)。下表全部声明的完整名称以前缀 `LeanPML.PML.` 加所列短名构成；“已实现”指列明接口下的结论，不表示具体矩形接口本身已经证明。阶段构建、公理审计、退出码和完整日志分别登记于 [v0.3.4 验收记录](../logs/v0.3.4/acceptance.json)、[v0.3.5 验收记录](../logs/v0.3.5/acceptance.json)。

| 条目／原文来源 | 本轮实际声明及已证范围 | 输入与调用链 | 尚未关闭的具体 PDE 接口 |
|---|---|---|---|
| T22，(9.2) | `fieldJ` 是实际 L² 有界系数内积定义；`fieldJ_integrable`、`fieldJ_eq_integral`、`fieldJ_nonneg` 分别证明密度可积、积分/内积相等和非负；定义本身不算证明完成 | θ 的可测性、0≤θ≤1、θx+θy=1 来自原分支和旧 `theta_partition`；`SpatialAbsorption.thetaXCoeff/thetaYCoeff` 构造有界乘子，与可能无界的 w 不同 | `spatialComponents_eq_gradient_Conditional` 在空间约束下把 Λ−ψ 接到梯度接口；具体矩形梯度仍待实现 |
| T22，(9.2) 零区及 (9.3) | `fieldJDensity_zero_region` 保留零区梯度平方；`fieldSpatialDissipation_ge_J` 证明实际空间耗散控制 (c−S)J 和 3cJ/4 | 加权物理恢复映射给 ψ=0 a.e. on Z；正区使用系数界，零区独立使用 Λ=h。密度可积后才取积分；没有吸收正下界 | 这是全域 L² 分量积分结论；解释成真实弱梯度需空间约束的矩形实例 |
| T22，(9.4) | `gradient_evolution_Conditional` 从原辅助演化推出两方向 ∂iE=λi,t−σj∂iu+σiλi | 原层 primitive 在时间集合内成立；`SameSourcePath` 的 HasDerivAt 与 `ConditionalSpatialPath` 的梯度交换；调用已证 `primitive_first_Conditional`，不把 (9.4) 预设为主入口条件 | 梯度/时间交换、域内路径的具体空间正则性来源仍是接口 |
| T23，(9.5) | `theta_absorption_square_bounds`、`directional_gradient_control` → `field_gradient_control` → `gradient_control_Conditional`，最终证明实际两方向梯度范数平方 ≤3J(U₁)+3S²J(U₀) | 先证明 θiσj²≤S²θj 和 θiσi²≤S²θi，再分配平方、转成 a.e. 场关系并积分；最终入口自行调用 (9.4)。零区、两个不对称边层及不对称角层均有正式调用 | 不是任意独立分量的点态矩阵估计；仍需给出同源路径和空间接口的具体 PDE 实例 |
| T24，§9.1、(9.1) | `fieldDissipation_lower`、`dissipation7_preliminary_Conditional` 证明真实单层/两层耗散下界，保留两个不同的负项 | 原吸收条件推出 a,b,ac−b≥0，阈值推出 cτ≤1/4；`debye_relations_Conditional` 从邻域兼容的真实求导取得 R+τR_t=κV，而非把 R_t 当普通命名变量 | 同源路径正则性及完整原 PDE 对应尚待具体化；目标耗散下界不在模型字段内 |
| T25，(9.6) 及其后幅度链 | `spatial_absorption_Conditional`、`scale_amplitude_chain`、`spatial_absorption_half_Conditional` | 对 E 使用同一 `G.trace` 零迹核的 Poincaré，再用 (9.3)、(9.5)、K=8μAC_P²；从原阈值证明 KS²≤Kc²/16≤1/16≤1，故 E 负项至多耗用一半空间耗散 | Poincaré 是一般零迹函数估计接口，不是目标 (9.6) 的代名词；精确矩形常数仍未证明 |
| T26，(9.7) | `debye_relations_Conditional`、`debye_absorption_split`、`debye_absorption_Conditional`，证明准确 μτ/(4κ) 系数 | 邻域两次真实兼容求导给 κE_t=P_t+τP_tt；两个材料阈值分别控制 P_t、P_tt 项。κ、τ 正性来自原材料参数，不新增教学 Debye 方程 | P_t=first.R、P_tt=second.R 由真实 L² 导数绑定；具体 PDE 正则性推出该路径尚待完成 |
| T27，(9.7) 后未编号下界、(6.8) | `dissipation7_lower_Conditional`、`dissipation7_nonneg_Conditional`；`energy7_law_and_closure_Conditional` 将真实能量导数和定量下界并列输出 | 同时使用 (9.1)、(9.6)、(9.7)，保留一半空间耗散及 μτ/(4κ) Debye 平方项；非负性从剩余项推出。实际 D₇ 不是任意实数代理 | 定量下界与导数声明作用于开时间区间；具体矩形分析和原模型实现仍未完成 |
| T28，(6.9) | `continuousOn_energy7`、`energy7_antitoneOn_Conditional`、`energy7_initial_bounds_Conditional`；`energy7_integral_balance_Conditional` 单独证明实际 intervalIntegral 平衡 | 闭区间普通/加权场连续推出能量连续；内部真实导数与已证耗散符号推出 AntitoneOn。积分平衡另由 `continuousOn_dissipation7`、`intervalIntegrable_dissipation7_Conditional` 和 mathlib FTC 推出 | 积分平衡额外要求 second.R=P_tt 在闭区间 L² 连续；不要求端点双侧导数，不从单调性直接推积分恒等式 |
| T21、T29 与 T28 的连接 | `graphSquare7_initial_bound_Conditional`、`physicalControl_initial_Conditional`、`main_energy_estimate_Conditional` | 调用上一阶段 (6.7)、(6.10)、(8.4)–(8.8)，再把右端 E₇(t) 降到 E₇(0)；所有重构乘数的非负性已证明 | 给定兼容提升的先验控制，不是原八变量 PDE 双向等价、提升唯一性或解存在唯一性 |

### 最终输入包及假设审查

`#print axioms` 不会把普通结构字段列成未完成分析接口。以下是对 `FiniteIntervalProblemConditional` 及最终 `main_energy_estimate_Conditional` 的单独语义审查：

| 输入 | 准确数学内容 | 为什么需要／没有包含什么目标 |
|---|---|---|
| `SpatialAbsorption`、`CoercivityParameters` | 时间不变可测吸收、非负、p,r≤S≤c/4；材料和 C_P 为正，c>0、c≤c_* | 从原条件推导全部系数界与两类吸收，不输入 (9.5)–(9.7)、D₇≥0 或能量单调性。一般测度空间引理不改变物理模型 p=p(x)、r=r(y) 的合同 |
| `Nonempty α` | 空间载体非空；ℝ×ℝ 自动满足 | 取一点由 0≤p≤S 证明 S≥0，使幅度平方链合法；不要求测度非零、积分域缩小或吸收严格为正 |
| `ConditionalGreenDomain`、同一迹的 `estimate` | 受限梯度/散度定义域、独立迹与边界配对、一般 Green；对 G.trace f=0 的一般函数给 Poincaré | 沿用前阶段诚实接口；Poincaré 与能量律使用同一迹核。字段不含能量律残差、图范数界或耗散闭合 |
| `path`、`regular`、`base_evolution` | `SameSourcePath` 的时间集合为 (0,T)；真实普通/加权 HasDerivAt、域内匹配、时间—空间交换；只输入原层 primitive 演化 | 导数层同系统、(9.4)、Debye 派生关系、能量律均由定理推出；没有全实轴方程或端点双侧导数条件 |
| `continuous_base/first` | 实际普通/加权状态各坐标在 [0,T] 连续 | 从坐标连续证明能量连续，不能以目标 energy7 连续性代替 |
| `static_base/first` | 闭区间上明确的极化、空间及同一迹核零迹约束 | 供包括端点的静态能量非负、双边界和重构使用；T=0 时仍须输入，不能从空内部方程推端点兼容。这些字段不含任何目标能量不等式 |
| `hsecondR`（主汇总/积分平衡另加） | second.R=P_tt 在 [0,T] 的 L² 连续性；在 (0,T) 内已有真实导数证据 | 推出 D₇ 连续和 IntervalIntegrable。单调性定理不使用此附加条件；它不是把耗散可积性或积分平衡直接收作模型字段 |

时间范围分开登记：真实能量导数、(9.5)–(9.7) 的同源估计及耗散定量下界在 **(0,T)** 使用内部演化；静态图范数界、非负性、单调性和初值控制在 **[0,T]** 成立。积分平衡对 $0\le t_1\le t_2\le T$ 成立，包括 $t_1=t_2$、两个端点和 $T=0$。`energy7_antitoneOn_zero_time`、`energy7_integral_balance_same` 分别正式处理单点性质；不能据此把 T=0 的任意端点耗散认定为非负。

剩余耗散的精确预算为

$$
\mathcal D_7\ge\frac12(\mathscr S_0+K\mathscr S_1)
+\frac{\mu\tau}{4\kappa}\bigl(\|P_t\|^2+K\|P_{tt}\|^2\bigr)\ge0.
$$

空间预算支付 $\mu cA\|E\|^2$，Debye 预算支付 $\mu cAK\|E_t\|^2$；没有把同一份正项重复使用。由真实 $\mathcal E_7'=-\mathcal D_7$ 推出导数非正，再由区间单调性引理得到单调不增。FTC 独立得到

$$
\mathcal E_7(t_2)+\int_{t_1}^{t_2}\mathcal D_7(t)\,dt=\mathcal E_7(t_1).
$$

### 后续范围

T22–T28 的上述 **Conditional 实际空间版本** 已有完整证明链；具体 PDE 层不随之整体关闭。仍缺：具体矩形梯度、散度和四边迹；Green/PEC 的矩形证明；精确 Poincaré 常数；从具体正则性推出时间微分交换及两层零迹；原八变量与 primitive 的完整双向对应；提升规范唯一性。没有证明解存在、唯一性、严格衰减、任意吸收幅度结论或全局解存在。

下一阶段仅登记 v0.4.1 的入口：明确矩形上的光滑函数/场、坐标方向导数、四边边界表示及零迹域，逐步实例化现有分析接口。本轮没有实施 v0.4。PDF 的各公式限定标记见 [标注账本](pdf_formalization_marks.md)；定义录入与已证结论分别登记。


## v0.4 增量：具体光滑矩形与原系统接口（保留上述历史）

本次四阶段分别通过实际完整构建、公理审计与最终假设检查。证据按 [v0.4.1](../logs/v0.4.1/acceptance.json)、[v0.4.2](../logs/v0.4.2/acceptance.json)、[v0.4.3](../logs/v0.4.3/acceptance.json)、[v0.4.4](../logs/v0.4.4/acceptance.json) 保存；准确命令、目录、退出码和完整输出均在所链接日志。没有将旧“待实现”文字直接当作当前状态，也没有覆盖历史。

| 原条目/公式 | 当前新增实际证据 | 范围与剩余部分 |
|---|---|---|
| T01；(1.1)、(2.1)–(2.2) | `Concrete.OriginalAt/OriginalOn` 建模全部八式，真实 HasDerivAt 和 fderiv；`OriginalRectPEC` 全四边 PEC | 定义不是无条件证明；选定光滑表示保证导数对象的分析解释。归一化 ε=ε₀ε∞、κ=ε₀(ε_s−ε∞)、μ=μ₀μ_r，p=σ_x/ε₀、r=σ_y/ε₀，Z/Q 不另外缩放 |
| T02；(2.3) | `Concrete.integralLift_initial/hasDerivAt_integralLift`；`Rectangle.toL2_integralLift_on_Icc` | 实际历史积分与 L² Bochner 积分连接；u₀/q₀任意固定初始原函数，不默认零 |
| T03；(2.4) | `Concrete.five_invariants_on_Icc`、`five_invariants_toLp_eq_of_continuous` | 全部五个真实时间不变量，包括两个磁辅助量；任意初始常数场可随空间变化。不是仅点态代数，也不等于原变量全零 |
| T04；(2.5)、(2.6)、命题2.1 | `Concrete.original_to_primitive_rectangle`、`primitive_to_original_rectangle`、`reconstruct_lift_eqOn`、`lift_reconstruct_eqOn` | 初始零兼容后双向恢复全部八式及 PEC；固定 u₀/q₀，正则性显式。primitive 回环的空间梯度识别在内部；非零不变量附加源项系统未实现 |
| T05；§5.2 零区 | `Concrete.original_zero_region_preserved`、`original_smoothZeroOn`、`original_static_closed` | 原场 φ₀=0 与原演化推出全区间保持，再内部求导得到加权三层零值；T=0 的首层初始图条件单列 |
| T08；(5.1) | `Rectangle.poincare_estimate/poincareDomain`、`scaleK_rectangle`、`threshold_rectangle_pos` | **保守版** CP=2Lx；K=32μ(ε+2κ)Lx²，c_*同步该值。未证明原精确 π 常数，不登记原式完整完成 |
| T10、T12；(5.5)–(5.6)、(6.3)/(6.6) | `Rectangle.hasDerivAt_weighted_smooth`、`hasDerivAt_jet_gradientX/Y`、`hasDerivAt_jet_divergence`、`smoothSpatialPath` | 真实函数↔普通/加权L²及混合交换；统一和加权正则性仍是输入。(5.7)/(5.8)自动传播未证 |
| T16；(7.5) | `Rectangle.green_L2/greenDomain`、`boundary_multiplier_zero`、`twoLayer_zeroBoundary` | 已证明具体光滑矩形四边 Green，域/迹良定义并线性；两层 PEC 消去来自真实求导。不是一般弱 Green，T=0闭端点E_t迹须额外初始迹条件 |
| T11、T17–T29 的具体接口 | `Concrete.originalFiniteIntervalProblem_separated`、`originalFiniteIntervalProblem_second_R_continuous` | 从原八式、初始兼容、实际历史识别、PEC、强正则性产生旧有限区间问题；Green、Poincaré、交换、全时段静态/零区不再外传为目标假设。既有能量结论未在本轮另行发布为v0.5主定理 |
| T30–T31、T06–T07 | 暂不升级为完整完成 | v0.5.1最终具体先验定理发布、弱空间完整范围、加权传播、提升规范唯一性仍各有边界 |

表中 `Concrete.*` 完整前缀为 `LeanPML.PML.Concrete.`，`Rectangle.*` 为 `LeanPML.Rectangle.`。代码位于 [Rectangle](../LeanPML/Rectangle) 和 [OriginalAssembly](../LeanPML/PML/OriginalAssembly.lean) 导入链；逐项哈希与实际声明名见最终验收/源码。

最高入口的输入审查另见 [独立语义记录](../logs/v0.4.4/semantic_review_geometry.md)。`SmoothZeroOn`、`SmoothStaticAt` 是中间桥接需要的结论包，最终入口由原方程证明填入；不可只看结构名字或 #print axioms 就视其为已证。`SmoothStateRegular` 只给真实成员资格、连续性与可微性。光滑延拓和 C(K) 条件比完整 V7 弱范围强，且不要求延拓域外满足 PDE。
