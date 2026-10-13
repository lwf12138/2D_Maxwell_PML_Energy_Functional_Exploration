# 原模型与主定理语义合同

用途：先固定“Lean 最终应当证明哪一个数学命题”，再安排代码实现。本文件集中说明变量、方程、假设、能量和结论；它是 v0.0.2 的规格文档，不是新的证明，也不是已通过 Lean 检查的定理。

核对日期：2026-10-06（Asia/Shanghai）。定理与模块的计划见 [theorem_inventory.md](theorem_inventory.md)，覆盖范围、疑点、版本差异和阶段验收见 [scope.md](scope.md)。

## 1. 来源、状态与统一约定

来源编号继承 [source_inventory.md](source_inventory.md)，历史证据继承 [claim_ledger.md](claim_ledger.md)：

- **S1**：[原问题](../../sources/energy_functional_problem.tex)，尤其 `eq:main-model`、PEC 和 `alpha=1` 说明。
- **S2**：[V7 正文](../../results/V7_Maxwell_Debye_PML/V7_global_energy.md)，尤其 §§1–2、5–9 和定理 6.1。
- **S3a**：[V7 证明自审](../../results/V7_Maxwell_Debye_PML/proof_audit.md)，用于核对假设用途，不当作独立证明。
- **S3b**：[V7 README](../../results/V7_Maxwell_Debye_PML/README.md)，用于核对交付边界。
- **S4、S5**：清单中的 V6 数学完整性审查、旧 Lean 覆盖审查；它们说明历史缺口，不替代 V7 证明。
- **R**：[当前路线图](../ROADMAP_lean_PML_revised.md) §§4–5、v0.0.2。R 的哈希已与 v0.0.1 快照不同；本轮重读当前版本，差异记录见 scope §2。S1、S2、S3a 等数学来源哈希未变。

下文“拟证明”“应推出”都表示开发目标。S2 中已有纸面推导，不表示本轮重证，更不表示已有 Lean 实现。公式号如 **V7 (6.7)** 专指 S2；本文件不另造相同编号。

所有场取实值。空间积分使用整个矩形上的 Lebesgue 测度；无下标的范数为 $L^2(\Omega)$ 范数，向量范数对两个分量求和。空间等式、零集和系数界按几乎处处意义理解；边界条件用迹解释。光滑实现可使用相应经典对象，但须证明与所用接口对应。[S2 §§1、5–7；R v0.4、v1.0]

## 2. 几何、变量与归一化

令

$$
\Omega=(x_-,x_+)\times(y_-,y_+),\qquad
x_-<x_+,\quad y_-<y_+,\quad
L_x=x_+-x_-,\quad L_y=y_+-y_->0.
$$

其中 $L_x>0$。这是**整个截断计算域**，包含物理区、PML 边层和角层；不将积分域缩为某一个正吸收角区。可指定内部物理矩形 $\Omega_{\rm phys}=I_{x,\rm phys}\times I_{y,\rm phys}$，使 $p$ 在 $I_{x,\rm phys}$ 上为零、$r$ 在 $I_{y,\rm phys}$ 上为零。V7 允许退化的单轴吸收乃至全零吸收；代表性的双轴例子另见 V7 (10.2)。不把“每个边层/角层必须非空”增加为一般定理假设。[S1 Primary Goal；S2 §§1、10、11.3]

| 符号 | 含义与类型 | 来源 |
|---|---|---|
| $E=E_z$ | 二维 TM 模型的电场标量，依赖 $(t,x,y)$ | S1 Model to Analyze；S2 (2.1) |
| $H_x,H_y$ | 原模型的两个磁场分量；不是未经映射的坐标拉伸磁场 | S1；S2 (2.1)、(3.3) |
| $P$ | Debye 极化变量，保留在模型和能量中 | S1 的 $\alpha=1$ 说明；S2 (2.1) |
| $Z_1=P_{z,1},Z_2=P_{z,2}$ | 两个电辅助变量 | S2 §2.1 |
| $Q_x,Q_y$ | 两个磁辅助变量 | S1；S2 (2.1) |
| $\epsilon_0,\epsilon_\infty,\epsilon_s,\mu,\tau$ | 正的材料常数，且 $\epsilon_s>\epsilon_\infty$；$\mu=\mu_0\mu_r$ | S1；S2 (1.1) |
| $\epsilon=\epsilon_0\epsilon_\infty>0$ | 归一化记号下的瞬时介电系数 | S2 (1.1) |
| $\kappa=\chi=\epsilon_0(\epsilon_s-\epsilon_\infty)>0$ | 极化耦合强度 | S2 (1.1) |
| $p(x)=\sigma_x^{\rm old}(x)/\epsilon_0$、$r(y)=\sigma_y^{\rm old}(y)/\epsilon_0$ | 本合同实际使用的吸收系数；保留旧电导率与新系数的量纲区别 | S2 (1.1) |
| $\sigma_x=p,\sigma_y=r$ | V7 分量公式中的简记；下标 $i,j$ 表示不同坐标方向 | S2 §§1、7、9 |
| $a=p+r,\ b=pr$ | 非负、时间不变的空间函数 | S2 §1 |
| $Z=\{a=0\},\ \Omega_+=\{a>0\}$ | 零吸收区与正吸收集合；$Z$ 不等于电辅助变量 $Z_1,Z_2$ | S2 §1 |

归一化只改写系数记号，不缩放这八个未知量。例如 $\epsilon b=(\epsilon_\infty/\epsilon_0)\sigma_x^{\rm old}\sigma_y^{\rm old}$，与 S1 的 $Z_1$ 方程系数对应。[S1 `eq:main-model`；S2 (1.1)、(2.1)]

## 3. 必须保留的八变量方程与边界

以下是最终具体 PDE 定理的方程输入，逐式对应 **V7 (2.1)**：

$$
\begin{aligned}
\epsilon E_t&=\partial_xH_y-\partial_yH_x-\epsilon aE-P_t-aP+Z_1+Z_2,\\
\mu H_{x,t}&=-\partial_yE-\mu(r-p)H_x+Q_x,\\
\mu H_{y,t}&=\partial_xE-\mu(p-r)H_y+Q_y,\\
\tau P_t+P&=\kappa E,\\
Z_{1,t}&=-\epsilon bE,\\
Z_{2,t}&=-bP,\\
Q_{x,t}&=-pQ_x+\mu p(r-p)H_x,\\
Q_{y,t}&=-rQ_y+\mu r(p-r)H_y.
\end{aligned}
$$

极化律取 $\alpha=1$，仍为 $P+\tau P_t=\kappa E$；不能删除 $P$，也不能以 $\kappa=0$ 代替当前模型。[S1；S2 §§2.1、13]

整个外边界采用 **V7 (2.2)**：

$$
E(t)|_{\partial\Omega}=0.
$$

最终原系统解的定义只包含实际场、必要的导数意义、八条方程与 PEC。初值兼容及正则性可作为分列的条件，但不得包含能量恒等式、耗散非负、(9.5) 或目标单调性。$u$ 与 $E_t$ 的零迹要通过提升初值和时间正则性得到，不给每个内部子区额外强加非正通量。[R v0.0.2、v0.4；S2 §7.3]

**磁场约束声明：** 不额外假设整个域上 $\partial_xH_x+\partial_yH_y=0$ 或 $H\cdot n=0$。下文兼容类本身有实质限制，尤其在 $Z$ 上要求 $\lambda_0=\nabla u_0$；这不应被隐去，也不应擅自换成另一个散度约束类。[S2 定义 5.1、命题 2.2；R v0.0.2]

## 4. 系数、小量条件和权重

### 4.1 原始系数条件

$p\in W^{1,\infty}((x_-,x_+))$、$r\in W^{1,\infty}((y_-,y_+))$，延拓到矩形后分别只依赖 $x$、$y$；它们非负且不依赖时间，满足上一节物理区的零吸收约定。采用相应 Lipschitz 代表时可描述从内界面连续起步的剖面。**没有吸收正下界，没有吸收梯度小量条件。** $W^{1,\infty}$ 的有界导数要求与“梯度必须足够小”不是一回事。[S2 §§1、10；S3a 假设表]

### 4.2 固定常数与显式幅度条件

按 **V7 (5.1)–(5.3)** 固定

$$
C_P^2=\left(\frac{\pi^2}{L_x^2}+\frac{\pi^2}{L_y^2}\right)^{-1},\quad
A=\epsilon+2\kappa,\quad K=8\mu A C_P^2,
$$

$$
c_* =\min\left\{K^{-1/2},\frac{\kappa\tau}{8AK},\frac{\kappa}{8A\tau}\right\},\quad
0<c\le c_*,\quad
S=\max\{\Vert p\Vert _{L^\infty},\Vert r\Vert _{L^\infty}\}\le c/4.
$$

$A$ 是材料标量，不是矩阵；$c,K$ 是时间无关的常数。选择可在求解之前完成，不依赖未来解；允许依据幅度选择满足条件的 $c$，也可以按 S2 固定 $c=c_*$。在正参数前提下，拟在 Lean 证明上述条件与下列小量不等式的对应关系，而不是本轮新增证明：[S2 (5.2)–(5.3)；R v0.2.1]

$$
c>0,\quad c^2K\le1,\quad
8cAK\le\kappa\tau,\quad
8cA\tau\le\kappa,\quad 0\le p,r\le S\le c/4.
$$

以下是应当推出的系数结论，不是额外的剖面假设：

$$
a\le c/2,\quad b\le c^2/16,\quad ac-b\ge0,\quad
c\tau\le\frac{\kappa}{8A}<\frac1{16},\quad KS^2\le1/16.
$$

[S2 (5.4)、(9.6) 后的估计]

其中具体矩形 Poincaré 不等式 $\Vert v\Vert ^2\le C_P^2\Vert \nabla v\Vert ^2$ 是待证明的分析结论。v0.3 可使用显式接口，最终具体 PDE 定理必须兑现它。若先实现了较保守常数，须重算 $K,c_*$ 并登记定理范围差异，不能声称仍覆盖这里的精确参数范围。[S2 (5.1)；R v0.4.2]

### 4.3 退化权重与状态空间

按 **V7 (5.5)–(5.6)**：

$$
w_x=\frac{c-r}{a},\quad w_y=\frac{c-p}{a}\quad\text{在 }\Omega_+;
\qquad w_x=w_y=0\quad\text{在 }Z,
$$

$$
L_w^2=\left\{\psi:\Omega\to\mathbb R^2\text{ 可测},\quad
\psi=0\text{ a.e. 于 }Z,\quad
\Vert \psi\Vert _w^2:=\int_{\Omega_+}(w_x\psi_x^2+w_y\psi_y^2)<\infty\right\}/\!\sim,
$$

其中 $\psi\sim\widetilde\psi$ 指两者在整个 $\Omega$ 上按 Lebesgue 测度几乎处处相等，且均满足 $Z$ 上零延拓条件；这是对 S2 Hilbert 空间记号的类型澄清，实际空间、等价类、内积和完备性的构造仍待形式化。若使用加权测度的 $L^2$，必须明确零权重集合 $Z$ 上的零延拓代表和到普通 $L^2$ 的映射，不能任意读取等价类在 $Z$ 上的值。[S2 (5.6)；R v1.0.1]

在 $\Omega_+$ 上应证明 $w_i\ge3/2$；结合 $\psi=0$ 于 $Z$ 得到 $L_w^2\hookrightarrow L^2(\Omega)^2$。不把 $w_i\ge1$ 写成在 $Z$ 上也成立，不把可能无界的 $w_i$ 当作普通 $L^2$ 的有界乘子。$p=r=0$、只有一个正吸收、两个均正三种情形都必须保留。[S2 §§5.1、7.1]

## 5. 提升、五个不变量与兼容初值

### 5.1 提升的定义和应推导的关系

选取初始原函数 $u_0,q_0$，按 **V7 (2.3)** 定义

$$
u(t)=u_0+\int_0^tE(s)\,ds,\quad
q(t)=q_0+\int_0^tP(s)\,ds,\quad
\lambda=(\mu H_y,-\mu H_x),\quad \phi=\lambda-\nabla u.
$$

$\lambda_x=\mu H_y$、$\lambda_y=-\mu H_x$ 中的 $x,y$ 是向量分量下标；$\partial_x\lambda$ 才表示导数。$u,q$ 包含过去历史和已固定初值，不能默认 $u_0=q_0=0$。[S2 §§2.2、3]

要从真实导数与八变量方程证明 **V7 (2.4)** 的五个量在时间上恒定：

$$
C_D=q+\tau P-\kappa u,\quad
C_{z1}=Z_1+\epsilon bu,\quad C_{z2}=Z_2+bq,
\quad C_x=Q_x-p\phi_y,\quad C_y=Q_y+r\phi_x.
$$

这里每个 $C$ 可以是空间函数，“恒定”指 $C(t)=C(0)$，不表示空间常数。尤其磁辅助项需要时间微分与空间梯度交换，不能只靠给代数变量命名为 `Pt` 或 `gradE`。[S2 (2.4) 及其推导；S5]

### 5.2 初始兼容类是输入，演化保持是结论

按 **V7 定义 5.1**，给定原八变量初值，要求存在 $u_0\in H_0^1(\Omega)$，使

$$
q_0=\kappa u_0-\tau P_0,\quad
\lambda_0=(\mu H_{y0},-\mu H_{x0}),\quad
\phi_0=\lambda_0-\nabla u_0\in L_w^2,
$$

并满足四个初值关系

$$
Z_{1,0}=-\epsilon bu_0,\quad Z_{2,0}=-bq_0,\quad
Q_{x,0}=p\phi_{y,0},\quad Q_{y,0}=-r\phi_{x,0}.
$$

这使五个 $C(0)$ 为零。再由不变量保持得到全时间重构 **V7 (2.5)** 和 $q+\tau P=\kappa u$。$\phi_0\in L_w^2$ 包含 $\phi_0=0$ 于 $Z$；其保持和加权可积性保持分别是辅助演化与 **V7 (5.7)–(5.8)** 的证明任务，不是对每一时刻重新输入兼容关系。[S2 §§2.2、5.2]

主定理还要求由 PDE 生成的一阶时间初始图状态有限，并满足相应 PEC 迹相容。例如

$$
P_{t0}=(\kappa E_0-P_0)/\tau,\qquad
\phi_{i,t0}=\sigma_j\partial_i u_0-\sigma_i\lambda_{i0}\quad(j\ne i),
$$

$E_{t0}$ 按原电场方程计算，$\lambda_{t0}$ 按原磁场方程及提升关系计算。它们不是独立可选的初值。下文 (6.6) 的正则解语义应使这些取值及零迹有意义；不能用任意有限实数代替导数初值。[S2 定义 5.1、(6.3)、(6.5)–(6.6)]

### 5.3 primitive 系统是需要证明的等价中间模型

由原方程和零不变量应当推出 **V7 (2.6)**：

$$
\begin{aligned}
\mu[\epsilon(u_{tt}+au_t+bu)+P_t+aP+bq]&=\operatorname{div}\lambda,\\
\phi_{x,t}+p\phi_x&=(r-p)\partial_xu,\\
\phi_{y,t}+r\phi_y&=(p-r)\partial_yu,\\
\lambda&=\nabla u+\phi,\\
q_t=P,\quad q+\tau P&=\kappa u,\quad u_t=E.
\end{aligned}
$$

还需反向验证：给定足够正则的上述提升解，使用 $E=u_t$、$H_y=\lambda_x/\mu$、$H_x=-\lambda_y/\mu$ 和 (2.5)，恢复全部八条方程。该反向结果的 PEC 仍需 $u_t$ 的零迹。[S2 命题 2.1；R v0.4.4]

S2 定理 6.1 同时写有“原八变量解”及“并满足 (2.6)”。本合同的最终原系统版本将后者安排为**已证明的中间结论**；允许独立建立 primitive 条件定理，但其名称和输入必须明确，不能用它代替原系统等价证明。[S2 §§2.2、6；R §§4–5]

非零 $C_{z1},C_{z2}$ 会在 primitive 主方程右端引入 $\mu(C_{z1}+C_{z2})$，非零磁不变量引入 $(C_y,-C_x)$，非零 $C_D$ 改变极化约束。这些情形不在本轮固定的无源主定理中。[S2 命题 2.1 后说明]

提升规范唯一性是单独的待证结论：同一原状态的两个兼容提升应相同。所需切片、零迹及零水平集弱梯度事实来自 S2 §5.3 的纸面论证，尚待兑现；不能把“唯一提升存在”偷偷放进原解定义。[S2 §5.3；R v1.0.2]

## 6. 时间、正则性与假设用途总表

固定任意有限 $T\ge0$。本合同采用 **V7 (6.6)** 的充分正则性作为完整目标：

$$
\begin{aligned}
u&\in C^2([0,T];H_0^1(\Omega))\cap C^3([0,T];L^2(\Omega)),\\
P&\in C^2([0,T];L^2(\Omega)),\\
\phi&\in C^2([0,T];L_w^2),\\
\lambda&\in C^1([0,T];H(\operatorname{div};\Omega)).
\end{aligned}
$$

这里 $H(\operatorname{div};\Omega)=\{\Lambda\in L^2(\Omega)^2:\operatorname{div}\Lambda\in L^2(\Omega)\}$，导数按弱导数理解；$H_0^1$ 包含零边界迹。$q$ 先按时间积分定义，其 $q=\kappa u-\tau P$ 由兼容保持得到。正则性不是能量律或稳定性的别名。[S2 (6.6)、§7.3；R v1.0]

区间导数采用：内部 $t\in(0,T)$ 为通常时间导数；若表述端点导数，则须采用已说明的单侧/区间导数约定。连续性与积分结论覆盖闭区间，$T=0$ 时任意两时刻只能相等。具体 Lean 的闭区间 $C^k$、迹和导数 API 留待建模，不预先假设整条实轴上存在解。[R v0.1.1；S2 (6.6)、(6.9)；端点明确化属本合同规格约定]

| 编号 | 输入条件与数学含义 | 来源 | 证明中的用途 |
|---|---|---|---|
| H01 | 有限非退化矩形、实值场、有限 $T\ge0$；全域空间积分 | S1；S2 §1 | 定义状态和边界；具体 Poincaré 常数；闭区间时间结论 |
| H02 | 常正材料 $\epsilon,\mu,\kappa,\tau$，$\alpha=1$；保留归一化来源 | S1；S2 (1.1)、(2.1) | 正能量系数、Debye 耗散、除法合法与 (9.7)；不允许直接取 $\kappa=0$ |
| H03 | 非负、时间不变、分离的 $W^{1,\infty}$ 吸收，保留零区 | S2 §1；S3a | 系数界、时间不变量、导数层同系统；分离性另用于规范唯一性和坐标拉伸说明；不声称每个局部能量式都使用分离性 |
| H04 | $C_P,A,K,c_*,c,S$ 按 §4 定义并满足小量条件 | S2 (5.1)–(5.4) | 权重正性；$c^2K\le1$ 控制正定性交叉项；$KS^2\le1$ 用于 (9.6)；两条材料条件用于 (9.7) |
| H05 | 实际原八变量路径满足 §3 八条方程，导数是真实导数 | S1；S2 (2.1) | 推导不变量、primitive 映射、局部求导及 (9.4) |
| H06 | 整个外边界 $E=0$ 的 PEC 迹 | S2 (2.2)；§7.3 | 与 $u_0$ 零迹及正则性一起导出 $u,E,E_t$ 零迹，消去两层边界项 |
| H07 | 定义 5.1 的初值提升见 §5.2：$u_0\in H_0^1$、四重构、$\phi_0\in L_w^2$ | S2 §5.2 | 初始五不变量为零、排除静态源项；零吸收区辅助变量为零；保证初始加权项可定义 |
| H08 | PDE 生成的初始一阶时间图状态有限、相应 PEC 迹相容 | S2 定义 5.1、(6.5) | 两层能量初值有限；不能将导数状态任意独立指定；与 H09 的取值关系须形式化 |
| H09 | 提升路径具有上述 (6.6) 充分正则性 | S2 (6.6)；S3a | 内积/积分求导、空间弱导数、时间—空间交换、PEC 时间微分与两层 Green 合法；不是适定性结论 |

H08 与 H09 可能在具体实现中存在可证明的蕴含关系，不能简单删除其中的原始初值要求而改变定理入口。应在后续给出显式连接引理。[S2 定义 5.1、定理 6.1；本合同接口安排]

## 7. 两层能量、图状态和显式耗散

### 7.1 状态和能量

对路径 $U=(v,R,z,\psi)$，记 $\Lambda=\nabla v+\psi$，满足 **V7 (6.1)** 的 $z_t=R$、$z+\tau R=\kappa v$。范数和能量还用到真实的 $v_t$，因此形式化时应使用“路径在 $t$ 的值及导数”或包含 $v_t$ 的受约束图状态；不能声称任意瞬时四元组就唯一确定 $N$。[S2 (6.1)、(6.5)；R v0.3.1]

单层能量按 **V7 (6.2)** 原式定义：

$$
\begin{aligned}
\mathcal F_c[U]=\frac12\int_\Omega\Big\{&
\mu\epsilon[v_t^2+2cvv_t+(b+ac)v^2]
+|\Lambda|^2+w_x\psi_x^2+w_y\psi_y^2\\
&+\frac\mu\kappa[(1+(a+c)\tau)R^2+2(c+b\tau)Rz
+(ac+b(1+c\tau))z^2]\Big\}\,dx\,dy.
\end{aligned}
$$

两层来自同一个解，按 **V7 (6.3)–(6.4)**：

$$
U_0=(u,P,q,\phi),\quad U_1=(E,P_t,P,\phi_t),\quad
\Lambda_0=\lambda,\quad\Lambda_1=\lambda_t,
$$

$$
\boxed{\mathcal E_7(t)=\mathcal F_c[U_0(t)]+K\mathcal F_c[U_1(t)].}
$$

两层满足相同 primitive 型系统、$U_1$ 确为导数层，均应由方程与时间不变系数推出。不能为获得符号估计而把两层当成互相独立的数据。[S2 §§6、7；R v0.3.2]

### 7.2 被控制的图范数

按 **V7 (6.5)**：

$$
N(U)^2=\mu\epsilon\Vert v_t\Vert ^2+\frac\mu\kappa\Vert R\Vert ^2
+\Vert \Lambda\Vert ^2+\Vert \psi\Vert _w^2,
\qquad \mathcal N_7^2=N(U_0)^2+KN(U_1)^2.
$$

约束包括 $v\in H_0^1$、$\psi\in L_w^2$、$v_t,R\in L^2$、$z=\kappa v-\tau R$ 和 $\Lambda=\nabla v+\psi$。具体展开为

$$
\mathcal N_7^2=\mu\epsilon(\Vert E\Vert ^2+K\Vert E_t\Vert ^2)
+\frac\mu\kappa(\Vert P\Vert ^2+K\Vert P_t\Vert ^2)
+\Vert \lambda\Vert ^2+K\Vert \lambda_t\Vert ^2
+\Vert \phi\Vert _w^2+K\Vert \phi_t\Vert _w^2.
$$

这是含时间导数层和加权辅助量的约束图范数。其非退化性使用空间关系和 Poincaré；能量含交叉项，不能用“对所有独立点态变量的矩阵正定”替代全域估计。[S2 (6.5)、§8]

### 7.3 耗散的定义不能省略

按 **V7 (7.2)**，$j\ne i$：

$$
\mathscr S[U]=\int_{\Omega_+}\sum_i
\left[\frac{\sigma_i(c+\sigma_i)}a\Lambda_i^2+
\frac{\sigma_j(c-\sigma_j)}a(\partial_i v)^2\right]
+\int_Z c|\nabla v|^2.
$$

这里的系数有界，零区的贡献被显式保留；没有在 $\partial\Omega_+$ 上另做主要分部积分。[S2 §§1、7.1]

按 **V7 (7.7)–(7.8)**：

$$
\begin{aligned}
\mathcal D_c[U]=\mathscr S[U]
&+\mu\epsilon\int_\Omega[(a-c)v_t^2+bcv^2]\\
&+\frac\mu\kappa\int_\Omega[\tau R_t^2+(a-c+\tau(ac-b))R^2+bcz^2],\\
\mathcal D_7&=\mathcal D_c[U_0]+K\mathcal D_c[U_1].
\end{aligned}
$$

本式只定义耗散表达式；$\mathcal D_c$ 一般不非负，$\mathcal D_7\ge0$ 是主证明的结论。不能把名称“耗散”当成已有的符号证据。[S2 §§7.3、9、11.1]

为明确闭合中的辅助量，按 **V7 (9.2)** 在 $\Omega_+$ 取 $\theta_i=\sigma_i/a$，在 $Z$ 取 $\theta_x=\theta_y=1/2$，定义

$$
J(U)=\int_\Omega\sum_i[\theta_i\Lambda_i^2+\theta_j(\partial_i v)^2].
$$

$\theta$ 与 $w$ 的零区取值不同；也不同于 V6 的零延拓比值，必须分开命名。[S2 §9.2；R v0.2.1]

## 8. 最终主定理必须交付的结论

对任意满足 H01–H09 的数据、兼容提升及已存在的解，在 $[0,T]$ 上，以 §7 的**具体定义**计算能量和耗散，拟证明以下结论。此处每条均为输出，不能放回输入。[S2 定理 6.1；R §5]

1. **状态及模型对应。** 五不变量保持；零初值导出 (2.5)–(2.6)；加权状态合法；两层确为同一解的时间层；提升规范在声明类中唯一。[S2 §§2、5–6]
2. **图范数控制及非负性，V7 (6.7)：** 对每个 $t\in[0,T]$，

   $$
   \frac14\mathcal N_7(t)^2\le\mathcal E_7(t)\le\mathcal N_7(t)^2.
   $$

3. **真实导数与耗散闭合，V7 (7.8)、(6.8)：** 内部时间上

   $$
   \mathcal E_7'(t)=-\mathcal D_7(t),
   $$

   $$
   \mathcal D_7\ge\frac12(\mathscr S[U_0]+K\mathscr S[U_1])
   +\frac{\mu\tau}{4\kappa}(\Vert P_t\Vert ^2+K\Vert P_{tt}\Vert ^2)\ge0.
   $$

4. **闭区间积分平衡和单调不增，V7 (6.9)：** 对所有 $0\le t_1\le t_2\le T$，

   $$
   \mathcal E_7(t_2)+\int_{t_1}^{t_2}\mathcal D_7(t)\,dt=\mathcal E_7(t_1),\qquad
   \mathcal E_7(t_2)\le\mathcal E_7(t_1).
   $$

5. **原电磁场与极化控制，V7 (6.10)：**

   $$
   \epsilon\Vert E\Vert ^2+\mu(\Vert H_x\Vert ^2+\Vert H_y\Vert ^2)+\kappa^{-1}\Vert P\Vert ^2
   \le\frac4\mu\mathcal E_7.
   $$

6. **原辅助变量也受控，V7 (8.4)–(8.8)：**

   $$
   \Vert u\Vert ^2\le8C_P^2\mathcal E_7,\qquad \Vert \phi\Vert ^2\le4\mathcal E_7,
   $$

   $$
   \Vert q\Vert ^2\le\left(16\kappa^2C_P^2+\frac{8\kappa\tau^2}{\mu}\right)\mathcal E_7,
   $$

   $$
   \Vert Z_1\Vert ^2\le8\epsilon^2S^4C_P^2\mathcal E_7,\qquad
   \Vert Z_2\Vert ^2\le S^4\left(16\kappa^2C_P^2+\frac{8\kappa\tau^2}{\mu}\right)\mathcal E_7,
   $$

   $$
   \Vert Q_x\Vert ^2+\Vert Q_y\Vert ^2\le4S^2\mathcal E_7.
   $$

常数不能依赖终止时间 $T$、吸收梯度的大小或吸收正下界；这里的具体常数可依赖已列材料、域尺度和幅度参数。若解存在于全部非负时间，才可据同一先验结果对任意非负时刻应用，不能从有限区间估计直接宣布全局解存在。[S2 定理 6.1 后说明、§8.3]

## 9. 必须兑现的证明连接与禁止的弱化

证明任务的结构是：原八变量方程 → 时间不变量与场层等价 → 真实两层能量；一支完成局部求导与全域 Green 得到 (7.8)，另一支完成约束消元和 Poincaré 得到 (6.7)；再从原辅助演化推出 (9.4)–(9.5)，结合 (9.6)、(9.7) 闭合 (9.1)，最终得到 (6.8)–(6.10)。范数控制与能量求导可分别开发，不应人为制造互相循环依赖。[R §5；S2 §§7–9]

具体说，必须证明而不能预设：

$$
\Vert \nabla E\Vert ^2\le3J(U_1)+3S^2J(U_0)\quad\text{[V7 (9.5)]},
$$

$$
\mu cA\Vert E\Vert ^2\le\frac K2(\mathscr S[U_1]+S^2\mathscr S[U_0])
\quad\text{[V7 (9.6)]},
$$

$$
\mu cAK\Vert E_t\Vert ^2\le\frac{\mu\tau}{4\kappa}
(\Vert P_t\Vert ^2+K\Vert P_{tt}\Vert ^2)\quad\text{[V7 (9.7)]}.
$$

最终具体 PDE 定理不得残留“假设 Green/Poincaré 成立”“假设能量已经求导正确”“假设 $\mathcal D_7\ge0$”等未兑现接口。它们可作为明确命名的条件性中间定理的输入，并在 inventory 中标出，但不能因此把最终主定理标为完成。[R v0.3–v0.5、§15；S5]

本合同不要求所有非零状态严格衰减，不宣称任意八变量 $L^2$ 状态都可定义此能量，不宣称解存在唯一，不用 $e^{-Ct}\mathcal E(t)$ 或未知未来积分替换上述 $\mathcal E_7$。这些边界及材料待核验项统一见 [scope.md](scope.md)。
