# 二维变系数 strict PML 的非局部记忆能量审查

Problem id: `2d_maxwell_pml_energy_functional_exploration`

Terminal artifact: `results/v6_tex/nonlocal_memory_strict_pml_report.md`

## 原始目标与结论

目标是对二维连续 Maxwell--Debye 系统的严格坐标拉伸 PML，在
`sigma_x=sigma_x(x)>=0`, `sigma_y=sigma_y(y)>=0` 下寻找正定、与自然状态范数
等价且单调的能量，并严格审查新 PDF 提出的椭圆非局部修正。

本轮结论分级为 **Level B：已证明条件性单调能量**。在双轴角 PML 子域、相容状态、
非正边界通量以及下述点态 Schur 条件下，原 Baffet--Debye 能量满足

```text
E_B'(t)+theta D_0(t) <= 0,  theta>0.
```

对任意非负 `W^{1,infty}` 剖面的无条件 Level A 结论没有得到。新 PDF 的椭圆修正
完整求导后为

```text
F'/eta=(lambda_t,grad z)+(lambda-u grad a,grad z_t),
```

并不产生抵消 `R_sigma=-(u grad a,lambda)` 所需的
`+(u grad a,lambda)`；因此该候选失败。局部交叉项、第二椭圆变量和时间 primitive
也留下明确的新余项。Gramian 路线只在预先指数稳定和精确可观测假设下给出 Level C，
这些假设尚未独立证明。

严格 PML 的内界面 perfect matching 与有限厚外边界截断严格区分：前者成立，后者
通常仍有反射。Port layer 有无条件耗散能量但斜入射不匹配，未被用作最终模型。

## Fact index

| fact id | 状态 | 证据/verification |
|---|---|---|
| `fact:2d_maxwell_pml_energy_functional_exploration:v6-strict-matching-level-b` | verified | `verification/results/verify-20260714T112741879698Z-fact-reverify-fact-2d_maxwell_pml_energy.json` |
| `fact:2d_maxwell_pml_energy_functional_exploration:v6-elliptic-correction-residual` | verified | `verification/results/verify-20260714T112105126790Z-fact-verify-fact-2d_maxwell_pml_energy_f.json` |

两项 durable fact 均已通过真实 agent verification 并由 CLI promote。

## 1. 来源--公式/结论--用途追溯表

| 来源 | 页码/公式或结论 | 本轮用途 |
|---|---|---|
| `references/nonlocal_memory_energy_strict_pml.pdf`（项目研究稿，未同行评审） | pp.3--4, (9)--(17)：strict stretch 与导纳；pp.7--8, (42)--(50)：椭圆候选与 Gramian | 重新推导 matching；完整补上该稿遗漏的 `z_t` 与能量导数，并否定其动态抵消 |
| `references/variable_coefficient_baffet_energy.pdf`（项目研究稿） | pp.5--7, (14)--(29)：`E_B`, `D_0`, `R_sigma` 与小梯度条件 | 逐项复核 Baffet 恒等式并把全局常数条件加强为点态矩阵 Schur 条件 |
| `results/v5_variable_coefficient_baffet/variable_coefficient_baffet_next_step_report.md` | “Short Answer”, “Required Judgments” | 继承已验证的 v5 余项与 port-layer 不匹配结论，不把 port 层冒充 PML |
| `results/v5-tex/variable_coefficient_baffet_energy_analysis.tex` | (Baffet energy), (D0), (small-gradient), (port mismatch) | 核对所有系数、符号、边界通量与物理区退化 |
| D.H. Baffet, M.J. Grote, S. Imperiale, M. Kachanovska, *Energy Decay and Stability of a Perfectly Matched Layer for the Wave Equation*, J. Sci. Comput. 81 (2019), 2237--2270, [DOI 10.1007/s10915-019-01089-9](https://doi.org/10.1007/s10915-019-01089-9) | PDF pp.5--7，(2.3)--(2.9), Thm.2.1：常阻尼二维 primitive 能量 | Baffet 乘子 `u_t+a u`、`lambda=grad u+phi`、常系数抵消的原始证明；该文明确限制常阻尼 |
| P. Joly, *An elementary introduction to the construction and the analysis of perfectly matched layers for time domain wave propagation*, SeMA J. 57 (2012), 5--48, [DOI 10.1007/BF03322599](https://doi.org/10.1007/BF03322599) | PDF pp.7,10--11：阻抗匹配、复坐标变换、变剖面；(17), Thm.1 | 区分 impedance matching、吸收、稳定与有限截断；支持任意法向剖面坐标变换 |
| É. Bécache, M. Kachanovska, M. Wess, *Convergence analysis of time-domain PMLs for 2D electromagnetic wave propagation in dispersive waveguides*, ESAIM:M2AN 57 (2023), 2451--2491, [DOI 10.1051/m2an/2023060](https://doi.org/10.1051/m2an/2023060) | §2.2, (8)--(14), Thm.2.11；§3 Laplace inf-sup | 用于 dispersive PML 的 Laplace 域实现、因果性、稳定/收敛与异质扰动警告；不等同于本轮时域单调能量 |
| É. Bécache, S. Fliss, M. Kachanovska, M. Kazakova, *On a surprising instability result of Perfectly Matched Layers for Maxwell’s equations in 3D media with diagonal anisotropy*, C. R. Math. 359 (2021), 249--256, [DOI 10.5802/crmath.165](https://doi.org/10.5802/crmath.165) | PDF pp.5--8, (9)--(11), Thm.1 | 说明 matching 不蕴含稳定；3D/backward-wave 障碍不可误移植成当前 2D 各向同性反例 |
| `sources/energy_functional_problem.tex` | Maxwell--PML 原问题、边界与阶段目标 | 固定物理符号并避免改题到旧 ADE/port 模型 |
| `sources/energy_ansatz_notes.tex` | naive energy、shifted variables、Lyapunov 搜索建议 | 对照局部交叉项、有限维矩阵和 Cole--Cole 后续方向；该文件明确不是证明 |
| `verification/algebra/VariableCoefficientBaffet.lean` | Schur、Debye primitive、乘积法则 | 复用 v5 代数目标并在新 Lake 环境中扩展 |
| `verification/algebra/variable_coefficient_baffet_sympy.py` | determinant、product rule、matching、port mismatch | 新脚本的回归基线 |
| `lean_verification/PMLVerification/VariableCoefficientBaffet.lean` | Mathlib 项目版本的 v5 定理 | 确认正确 Lake/Mathlib 调用方式 |

## 2. 固定模型与严格时域等价性

物理 TM Maxwell--Debye 系统为

```text
epsilon E_t+P_t=partial_x H_y-partial_y H_x,
mu H_x,t=-partial_y E,  mu H_y,t=partial_x E,
tau P_t+P=kappa E.
```

`epsilon,mu,tau,kappa>0`。在 `Re s>0` 令

```text
S_i(s,x_i)=1+sigma_i(x_i)/s,  partial_i -> S_i^{-1}partial_i,
epsilon_D(s)=epsilon+kappa/(1+tau s).
```

严格频域系统为

```text
s epsilon_D E=S_x^{-1} partial_x H_y-S_y^{-1} partial_y H_x,
mu s H_x=-S_y^{-1}partial_y E,
mu s H_y= S_x^{-1}partial_x E.
```

取 causal primitive

```text
u_t=E, q_t=P, q+tau P=kappa u,
a=sigma_x+sigma_y, b=sigma_x sigma_y,
Gamma_1=diag(sigma_x,sigma_y),
Gamma_2=diag(sigma_y-sigma_x,sigma_x-sigma_y),
phi_t+Gamma_1 phi=Gamma_2 grad u,
lambda=grad u+phi.
```

则精确时域系统是

```text
mu{epsilon(u_tt+a u_t+b u)+P_t+aP+bq}-div lambda=0,
phi_t+Gamma_1 phi=Gamma_2 grad u,
tau P_t+P=kappa u_t, q_t=P, q+tau P=kappa u.
```

Laplace 域逐点有

```text
lambda_x=(S_y/S_x)partial_x u, lambda_y=(S_x/S_y)partial_y u,
lambda_x=mu S_y H_y, lambda_y=-mu S_x H_x.
```

因此它对分离剖面完全等价于 strict stretch，而非仅对某些模态相似。非零初始数据时，
辅助变量必须初始化为其 causal history；本文的无源 Laplace 匹配采用 PML 内零历史，
并要求 `q(0)+tau P(0)=kappa u(0)`, `u_t(0)=E(0)`, `lambda(0)=grad u(0)+phi(0)`。
若从零时刻截断任意已有波场而不给 history，则会出现初值源项，不能援引同一等价性。

剖面假设：`sigma_i in W^{1,infty}`, 非负，仅依赖 `x_i`，物理区为零，外层有界；
为无分布界面余项，内界面取连续零迹，或把跳跃作为显式 transmission flux。物理/PML
界面连续切向 `E,H`；外边界可取 PEC `E=0`（primitive 零历史下 `u=0`），也可取周期/
非正能量通量条件。`sigma_x=sigma_y=0` 时 `phi=0`, `lambda=grad u`，系统退化为物理
Maxwell--Debye 的时间 primitive。

## 3. 独立 perfect-matching 检验

在平直 `x=0` 界面，右侧仅法向 stretch (`S_y=1`)。对任意 `Re s>0` 与实 `k_y`，令

```text
nu_0^2=k_y^2+mu s^2 epsilon_D(s).
```

固定由 `Re s>0` 的 causal outgoing resolvent 解析延拓得到的平方根分支；右侧透射场取

```text
E_+(x,y)=T exp(i k_y y-nu_0 integral_0^x S_x(s,xi) dxi).
```

这不是只比较平方：同一 `nu_0` 分支直接进入场。于是

```text
S_x^{-1}partial_x E_+=-nu_0 E_+,
Y_+=-H_y/E=nu_0/(mu s)=Y_0.
```

（改变法向/导纳符号约定会同时改变两侧，不改变结论。）传输条件给出

```text
1+R=T,  Y_0(1-R)=Y_+T,
R=(Y_0-Y_+)/(Y_0+Y_+)=0.
```

证明只用积分坐标 `integral S_x dx`，所以任意非负法向变剖面仍匹配。它仅证明内界面
无反射；有限厚层的 PEC/其他外边界会产生经衰减后返回的截断反射。

角区是两坐标均按同一 strict transform 拉伸，坐标变换的一致延拓仍保持各内界面匹配。
但若所谓 multi-axial/cross damping 在 `x` 界面令切向 `S_y!=1`，则

```text
Y_+^2-Y_0^2 = k_y^2(S_y^{-2}-1)/(mu^2 s^2),
```

一般非零；只有 `S_y=1`、`k_y=0` 或另有精确补偿才匹配。SymPy 已验证该缺陷。

## 4. Baffet 恒等式、正性与 Level-B 定理

令 `W=u_t+a u`。唯一新增乘积法则项是

```text
grad W=grad u_t+a grad u+u grad a.
```

定义

```text
alpha=1+2a tau, beta=a+b tau, gamma=a^2+b(1+a tau),
E_B=1/2 integral [mu epsilon W^2+|lambda|^2
 +phi^T a^{-1}Gamma_1 phi+mu epsilon b u^2
 +(mu/kappa)(alpha P^2+2 beta Pq+gamma q^2)].
```

逐项乘主方程以 `W`，使用 Baffet flux identity 与 Debye primitive identity 后，

```text
E_B'=-D_0+R_sigma+B,
R_sigma=-integral u grad(a).lambda,
B=integral_boundary W lambda.n,
D_0=integral [lambda^T Gamma_1(I+a^{-1}Gamma_1)lambda
 +(b/a)|grad u|^2+mu epsilon a b u^2
 +(mu/kappa){tau P_t^2+tau(a^2-b)P^2+a b q^2}].
```

所有符号均由 Lean/SymPy 的展开回归覆盖。`D_0>=0` 需要 `a>0`, `sigma_i>=0` 和正材料
参数，因为 `a^2-b=sigma_x^2+sigma_x sigma_y+sigma_y^2>=0`。

`(P,q)` 矩阵的首主子式为 `alpha>0`，行列式为

```text
b+a b tau+2a^3 tau+b(2a^2-b)tau^2>0,
2a^2-b=2sigma_x^2+3sigma_x sigma_y+2sigma_y^2.
```

在角域 `sigma_i` 有正下界和有限上界时，`E_B` 与
`||(u_t,u,lambda,phi,P,q)||_{L2}^2` 等价：`b u^2` 与 `W^2` 联合控制 `(u_t,u)`，
`a^{-1}Gamma_1` 控制 `phi`，Sylvester 判据控制 `(P,q)`。边 PML (`b=0`)、物理区
(`a=0`) 或零频 primitive gauge 上，全 primitive 空间不具统一等价性；必须限制到 causal
compatibility manifold，或在物理区拼接缩放后的自然 Maxwell--Debye 能量
`1/2 integral(mu epsilon E^2+mu^2|H|^2+(mu/kappa)P^2)`。界面 `a=0` 时
`W=E`, `lambda=(mu H_y,-mu H_x)`，通量恰好匹配。

`R_sigma` 无符号：若开集上 `u>0`, `lambda=-c grad a`，则 `R_sigma>0`；取相反方向则
`R_sigma<0`。这是可复查的状态选择，不由 `partial_i sigma_i>=0` 改变。

令

```text
C_lambda=Gamma_1(I+a^{-1}Gamma_1), c_u=mu epsilon a b,
Q=[[c_u,(grad a)^T/2],[grad a/2,C_lambda]].
```

**条件单调定理。** 若角域上 `C_lambda>0`，剖面有正上下界，边界通量非正，且存在
统一 `delta>0` 使

```text
(grad a)^T C_lambda^{-1}(grad a) <= 4(1-delta)c_u,
```

则 `Q>=0` 的 Schur 补给出 `E_B'+theta D_0<=0`，其中可取某个仅依赖
`delta` 与耗散块等价常数的 `theta>0`。积分版本是

```text
D_0>=m_u||u||^2+m_lambda||lambda||^2+...,
||grad a||_infty^2<4m_u m_lambda.
```

这确实给单调性，不只是带增长常数的估计。若只有能量控制而无 Schur 条件，则仅有
`E_B'<=C_sigma E_B` 与 Gronwall 界；本报告不称其为单调下降。

## 5. 椭圆非局部候选的完整审查

取 `Omega_+` 为具有 Lipschitz 边界的角 PML 子域，`V=H_0^1(Omega_+)`，
`C=C^T`, `C>=c_*I`, `c>=0`，

```text
L v=-div(C grad v)+c v,
A(z,v)=(C grad z,grad v)+(c z,v),
z=L^{-1}div(u grad a),
A(z,v)=-(u grad a,grad v).
```

Dirichlet 情形无核且 Lax--Milgram 可逆。Neumann 情形必须取
`(C grad z+u grad a).n=0`，并要求 `c>=c_0>0`，或在均值零商空间满足 compatibility；
否则常数核使 `L^{-1}` 未定义。若改用其他边界条件，弱式会保留相应边界项。

由于剖面与 `L` 不依赖时间，

```text
A(z_t,v)=-(u_t grad a,grad v),
z_t=L^{-1}div(u_t grad a).
```

对 PDF 候选

```text
F=eta(lambda,grad z)+eta/2 A(z,z)
```

有完整恒等式

```text
F'/eta=(lambda_t,grad z)+(lambda,grad z_t)+A(z,z_t)
      =(lambda_t,grad z)+(lambda-u grad a,grad z_t).
```

故

```text
(E_B+F)'=-D_0-(u grad a,lambda)
 +eta[(lambda_t,grad z)+(lambda-u grad a,grad z_t)]+B.
```

目标余项仍在，并新增 `lambda_t,u_t` 项；不是系数调节问题，而是静态椭圆变量的时间导数
结构错误。标量代理 `ell z=-g u` 的完整残差已由 Lean 与 SymPy 精确验证。

静态正性方面，`L^{-1}div(u grad a):L2->H_0^1` 有界；若 `eta` 相对 `E_B` 的
`lambda,u` 强制性足够小，可用 Schur 补使候选能量正定且有上界。但这依赖原能量已在角域
等价，且不能修复导数。在 `a->0`/边域，统一下界消失，因此也不能声称全目标状态范数等价。

两次修改均已计算：

1. 第二椭圆变量 `p=L^{-1}div(lambda)` 的交叉项只产生
   `u_t lambda+u lambda_t` 型项，不产生 `u lambda`。
2. 时间 primitive `r_t=lambda` 使 `d(u grad a,r)/dt` 含所需
   `+(u grad a,lambda)`，但留下 `(u_t grad a,r)`；裸交叉项不正定，添加 `||r||^2`
   又产生 `(r,lambda)`，且新 gauge 状态不与原自然范数等价。

## 6. 其余两条路线与比较

局部候选 `integral c_i u lambda_i` 使用

```text
lambda_i,t=partial_i u_t+sigma_j partial_i u-sigma_i lambda_i.
```

取 `c_i=-(partial_i a)/sigma_i` 虽产生目标抵消，却留下

```text
-(partial_i a/sigma_i)
 [u_t lambda_i+u partial_i u_t+sigma_j u partial_i u],
```

并在 `sigma_i=0` 界面奇异。一般局部 symmetrizer 必须满足主部对称条件及矩阵微分
Lyapunov/Riccati 不等式

```text
M A_0^{-1}A_i=(M A_0^{-1}A_i)^T,
M A_0^{-1}B+(A_0^{-1}B)^T M
-sum_i partial_i(M A_0^{-1}A_i)>=0, M>0.
```

本轮没有找到跨 `a=0` 的正解。

Gramian 路线：若相容 strict-ADE 生成元 `A_sigma` 在带 PEC/transmission 的自然
`H(curl) x L2-history` 空间上独立生成指数稳定半群，且输出 `C` 精确可观测，则

```text
G=int_0^infty T(t)^*C^*C T(t)dt,
A_sigma^*G+G A_sigma=-C^*C
```

给正定、等价、单调能量。指数稳定保证积分收敛，精确可观测保证下界；本轮均未独立证明，
所以不能循环地用该 `G` 证明稳定。只有强稳定时积分可发散；有限时域 Gramian 的导数是
`||CT(T)U||^2-||CU||^2`，加权 Gramian 的导数是 `-||CU||^2+2delta E_delta`，均不自动
单调。下一步应做 resolvent/KYP，而不是宣称已完成 Gramian。

ratio `(s+sigma_j)/(s+sigma_i)=1+(sigma_j-sigma_i)/(s+sigma_i)` 在右半平面为
positive-real，但时域指数核系数可变号；必须验证耦合 MIMO kernel/KYP storage，不能把
标量 positive-real 直接写成正卷积核。

| 路线 | matching | 正定/等价 | 单调性 | 参数条件 | Cole--Cole | DG |
|---|---|---|---|---|---|---|
| 局部 Baffet/交叉项 | 保持 strict PML | 角域可；界面退化 | Baffet 在 Schur 条件下成功；额外交叉项失败 | 小梯度、双轴正下界 | Debye 块可换正记忆，但空间余项仍在 | 最直接，可保留余项/设计通量 |
| 椭圆非局部 | 不改方程，故 matching 保持 | 小 `eta` 仅角域静态可 | PDF 候选失败，出现 `u_t,lambda_t` | 椭圆性及原能量强制性 | 可组合但计算昂贵 | 全局椭圆 solve 不利 DG |
| Gramian/KYP | 取同一生成元则保持 | 需 exact observability | 条件 Level C | 预先指数稳定/resolvent | 最有推广潜力 | 不显式，不利直接离散 |

论文下一步最值得推进的是 **resolvent/KYP Gramian 的非循环构造**；近期 DG 论文最可执行的
是 **Level-B Baffet 定理 + 分片常数/小梯度剖面 + 通量控制**。

## 7. 低维、冻结系数与退化必要检验

| 检验 | `M>0` / `Q>=0` 判断 | 结论 |
|---|---|---|
| `k_y=0` 一维法向 | 物理/最小 ADE 状态有 1D 被动能量；全 primitive `b=0` 有 gauge 零方向 | matching 成立；不能据此宣称全 primitive 等价 |
| 冻结 `k_y!=0` | 常系数角域 `M_B>0`；耗散 `Q_0>=0` | 通过必要测试；固定系数不看见 `grad a` |
| 常系数边层 | `b=0`，`u,phi` 某些方向退化 | 需 compatibility/reduced state |
| 常系数角层 | `sigma_i>0` 时 Sylvester/Schur 给 `M_B>0,Q_0>=0` | Baffet 定理适用 |
| 局部缓变 | `Q=[[c_u,g^T/2],[g/2,C_lambda]]` | 当且仅当对应 Schur 补非负 |
| 高梯度 | `m_u=m_lambda=1,g=3` 的特征值 `-1/2,5/2` | 原 Baffet 导数可正；精确反例控制 |
| `a->0` 界面 | `a^{-1}Gamma_1`, `b/a` 只能逐方向延拓，最小特征值趋零 | 分区物理能量；无统一全 primitive 等价 |
| 零频/静态 | `S_i` 含 `sigma_i/s`，primitive 有积分/gauge 模 | 需 causal compatibility；不能从零频代理推出严格衰减 |

对非局部候选，有限维代理的能量矩阵可在小 `eta` 下正，但其耗散矩阵保留已显示的
`u_t,lambda_t` 非对角项，故不存在由该计算推出的参数无关 `Q>=0`。随机特征值只作烟雾测试；
判别依据是精确 determinant/Sylvester/Schur 与有理反例。

## 8. 机器验证与交付物

- `results/v6_tex/NonlocalMemoryStrictPML.lean`：Lake/Mathlib 通过，无 `sorry/admit/axiom`。
- `results/v6_tex/nonlocal_memory_strict_pml_sympy.py`：通过 strict matching、乘积法则、
  非局部完整导数、两种修正、局部余项、Schur 与对抗/随机矩阵检查。
- `results/v6_tex/verification_outputs.md`：记录工具版本、命令、退出码和完整关键输出。
- `results/v6_tex/nonlocal_memory_strict_pml_analysis.tex/.pdf`：中文完整证明稿。
- `results/v6_tex/claims_and_open_problems.md`：声明边界与下一步。

## Assembly

`fact:...:v6-strict-matching-level-b` 组合严格 Laplace stretch、固定平方根分支的导纳计算、
Baffet 全恒等式、角域正定性与点态 Schur 条件，回答“能证明什么”：strict PML 保持
perfect matching，并在明确小梯度/强制性条件下有自然范数等价的单调能量。

`fact:...:v6-elliptic-correction-residual` 组合弱式、`z_t`、两项完整求导、静态 Schur 与
有限维机器代数，回答“新非局部候选是否升级为 Level A”：否；它留下具体的
`lambda_t,z_t,u_t` 余项，两种自然修正亦失败。

因此量词没有缩小成 port layer，也没有把 Gronwall 写成衰减。最终等级是 Level B；
一般非负变剖面的无条件显式单调能量仍为开放问题，而非本轮已证明的事实。

最终 assembly verification 已通过：
`verification/results/verify-20260714T113553444125Z-assembly-assemble-the-verified-v6-result.json`。
针对 `.iteris/goal_prompt.txt` 完整量词范围的 goal-success verification 已通过：
`verification/results/verify-20260714T114324180024Z-goal_success-execute-the-complete-v6-goa.json`。
