# V7：二维 Maxwell–Debye PML 的全域单调能量

## 常数移位乘子、时间导数层与显式小幅度条件

2026 年 9 月 24 日

研究原八变量二维 TM Maxwell--PML 系统，保留 $P+\tau P_t=\kappa E$，外边界为 PEC。 首先给出原变量与 primitive 变量的完整时域映射、全部初值不变量、可检验且演化保持的兼容提升类，并保留 Laplace 变换中的非零初值项。 独立复核 V6 全域平衡，证明其点态 Schur 条件不能覆盖从零连续起步的非平凡吸收剖面。 主要新结果是一个**小吸收幅度下的全域单调能量先验定理**：不改变方程，采用常数 $c$ 的乘子 $u_t+cu$、奇异但可积的辅助变量权重和一阶时间导数层，构造 $\mathcal E_7=\mathcal F_c[u,P,q,\phi]+K\mathcal F_c[u_t,P_t,q_t,\phi_t]$。 在明确的材料--域尺度条件和 $\max_i\|\sigma_i\|_\infty\le c/4$ 下，证明能量与指定的加权一阶图范数等价，控制原电磁场、极化与四个 PML 辅助变量，并满足 $\mathcal E_7'=-\mathcal D_7\le0$。 证明不要求吸收系数有正下界，不要求其梯度小，也不要求内部子区分别耗散。给出保留物理区、四个边层、四个角层及连续零起点的多项式剖面。 任意幅度下的一般全域单调能量尚未证明；本文不声称已证明整个初边值问题的适定性。

---

## 1　研究对象、输入依据与结论范围

本稿固定上传原文件 `sources/energy_functional_problem.tex` 中的八变量模型；对照 `results/v6_tex/nonlocal_memory_strict_pml_analysis.tex`、同目录报告，以及 `results/v6_mathematical_completeness_review_20260924.md`。 审查稿只作为待核验材料，不作为证明依据。原始文件的哈希与本次检查的文件范围另见交付包的 `source_manifest.json`。 本稿的主结论是定理 6.1，其完整证明见第 7--9 节。

设 

$$
\Omega=(x_-,x_+)\times(y_-,y_+),\quad L_x=x_+-x_-,\quad L_y=y_+-y_-.
$$

 这是整个截断计算域，而不是单个角层。 材料参数为正常数。全篇考虑实值场；复值场可对相应内积取实部。 所有未注明下标的范数均为 $L^2(\Omega)$ 范数。 记 

<a id="eq:normalization"></a>

$$
\epsilon=\epsilon_0\epsilon_\infty>0,\qquad
 \kappa=\chi=\epsilon_0(\epsilon_s-\epsilon_\infty)>0,\qquad
 p(x)=\frac{\sigma_x^{\rm old}(x)}{\epsilon_0},\quad
 r(y)=\frac{\sigma_y^{\rm old}(y)}{\epsilon_0}.
\tag{1.1}
$$

 其中 $\mu>0,\tau>0$。下文的归一化吸收系数为 $\sigma_x=p,\sigma_y=r$；不再用原有电导率量纲的 $\sigma_i^{\rm old}$。 设 $p,r\in W^{1,\infty}$，非负，且在矩形物理区的相应坐标区间上为零。 记 

$$
a=p+r,\qquad b=pr,\qquad Z=\{a=0\},\qquad \Omega_+=\{a>0\}.
$$

 所有集合与权重均按几乎处处意义理解。$\Omega_+$ 不被假定为单一 Lipschitz 子域；本文不在其边界上进行主要分部积分。

<a id="sec:mapping"></a>

## 2　原八变量与 primitive 系统：时域等价

### 2.1　原系统的归一化形式

以 $Z_1=P_{z,1}$、$Z_2=P_{z,2}$ 简记电辅助变量。原系统准确地变为 

<a id="eq:eight"></a>

$$
\begin{aligned}
 \epsilon E_t&=\partial_xH_y-\partial_yH_x-\epsilon aE-P_t-aP+Z_1+Z_2,\\
 \mu H_{x,t}&=-\partial_yE-\mu(r-p)H_x+Q_x,\\
 \mu H_{y,t}&=\partial_xE-\mu(p-r)H_y+Q_y,\\
 \tau P_t+P&=\kappa E,\\
 Z_{1,t}&=-\epsilon bE,\qquad Z_{2,t}=-bP,\\
 Q_{x,t}&=-pQ_x+\mu p(r-p)H_x,\\
 Q_{y,t}&=-rQ_y+\mu r(p-r)H_y.
\end{aligned}
\tag{2.1}
$$

 外边界条件为 

<a id="eq:pec"></a>

$$
E=0\quad\text{于 }\partial\Omega.
\tag{2.2}
$$

 这里 $\alpha=1$ 仅将极化律变成 Debye 一阶方程，$P$ 未被删除。

### 2.2　变量提升和初值不变量

取初始原函数 $u_0,q_0$，定义 

<a id="eq:lift"></a>

$$
u(t)=u_0+\int_0^tE(s)\,\mathrm ds,\quad
 q(t)=q_0+\int_0^tP(s)\,\mathrm ds,\quad
 \lambda=(\mu H_y,-\mu H_x),\quad \phi=\lambda-\nabla u.
\tag{2.3}
$$

 由于材料参数和吸收系数不依赖时间，原系统给出以下五个时间不变量： 

<a id="eq:invariants"></a>

$$
\begin{aligned}
 C_D&=q+\tau P-\kappa u,\\
 C_{z1}&=Z_1+\epsilon bu,\qquad C_{z2}=Z_2+bq,\\
 C_x&=Q_x-p\phi_y,\qquad C_y=Q_y+r\phi_x.
\end{aligned}
\tag{2.4}
$$

 例如 $\partial_t C_D=P+\tau P_t-\kappa E=0$，两个 $C_z$ 的导数直接为零。 磁场方程还给出 

$$
\phi_{x,t}=-(p-r)\lambda_x+Q_y,\qquad
 \phi_{y,t}=(p-r)\lambda_y-Q_x.
$$

 所以 

$$
\partial_t(Q_y+r\phi_x)
 =-rQ_y+r(p-r)\lambda_x+r[-(p-r)\lambda_x+Q_y]=0,
$$

 $\partial_t(Q_x-p\phi_y)=0$ 同理。这些是不使用 Laplace 变换的初值核验。

<a id="prop:mapping"></a>

**命题 2.1** (完整时域对应). 若式 (2.4) 的五个初值均为零，则对所有存在的时刻 

<a id="eq:reconstruct"></a>

$$
\boxed{Z_1=-\epsilon bu,\quad Z_2=-bq,\quad Q_x=p\phi_y,\quad Q_y=-r\phi_x,}
\tag{2.5}
$$

 并且提升变量满足 

<a id="eq:primitive"></a>

$$
\begin{aligned}
 \mu\{\epsilon(u_{tt}+au_t+bu)+P_t+aP+bq\}&=\mathop{\mathrm{div}}\lambda,\\
 \phi_{x,t}+p\phi_x&=(r-p)\partial_xu,\\
 \phi_{y,t}+r\phi_y&=(p-r)\partial_yu,\\
 \lambda&=\nabla u+\phi,\\
 q_t=P,\qquad q+\tau P&=\kappa u,\qquad u_t=E.
\end{aligned}
\tag{2.6}
$$

 反之，任何足够正则的式 (2.6) 的解，按式 (2.3)、(2.5) 重构，均满足原八变量方程 (2.1)。

**证明。** 将 $Z_1+Z_2=-\epsilon bu-bq$ 代回电场方程，并注意 $\mathop{\mathrm{div}}\lambda=\mu(\partial_xH_y-\partial_yH_x)$，即得第一式。 代入 $Q_y=-r\phi_x$，有 $\phi_{x,t}=(r-p)\partial_xu-p\phi_x$；另一分量相同。 反向代回恢复电、磁及 Debye 方程。辅助方程也直接成立，例如 

$$
\partial_t(p\phi_y)
 =p[(p-r)\partial_yu-r\phi_y]
 =-pQ_x+\mu p(r-p)H_x,
$$

 其中使用 $\lambda_y=\partial_yu+\phi_y=-\mu H_x$。 四个辅助变量都被核验，而不是只验证消元后的波方程。 ◻

对于非零不变量，primitive 主方程右端增加 $\mu(C_{z1}+C_{z2})$，$\phi$ 方程右端增加 $(C_y,-C_x)$； $C_D\ne0$ 也改变极化兼容关系。因此不能将任意八变量初值直接解释为无源 primitive 初值。

### 2.3　任意八变量初值的真实增长反例

<a id="prop:growth"></a>

**命题 2.2**. 若物理区含非空开集，则原八变量系统在允许所有八变量初值的类上不存在一个有限初能量、统一控制磁场 $L^2$ 范数且单调不增的能量。

**证明。** 取非恒定 $\psi\in C_c^\infty(\Omega_{\rm phys})$，令 

$$
(H_x,H_y)=t\nabla\psi,\qquad (Q_x,Q_y)=\mu\nabla\psi,
 \qquad E=P=Z_1=Z_2=0.
$$

 支集处 $p=r=0$，且 $\partial_xH_y-\partial_yH_x=t(\psi_{xy}-\psi_{yx})=0$。 故这些函数满足全部原方程及 PEC。磁能按 $t^2$ 增长。 若 $\mathcal E\ge C\|H\|^2$ 且 $\mathcal E(t)\le\mathcal E(0)<\infty$，立即矛盾。 ◻

此反例针对显示的八变量方程允许的任意初值；它不属于后文兼容类，并未满足另加的无磁荷约束。 它不能用于否定通常从物理场启动、PML 辅助变量为零的相容实验。

<a id="sec:laplace"></a>

## 3　非零初值、历史和严格坐标拉伸的对应

本节的变换公式在 Laplace 变换存在的半平面成立；主定理证明不依赖它们，也不预先假设长期稳定。 对命题 2.1 的兼容解，精确公式是 

<a id="eq:laplace-init"></a>

$$
\begin{aligned}
 \widehat E&=s\widehat u-u_0,&
 \widehat P&=s\widehat q-q_0,\\
 (1+\tau s)\widehat P&=\kappa\widehat E+\tau P_0,&
 (1+\tau s)\widehat q&=\kappa\widehat u+\tau q_0,\\
 (s+\sigma_i)\widehat\phi_i
 &=(\sigma_j-\sigma_i)\partial_i\widehat u+\phi_{i0},\quad j\ne i,\\
 \widehat\lambda_i&=\frac{s+\sigma_j}{s+\sigma_i}\partial_i\widehat u
                 +\frac{\phi_{i0}}{s+\sigma_i}.
\end{aligned}
\tag{3.1}
$$

 主方程的完整变换为 

<a id="eq:lap-main"></a>

$$
\mu(s^2+as+b)(\epsilon\widehat u+\widehat q)-\mathop{\mathrm{div}}\widehat\lambda
 =\mu\big[(s+a)(\epsilon u_0+q_0)+\epsilon E_0+P_0\big].
\tag{3.2}
$$

 例如 $u_{tt}$ 产生 $-su_0-E_0$，$q_{tt}=P_t$ 产生 $-sq_0-P_0$；这些项均未略去。

在零初值/零记忆的算子关系中，令 

$$
S_x(s,x)=1+p(x)/s,\quad S_y(s,y)=1+r(y)/s,\qquad
 \epsilon_D(s)=\epsilon+\kappa/(1+\tau s).
$$

 原变量与 V6 所写的 stretched-coordinate 磁场 $H^{\rm SC}$ 不是同名相同状态，而是 

<a id="eq:sc-map"></a>

$$
\widehat H_x=S_x\widehat H_x^{\rm SC},\qquad
 \widehat H_y=S_y\widehat H_y^{\rm SC},\qquad
 \widehat\lambda_x=\mu S_y\widehat H_y^{\rm SC},\quad
 \widehat\lambda_y=-\mu S_x\widehat H_x^{\rm SC}.
\tag{3.3}
$$

 $S_i^{-1}$ 的时域实现是因果滤波器，例如 

$$
H_x^{\rm SC}(t)=H_x(t)-p\int_0^t e^{-p(t-s)}H_x(s)\,\mathrm ds,
$$

 $H_y^{\rm SC}$ 使用 $r$。这样可得到严格的 $\partial_i\mapsto S_i^{-1}\partial_i$ 结构，而没有修改 PML 系数。 分离依赖保证 $S_y$ 可穿过 $\partial_x$、$S_x$ 可穿过 $\partial_y$。

更具体地，对第 5 节中支撑在物理区的非零初值族，$Z_{1,0}=Z_{2,0}=Q_{x,0}=Q_{y,0}=0$、$\phi_0=0$，且吸收系数与全部初值的乘积为零。 对原方程消去 $Q_x,Q_y,Z_1,Z_2$，得到 

<a id="eq:sc-nonzero"></a>

$$
\begin{aligned}
 \mu(s\widehat H_y^{\rm SC}-H_{y0})&=S_x^{-1}\partial_x\widehat E,\\
 \mu(s\widehat H_x^{\rm SC}-H_{x0})&=-S_y^{-1}\partial_y\widehat E,\\
 s(\epsilon\widehat E+\widehat P)-(\epsilon E_0+P_0)
 &=S_x^{-1}\partial_x\widehat H_y^{\rm SC}
   -S_y^{-1}\partial_y\widehat H_x^{\rm SC}.
\end{aligned}
\tag{3.4}
$$

 例如磁场消元先给出 $\mu s(S_x/S_y)\widehat H_y=\partial_x\widehat E+\mu H_{y0}$； 初值支集上 $p=r=0$，再用 $\widehat H_y=S_y\widehat H_y^{\rm SC}$ 得第一式。 电场消元给出 $sS_xS_y(\epsilon\widehat E+\widehat P)$，而初值项为 $\epsilon E_0+P_0$；除以 $S_xS_y$ 时该初值不变。 因此常用非零物理初值也保留标准坐标拉伸的初值源项。 对一般非零 PML 记忆初值，应使用式 (3.1)--(3.2)，不能擅自化为式 (3.4)。

<a id="sec:v6"></a>

## 4　独立复核 V6：全域恒等式成立，但原 Schur 条件不够

### 4.1　权重延拓、完整能量和耗散

在 $Z$ 上定义 $\sigma_i/a=0$、$b/a=0$，其余处按通常比值定义。 这些权重有界可测；后续只作时间求导，不对它们作空间微分。 在兼容类 $\phi=0$ 于 $Z$ 下，定义整个 $\Omega$ 上的 

<a id="eq:V6energy"></a>

$$
\begin{aligned}
 \mathcal E_B=\frac12\int_\Omega\Big\{&
 \mu\epsilon(E+au)^2+|\lambda|^2+\sum_i\frac{\sigma_i}{a}\phi_i^2+\mu\epsilon b u^2\\
 &+\frac\mu\kappa\big[(1+2a\tau)P^2+2(a+b\tau)Pq
 +(a^2+b(1+a\tau))q^2\big]\Big\}\,\mathrm dx\,\mathrm dy,
\end{aligned}
\tag{4.1}
$$

 

<a id="eq:V6diss"></a>

$$
\begin{aligned}
 D_B=\int_\Omega\Big\{&\sum_i\sigma_i\Big(1+\frac{\sigma_i}{a}\Big)\lambda_i^2
 +\frac ba|\nabla u|^2+\mu\epsilon ab u^2\\
 &+\frac\mu\kappa[\tau P_t^2+\tau(a^2-b)P^2+abq^2]\Big\}\,\mathrm dx\,\mathrm dy\ge0.
\end{aligned}
\tag{4.2}
$$

 在 $Z$ 上能量密度是 $\frac12(\mu\epsilon E^2+|\lambda|^2+\mu P^2/\kappa)$，即原 Maxwell--Debye 能量的 $\mu$ 倍。 极化矩阵的行列式为 

$$
b+ab\tau+2a^3\tau+b(2a^2-b)\tau^2.
$$

 它在 $a>0$ 时严格为正，在 $a=b=0$ 时矩阵为 $\operatorname{diag}(1,0)$，故式 (4.1) 全域非负。 跨零吸收区的扩展状态范数等价不能只靠正角区 Sylvester 判据推断。

<a id="prop:V6balance"></a>

**命题 4.1** (V6 全域平衡). 对足够正则的兼容解，令 $W=E+au$，有 

<a id="eq:V6balance"></a>

$$
\mathcal E_B'=-D_B-\int_\Omega u\nabla a\cdot\lambda\,\mathrm dx\,\mathrm dy
                 +\left\langle W,\lambda\cdot n\right\rangle_{\partial\Omega}.
\tag{4.3}
$$

**证明。** 逐分量记 $h=\partial_i u,v=\partial_iE,f=\phi_i,l=\lambda_i=h+f$。 有 $f_t=\sigma_j h-\sigma_i l$、$l_t=v+\sigma_jh-\sigma_i l$。直接展开得 

$$
\frac12\partial_t\Big(l^2+\frac{\sigma_i}{a}f^2\Big)
 =(v+ah)l-\sigma_i\Big(1+\frac{\sigma_i}{a}\Big)l^2-\frac ba h^2.
$$

 在 $Z$ 上则是 $\frac12\partial_t|\lambda|^2=\lambda\cdot\nabla E$。 极化关系给出 $\kappa W=\tau P_t+(1+a\tau)P+aq$。 令 $Q_B=(1+2a\tau)P^2+2(a+b\tau)Pq+(a^2+b(1+a\tau))q^2$。 逐项展开并使用 $q_t=P$ 得到 

$$
(P_t+aP+bq)\kappa W
 =\tfrac12\partial_t Q_B+\tau P_t^2+\tau(a^2-b)P^2+abq^2.
$$

 将此式乘 $\mu/\kappa$，即为所列极化能量导数与耗散。 电块为 

$$
\epsilon(u_{tt}+au_t+bu)W
 =\frac\epsilon 2\partial_t(W^2+bu^2)+\epsilon ab u^2.
$$

 主方程乘 $W$ 并在整个 $\Omega$ 一次积分。由于 $\nabla W=\nabla E+a\nabla u+u\nabla a$，前两项与空间块抵消，只剩式 (4.3)。 ◻

若 $u_0\in H_0^1(\Omega)$，PEC 保证 $u(t)$ 零迹，故 $W$ 零迹，外边界项为零。 仅有 $E=0$ 而不限制 $u_0$ 的边界迹，不能推出这个结论。 若人为把域分为 Lipschitz 子区，内部面 $\Sigma$ 的两项为 $W\lambda^+\cdot n^++W\lambda^-\cdot n^-$，在 $W$ 单值、$\lambda\in H(\mathop{\mathrm{div}})$ 的法向迹相容条件下抵消。 这里无需要求每个子区能量分别下降。连续吸收剖面也不要求另设人工拼接能量。

### 4.2　Schur 条件不能一直延伸到零起点

正角区的 V6 条件是 

<a id="eq:schur"></a>

$$
(\nabla a)^TC_\lambda^{-1}\nabla a
 \le4(1-\delta)\mu\epsilon ab,\qquad
 C_\lambda=\operatorname{diag}\Big(\sigma_i(1+\sigma_i/a)\Big),\quad 0<\delta<1.
\tag{4.4}
$$

 固定一个 $r(y)>0$ 且满足 Fubini 截面性质的 $y$，舍去左端非负的另一分量，得 

$$
|p'(x)|\le2\sqrt{(1-\delta)\mu\epsilon\,r(2p+r)}\,p(x)\le C p(x).
$$

 若在从 $p(x_0)=0$ 到正吸收层的整个区间都成立，则绝对连续性给出 $p(x)\le C\int_{x_0}^xp(s)\,\mathrm ds$，从而 $p\equiv0$。 左侧 PML 只需反向参数化区间。同样结论适用于 $r$。 在 $r=0$ 的边层，点态 $(u,\lambda_x)$ 耗散矩阵的 $u^2$ 系数为零，半正定性更直接要求 $p'=0$。 因此式 (4.4) 只能用于远离零界面的正角子域，不能用来覆盖常用的连续起步剖面。 这是否定该充分条件的全域适用性，不是否定所有可能能量。

<a id="sec:data"></a>

## 5　新的全域结构与相容能量空间

### 5.1　域尺度、幅度条件与权重

矩形 Dirichlet Poincaré 常数可取 

<a id="eq:poincare"></a>

$$
C_P^2=\left(\frac{\pi^2}{L_x^2}+\frac{\pi^2}{L_y^2}\right)^{-1},
 \qquad \|v\|^2\le C_P^2\|\nabla v\|^2\quad(v\in H_0^1(\Omega)).
\tag{5.1}
$$

 证明只需对 $x,y$ 的一维零端点 Wirtinger 不等式分别积分再相加；一般 $H_0^1$ 函数由密度推广。 定义 

<a id="eq:constants"></a>

$$
A=\epsilon+2\kappa,\qquad K=8\mu A C_P^2,
 \qquad
 c_* =\min\left\{K^{-1/2},\frac{\kappa\tau}{8AK},\frac{\kappa}{8A\tau}\right\}>0.
\tag{5.2}
$$

 本稿的附加条件为 

<a id="eq:smallness"></a>

$$
0<c\le c_*,\qquad
 S:=\max\{\|p\|_\infty,\|r\|_\infty\}\le c/4.
\tag{5.3}
$$

 可固定 $c=c_*$，因此条件完全由材料、域和吸收幅度决定，独立于解。 $K$ 的量纲为时间平方，$c$ 的量纲为时间的倒数。 立即有 

<a id="eq:consequences"></a>

$$
a\le c/2,\quad b\le c^2/16,\quad ac-b\ge0,\quad
 c^2K\le1,\quad c\tau\le\frac{\kappa}{8A}<\frac1{16}<\frac14.
\tag{5.4}
$$

 其中 $b\le a^2/4$ 且 $a\le c/2$ 蕴含 $ac-b\ge0$。

定义新的辅助权重 

<a id="eq:weights"></a>

$$
w_x=\frac{c-r}{a},\quad w_y=\frac{c-p}{a}\quad\text{于 }\Omega_+;
 \qquad w_x=w_y=0\quad\text{于 }Z.
\tag{5.5}
$$

 在 $\Omega_+$ 上 $w_i\ge3/2\ge1$。它们在零吸收界面附近可能无界；本文不把这点隐去，也不假称对任意 $L^2$ 辅助变量都有限。 定义 Hilbert 空间 

<a id="eq:weighted-space"></a>

$$
L_w^2=\left\{\psi:\psi=0\ \text{于 }Z,\quad
 \|\psi\|_w^2:=\int_{\Omega_+}\sum_iw_i\psi_i^2<\infty\right\}.
\tag{5.6}
$$

 因 $w_i\ge1$，该空间连续嵌入 $L^2(\Omega)^2$。

### 5.2　可检查的初值类及其保持

<a id="def:data"></a>

**定义 5.1** (兼容提升初值类 $\mathfrak C_c$). 原八变量初值属于 $\mathfrak C_c$，指存在 $u_0\in H_0^1(\Omega)$，令 

$$
q_0=\kappa u_0-\tau P_0,\qquad
 \lambda_0=(\mu H_{y0},-\mu H_{x0}),\qquad
 \phi_0=\lambda_0-\nabla u_0,
$$

 满足式 (2.5) 的四个初值约束，且 $\phi_0\in L_w^2$。 主定理还要求所生成的一阶时间导数初值有第 6 节定义的有限图范数，并满足相应 PEC 迹相容。 这些时间导数不是自由数据，而由原 PDE 决定，例如 

$$
P_{t0}=(\kappa E_0-P_0)/\tau,\quad
 \phi_{i,t0}=\sigma_j\partial_i u_0-\sigma_i\lambda_{i0},
$$

 $E_{t0}$ 由式 (2.1) 第一式计算。

该定义特别要求物理零吸收区 $\lambda_0=\nabla u_0$，以及 $u_0$ 零边界迹。 它是实质性的初值限制，不只是给全部八变量状态重新命名；例如任意磁静态背景或带磁荷数据未必属于此类。

五个不变量已证明保持。$E$ 的 PEC 迹与式 (2.3) 保证 $u(t)$ 零迹。 在 $Z$ 上 $\phi_t=0$，因此 $\phi_0=0$ 保持。 辅助 ODE 的显式公式是 

<a id="eq:memory-formula"></a>

$$
\phi_i(t)=e^{-\sigma_i t}\phi_{i0}
 +(\sigma_j-\sigma_i)\int_0^te^{-\sigma_i(t-s)}\partial_i u(s)\,\mathrm ds.
\tag{5.7}
$$

 由于 $w_i(\sigma_j-\sigma_i)^2\le ca\le2cS$，得到 

<a id="eq:weighted-preservation"></a>

$$
\|\phi(t)\|_w^2\le2\|\phi_0\|_w^2
 +4cSt\int_0^t\|\nabla u(s)\|^2\,\mathrm ds.
\tag{5.8}
$$

 此外 $w_i\sigma_i^2\le cS$、$w_i\sigma_j^2\le cS$，故 

$$
\|\phi_t\|_w^2\le2cS(\|\nabla u\|^2+\|\lambda\|^2).
$$

 对时间微分后的 ODE 同样适用。因此在本文足够正则解的类中，兼容条件与所需的加权可积性保持。 式 (5.8) 只用于确认空间定义与演化相容，并非用有限时间 Gronwall 冒充最终单调结论。

这个初值类是无限维且包含常见非零启动。取任意 $f,g,\psi\in C_c^\infty(\Omega_{\rm phys})$，令 

<a id="eq:common-data"></a>

$$
E_0=f,\quad P_0=g,\quad
 H_{y0}=\psi_x/\mu,\quad H_{x0}=-\psi_y/\mu,\quad
 u_0=\psi,\quad q_0=\kappa\psi-\tau g,\quad\phi_0=0.
\tag{5.9}
$$

 原四个 PML 辅助初值均为零。$P_0$ 可以为零，也可以等于 $\kappa E_0$，或为任意上述紧支极化脉冲；$H_0$ 是通常的无散紧支磁场脉冲族。 所有有限阶初始空间/时间迹条件对这样的光滑紧支数据均有自然意义。 这里陈述的是非平凡的可容许初始数据族，不借此声称已证明它们的全局解存在。

### 5.3　原函数规范的唯一性

若同一个原八变量状态有两个满足定义 5.1 的提升，两者之差可写为 

$$
u\mapsto u+g,\quad q\mapsto q+\kappa g,\quad
 \phi\mapsto\phi-\nabla g,
$$

 其中 $g$ 与时间无关，$g\in H_0^1(\Omega)$。 原变量重构与 $\phi=0$ 于 $Z$ 要求 

$$
bg=0,\qquad p\partial_yg=0,\qquad r\partial_xg=0,\qquad
 \nabla g=0\ \text{于 }Z.
$$

 对几乎处处满足 $p(x)>0$ 的垂直切片，$\partial_yg=0$，而切片两端零迹，故 $g=0$ 于该切片。 对 $r(y)>0$ 的水平切片同理。于是 $g=0$ 于 $\Omega_+$；Sobolev 函数在其零水平集上的弱梯度几乎处处为零，再结合 $Z$ 上的梯度条件，得 $\nabla g=0$ 于整个域。 $H_0^1$ 的 Poincaré 不等式给出 $g=0$。 所以本类中的提升没有未固定的原函数规范自由度。能量并未沿任意不可观察的规范方向取值。

<a id="sec:energy"></a>

## 6　V7 能量和主定理

对满足 

<a id="eq:tuple"></a>

$$
z_t=R,\qquad z+\tau R=\kappa v,\qquad \Lambda=\nabla v+\psi
\tag{6.1}
$$

 的四元组 $U=(v,R,z,\psi)$，定义 

<a id="eq:Fc"></a>

$$
\begin{aligned}
 \mathcal F_c[U]=\frac12\int_\Omega\Big\{&
 \mu\epsilon\big[v_t^2+2cvv_t+(b+ac)v^2\big]
 +|\Lambda|^2+\sum_iw_i\psi_i^2\\
 &+\frac\mu\kappa\big[(1+(a+c)\tau)R^2+2(c+b\tau)Rz
 +(ac+b(1+c\tau))z^2\big]\Big\}\,\mathrm dx\,\mathrm dy.
\end{aligned}
\tag{6.2}
$$

 在 $\psi=0$ 的 $Z$ 上，$\sum_iw_i\psi_i^2$ 按零定义。 $\mathcal F_c$ 的每个点态时间块不必独立正定；其全域正定性使用约束 (6.1) 与 Poincaré，不是遗漏交叉项。

定义两层状态 

<a id="eq:layers"></a>

$$
U_0=(u,P,q,\phi),\qquad
 U_1=(u_t,P_t,q_t,\phi_t)=(E,P_t,P,\phi_t),
\tag{6.3}
$$

 相应通量为 $\Lambda_0=\lambda$、$\Lambda_1=\lambda_t$。 它们满足同一个 primitive 型系统，因为所有系数与时间无关。 定义 

<a id="eq:E7"></a>

$$
\boxed{\mathcal E_7(t)=\mathcal F_c[U_0(t)]+K\mathcal F_c[U_1(t)].}
\tag{6.4}
$$

 这是局部时间状态与必要历史的能量。$u,q$ 可由式 (2.3) 的已有历史计算； $E_t,P_t,\lambda_t,\phi_t$ 由当前原变量和空间导数计算，不需要未来解。 常数 $c,K$ 只依赖模型参数与域尺度。

为准确陈述范数，令 

<a id="eq:N"></a>

$$
N(U)^2=\mu\epsilon\|v_t\|^2+\frac\mu\kappa\|R\|^2
 +\|\Lambda\|^2+\|\psi\|_w^2,\qquad N_j=N(U_j).
\tag{6.5}
$$

 空间约束为 $v\in H_0^1(\Omega)$、$\psi\in L_w^2$、$v_t,R\in L^2$，$z=\kappa v-\tau R$。 在这个约束空间上 $N$ 是范数，因为 $\nabla v=\Lambda-\psi$ 且 $v$ 零迹；$N=0$ 蕴含全部约束变量为零。 $N_0^2+KN_1^2$ 是本文的一阶加权图范数平方，不是裸八变量 $L^2$ 范数。

<a id="thm:main"></a>

**定理 6.1** (小幅度分离变系数下的全域单调能量). 设域、材料与系数满足第 1 节及式 (5.3)。 设原八变量解满足 PEC，初值属于 $\mathfrak C_c$，提升后的解在 $[0,T]$ 上足够正则。 一组充分的正则性为 

<a id="eq:regularity"></a>

$$
\begin{aligned}
 &u\in C^2([0,T];H_0^1(\Omega))\cap C^3([0,T];L^2(\Omega)),\\
 &P\in C^2([0,T];L^2(\Omega)),\qquad
 \phi\in C^2([0,T];L_w^2),\\
 &\lambda\in C^1([0,T];H(\mathop{\mathrm{div}};\Omega)),
 \qquad q=\kappa u-\tau P,
\end{aligned}
\tag{6.6}
$$

 并满足式 (2.6)。 那么能量 (6.4) 非负，并有 

<a id="eq:equivalence"></a>

$$
\frac14(N_0^2+KN_1^2)\le\mathcal E_7\le N_0^2+KN_1^2.
\tag{6.7}
$$

 令 $\mathscr S[U]$ 由式 (7.2) 定义，$\mathscr S_j=\mathscr S[U_j]$。 则存在第 7 节显式定义的 $\mathcal D_7$，满足 

<a id="eq:main-diss"></a>

$$
\mathcal E_7'=-\mathcal D_7,\qquad
 \mathcal D_7\ge\frac12(\mathscr S_0+K\mathscr S_1)
 +\frac{\mu\tau}{4\kappa}\big(\|P_t\|^2+K\|P_{tt}\|^2\big)\ge0.
\tag{6.8}
$$

 因而对所有 $0\le t_1\le t_2\le T$， 

<a id="eq:main-balance"></a>

$$
\mathcal E_7(t_2)+\int_{t_1}^{t_2}\mathcal D_7(t)\,\mathrm dt=\mathcal E_7(t_1),
 \qquad \mathcal E_7(t_2)\le\mathcal E_7(t_1).
\tag{6.9}
$$

 能量直接控制原电磁场和极化： 

<a id="eq:physicalcontrol"></a>

$$
\epsilon\|E\|^2+\mu(\|H_x\|^2+\|H_y\|^2)+\kappa^{-1}\|P\|^2
 \le\frac4\mu\mathcal E_7.
\tag{6.10}
$$

 以上常数不依赖 $T$、吸收梯度或吸收的正下界。

正则性 (6.6) 是保证全部求导与 Green 公式合法的充分条件，不声称是最低要求。 本定理是已存在的足够正则解的先验定理；未在这里另证强解/弱解存在性、唯一性或正则性传播。 若解存在于所有 $t\ge0$，则式 (6.9) 对任意两个非负时刻成立。

<a id="sec:identity"></a>

## 7　能量求导：完整局部恒等式及所有边界项

### 7.1　常数移位的空间恒等式

对于一层 $U=(v,R,z,\psi)$，记 $h=\partial_i v$、$V=\partial_i v_t$、$l=\Lambda_i$、$f=\psi_i=l-h$。 辅助方程给出 

$$
f_t=\sigma_jh-\sigma_i l,\qquad l_t=V+\sigma_jh-\sigma_i l.
$$

 在 $a>0$ 处，完整展开为 

<a id="eq:spatialidentity"></a>

$$
\begin{aligned}
 \frac12\partial_t(l^2+w_if^2)
 &=lV+(l+w_i(l-h))(\sigma_jh-\sigma_i l)\\
 &=(V+ch)l-\frac{\sigma_i(c+\sigma_i)}a l^2
              -\frac{\sigma_j(c-\sigma_j)}a h^2.
\end{aligned}
\tag{7.1}
$$

 使用的等式是 $\sigma_j+aw_i=c$。 在 $Z$ 上 $f=0,l=h$，因而同一恒等式写成 

$$
\frac12\partial_t|\nabla v|^2
 =(\nabla v_t+c\nabla v)\cdot\nabla v-c|\nabla v|^2.
$$

 由此定义全域非负空间耗散 

<a id="eq:spatialdiss"></a>

$$
\begin{aligned}
 \mathscr S[U]={}&\int_{\Omega_+}\sum_{i\in\{x,y\}}
 \left[\frac{\sigma_i(c+\sigma_i)}a\Lambda_i^2
       +\frac{\sigma_j(c-\sigma_j)}a(\partial_i v)^2\right]\,\mathrm dx\,\mathrm dy\\
 &+\int_Zc|\nabla v|^2\,\mathrm dx\,\mathrm dy,\qquad j\ne i.
\end{aligned}
\tag{7.2}
$$

 此处的耗散权重是有界的，尽管能量权重 $w_i$ 可无界。 加权空间的时间链式法则由 $\psi\in C^1(L_w^2)$ 保证。 计算未对 $w_i,p,r$ 作空间微分。

### 7.2　电块与 Debye 块的完整恒等式

电块为 

<a id="eq:electric-identity"></a>

$$
\begin{aligned}
 \epsilon(v_{tt}+av_t+bv)(v_t+cv)
 ={}&\frac\epsilon 2\partial_t\big[v_t^2+2cvv_t+(b+ac)v^2\big]\\
 &+\epsilon\big[(a-c)v_t^2+bcv^2\big].
\end{aligned}
\tag{7.3}
$$

 由式 (6.1) 得 

$$
\kappa(v_t+cv)=\tau R_t+(1+c\tau)R+cz.
$$

 将右侧与 $R_t+aR+bz$ 相乘，并用 $z_t=R$，得到 

<a id="eq:polaridentity"></a>

$$
\begin{aligned}
 &(R_t+aR+bz)(v_t+cv)\\
 &=\frac1{2\kappa}\partial_t\Big[(1+(a+c)\tau)R^2
       +2(c+b\tau)Rz+(ac+b(1+c\tau))z^2\Big]\\
 &\hspace{5mm}+\frac1\kappa\Big[\tau R_t^2+
       (a-c+\tau(ac-b))R^2+bcz^2\Big].
\end{aligned}
\tag{7.4}
$$

 例如右侧导数的 $R_tz$ 系数是 $(c+b\tau)/\kappa$，$R^2$ 系数包含由 $Rz$ 求导得到的 $(c+b\tau)/\kappa$；扣除它才产生耗散系数中的 $-c-b\tau$。 因此 $ac-b$ 的符号和 $c$ 的系数并非从 V6 直接猜测。

### 7.3　Green 公式和精确的两层耗散

一层主方程是 

$$
\mu[\epsilon(v_{tt}+av_t+bv)+R_t+aR+bz]=\mathop{\mathrm{div}}\Lambda.
$$

 乘以 $v_t+cv$，有 

<a id="eq:green"></a>

$$
\int_\Omega(v_t+cv)\mathop{\mathrm{div}}\Lambda
 =-\int_\Omega(\nabla v_t+c\nabla v)\cdot\Lambda
   +\left\langle v_t+cv,\Lambda\cdot n\right\rangle_{\partial\Omega}.
\tag{7.5}
$$

 这是 $H_0^1$ 与 $H(\mathop{\mathrm{div}})$ 的 Green 公式；光滑情形下边界配对就是通常曲面积分。 由式 (7.1)--(7.4) 得 

<a id="eq:Fcderivative"></a>

$$
\mathcal F_c[U]'=-\mathcal D_c[U]+\left\langle v_t+cv,\Lambda\cdot n\right\rangle_{\partial\Omega},
\tag{7.6}
$$

 其中 

<a id="eq:Dc"></a>

$$
\begin{aligned}
 \mathcal D_c[U]=\mathscr S[U]
 &+\mu\epsilon\int_\Omega[(a-c)v_t^2+bcv^2]\,\mathrm dx\,\mathrm dy\\
 &+\frac\mu\kappa\int_\Omega[\tau R_t^2+(a-c+\tau(ac-b))R^2+bcz^2]\,\mathrm dx\,\mathrm dy.
\end{aligned}
\tag{7.7}
$$

 **单层 $\mathcal D_c$ 一般不是非负的**；不能到这里就宣告完成定理。 由于 $c$ 是常数，式 (7.5) 没有 $v\nabla a$ 余项。这是对 V6 主要障碍的结构性消除，而非估计时漏掉梯度。

对 $U_0$，$v=u,v_t=E$ 零迹；对 $U_1$，$v=E,v_t=E_t$ 零迹。 后者由强解 PEC 的时间可微性保证。 因此两层外边界通量都为零；对全域直接积分不产生内部边界。 若分区积分，共面上 $(v_t+cv)$ 的单值迹及 $\Lambda_j\in H(\mathop{\mathrm{div}})$ 的法向迹使两项逐面对消。 所以 

<a id="eq:D7exact"></a>

$$
\mathcal D_7=\mathcal D_c[U_0]+K\mathcal D_c[U_1],\qquad \mathcal E_7'=-\mathcal D_7.
\tag{7.8}
$$

<a id="sec:coercivity"></a>

## 8　全域正定性与原状态控制的证明

由 $z=\kappa v-\tau R$，极化二次型可精确重写为 

<a id="eq:reduced-polar"></a>

$$
A_RR^2+2\kappa c(1-a\tau-b\tau^2)vR+\kappa^2Gv^2,
\tag{8.1}
$$

 其中 

$$
A_R=1+(a-c)\tau+(ac-b)\tau^2+bc\tau^3,
 \qquad G=ac+b(1+c\tau).
$$

 由式 (5.4) 的较宽条件 $c\tau\le1/4$，逐项可验 

<a id="eq:ARbounds"></a>

$$
\frac34\le A_R\le\frac54,\qquad
 0\le1-a\tau-b\tau^2\le1,
 \quad 0\le G\le\frac{37}{64}c^2,
 \quad 0\le b+ac\le\frac9{16}c^2.
\tag{8.2}
$$

 例如 $A_R\ge1-c\tau$；上界可丢弃 $(a-c)\tau\le0$，再用 $ac\tau^2\le(c\tau)^2/2$、$bc\tau^3\le(c\tau)^3/16$。

令 $B_{\rm sp}=\|\Lambda\|^2+\|\psi\|_w^2$。 由 $w_i\ge1$、$\psi=0$ 于 $Z$ 和 $\nabla v=\Lambda-\psi$， 

<a id="eq:spcontrols"></a>

$$
\|\nabla v\|^2\le2B_{\rm sp},\qquad
 \|v\|^2\le2C_P^2B_{\rm sp}.
\tag{8.3}
$$

### 8.1　下界

Young 不等式给出 

$$
|2\mu\epsilon c(v,v_t)|\le\tfrac12\mu\epsilon\|v_t\|^2
                              +2\mu\epsilon c^2\|v\|^2,
$$

 

$$
|2\mu c((1-a\tau-b\tau^2)v,R)|
 \le\tfrac14\mu\kappa^{-1}\|R\|^2+4\mu\kappa c^2\|v\|^2.
$$

 丢弃非负的 $v^2$ 对角项后，由式 (8.2) 得 

$$
2\mathcal F_c[U]\ge\tfrac12\mu\epsilon\|v_t\|^2+\tfrac12\mu\kappa^{-1}\|R\|^2
              +B_{\rm sp}-2\mu A c^2\|v\|^2.
$$

 而 

$$
2\mu A c^2\|v\|^2\le4\mu A c^2C_P^2B_{\rm sp}
  =\tfrac12Kc^2B_{\rm sp}\le\tfrac12B_{\rm sp}.
$$

 所以 $\mathcal F_c[U]\ge N(U)^2/4$。

### 8.2　上界

电交叉项使用相同估计，极化交叉项改用 

$$
|2\mu c((1-a\tau-b\tau^2)v,R)|
 \le\tfrac12\mu\kappa^{-1}\|R\|^2+2\mu\kappa c^2\|v\|^2.
$$

 由式 (8.2)， 

$$
2\mathcal F_c[U]\le2\mu\epsilon\|v_t\|^2+2\mu\kappa^{-1}\|R\|^2
       +B_{\rm sp}+3\mu(\epsilon+\kappa)c^2\|v\|^2.
$$

 最后一项不超过 $6\mu(\epsilon+\kappa)c^2C_P^2B_{\rm sp}
 \le3(\epsilon+\kappa)B_{\rm sp}/(4A)<B_{\rm sp}$， 故 $\mathcal F_c[U]\le N(U)^2$。 分别用于两层即证式 (6.7)。

### 8.3　原八变量的具体控制

$\lambda=(\mu H_y,-\mu H_x)$ 和 $N_0^2\le4\mathcal E_7$ 立即给出式 (6.10)。 其余变量并未遗失： 

<a id="eq:auxcontrol1"></a>

$$
\|u\|^2\le8C_P^2\mathcal E_7,\qquad \|\phi\|^2\le4\mathcal E_7,
\tag{8.4}
$$

<a id="eq:auxcontrol2"></a>

$$
\|q\|^2\le\left(16\kappa^2C_P^2+\frac{8\kappa\tau^2}{\mu}\right)\mathcal E_7,
\tag{8.5}
$$

<a id="eq:auxcontrol3"></a>

$$
\|Z_1\|^2\le8\epsilon^2S^4C_P^2\mathcal E_7,
\tag{8.6}
$$

<a id="eq:auxcontrol4"></a>

$$
\|Z_2\|^2\le S^4\left(16\kappa^2C_P^2+\frac{8\kappa\tau^2}{\mu}\right)\mathcal E_7,
\tag{8.7}
$$

<a id="eq:auxcontrol5"></a>

$$
\|Q_x\|^2+\|Q_y\|^2\le4S^2\mathcal E_7.
\tag{8.8}
$$

 这些由 $q=\kappa u-\tau P$、$b\le S^2$ 及式 (2.5) 逐项推出。 不存在能量漏掉一个实际增长的原状态分量的情形。 相反的裸八变量 $L^2$ 上界没有在本文证明，也不被声称成立；能量定义确实要求历史/图范数正则性。

<a id="sec:closing"></a>

## 9　关键闭合：用导数层和 Debye 耗散控制边层

### 9.1　单层耗散的可用下界

由 $R=\kappa v_t-\tau R_t$、$ac-b\ge0$， 

$$
\begin{aligned}
 \mathcal D_c[U]&\ge\mathscr S[U]+\frac{\mu\tau}{\kappa}\|R_t\|^2
                     -\mu c\epsilon\|v_t\|^2-\frac{\mu c}{\kappa}\|R\|^2\\
 &\ge\mathscr S[U]+\frac{\mu\tau}{\kappa}(1-2c\tau)\|R_t\|^2
                     -\mu c(\epsilon+2\kappa)\|v_t\|^2\\
 &\ge\mathscr S[U]+\frac{\mu\tau}{2\kappa}\|R_t\|^2-\mu cA\|v_t\|^2.
\end{aligned}
$$

 这里使用 $c\tau\le1/4$。于是由式 (7.8)， 

<a id="eq:D7pre"></a>

$$
\begin{aligned}
 \mathcal D_7\ge\mathscr S_0+K\mathscr S_1
 +\frac{\mu\tau}{2\kappa}(\|P_t\|^2+K\|P_{tt}\|^2)
 -\mu cA\|E\|^2-\mu cAK\|E_t\|^2.
\end{aligned}
\tag{9.1}
$$

 剩余两个负项必须真正处理，不能列为附加的未证假设。

### 9.2　PDE 相容关系提供跨边层的全域空间估计

在 $\Omega_+$ 上设 $\theta_i=\sigma_i/a$；在 $Z$ 上设 $\theta_x=\theta_y=1/2$。 注意此处是用于证明的另一组分配权重，与 V6 的零延拓约定没有冲突。 定义 

<a id="eq:J"></a>

$$
J(U)=\int_\Omega\sum_i[\theta_i\Lambda_i^2+\theta_j(\partial_iv)^2]\,\mathrm dx\,\mathrm dy,
 \qquad j\ne i.
\tag{9.2}
$$

 在 $Z$ 上 $\Lambda=\nabla v$，故该密度正好为 $|\nabla v|^2$。 由式 (7.2)， 

<a id="eq:SJ"></a>

$$
\mathscr S[U]\ge(c-S)J(U)\ge\frac{3c}4J(U).
\tag{9.3}
$$

原辅助演化给出精确的关系 

<a id="eq:gradientE"></a>

$$
\partial_iE=\lambda_{i,t}-\sigma_j\partial_i u+\sigma_i\lambda_i.
\tag{9.4}
$$

 将 $|\partial_iE|^2$ 分成 $\theta_i$ 与 $\theta_j$ 两部分，对前者使用式 (9.4) 和平方和不等式，得 

$$
\begin{aligned}
 \int\theta_i|\partial_iE|^2
 &\le3\int\theta_i|\lambda_{i,t}|^2
 +3\int\theta_i\sigma_j^2|\partial_i u|^2
 +3\int\theta_i\sigma_i^2|\lambda_i|^2.
\end{aligned}
$$

 在 $\Omega_+$ 上 $\theta_i\sigma_j^2=\sigma_i\sigma_j\theta_j\le S^2\theta_j$， $\theta_i\sigma_i^2\le S^2\theta_i$；在 $Z$ 上两个吸收项为零。 第二部分 $\int\theta_j|\partial_iE|^2$ 本身包含在 $J(U_1)$ 中。 逐分量相加得到关键不等式 

<a id="eq:globalgradient"></a>

$$
\boxed{\|\nabla E\|^2\le3J(U_1)+3S^2J(U_0).}
\tag{9.5}
$$

 它利用的是整个 PDE 的状态关系，不要求一个点态矩阵控制全部互相独立的 $(u,\lambda)$。

结合 PEC 的 Poincaré 及式 (9.3)， 

<a id="eq:absorbE"></a>

$$
\begin{aligned}
 \mu cA\|E\|^2
 &\le3\mu cAC_P^2[J(U_1)+S^2J(U_0)]\\
 &\le4\mu AC_P^2(\mathscr S_1+S^2\mathscr S_0)
 =\frac K2(\mathscr S_1+S^2\mathscr S_0).
\end{aligned}
\tag{9.6}
$$

 $KS^2\le Kc^2/16\le1/16\le1$，因此这一项至多消耗 $\mathscr S_0$ 的一半以及 $K\mathscr S_1$ 的一半。

### 9.3　Debye 耗散吸收最高时间项

Debye 方程的时间导数为 $\kappa E_t=P_t+\tau P_{tt}$，从而 

$$
\mu cAK\|E_t\|^2
 \le\frac{2\mu cAK}{\kappa^2}\|P_t\|^2
       +\frac{2\mu cAK\tau^2}{\kappa^2}\|P_{tt}\|^2.
$$

 式 (5.2) 中的两个材料条件逐一给出 

$$
c\le\frac{\kappa\tau}{8AK}
 \ \Longrightarrow\ \frac{2\mu cAK}{\kappa^2}\le\frac{\mu\tau}{4\kappa},
$$

 

$$
c\le\frac{\kappa}{8A\tau}
 \ \Longrightarrow\ \frac{2\mu cAK\tau^2}{\kappa^2}\le\frac{K\mu\tau}{4\kappa}.
$$

 故 

<a id="eq:absorbEt"></a>

$$
\mu cAK\|E_t\|^2\le\frac{\mu\tau}{4\kappa}
                 (\|P_t\|^2+K\|P_{tt}\|^2).
\tag{9.7}
$$

 将式 (9.6)、(9.7) 代回式 (9.1)，便得到 

$$
\mathcal D_7\ge\tfrac12(\mathscr S_0+K\mathscr S_1)
     +\frac{\mu\tau}{4\kappa}(\|P_t\|^2+K\|P_{tt}\|^2)\ge0.
$$

 连同第 8 节的正定性和式 (7.8)，定理 6.1 得证。 积分得到任意两个时刻的式 (6.9)；没有人为乘以 $e^{-Ct}$，也没有假定未来积分收敛。

<a id="sec:example"></a>

## 10　满足全部条件的二维 PML 配置

取无量纲参数 $\epsilon=\mu=\kappa=\tau=1$，整个域及物理区为 

$$
\Omega=(-1,1)^2,\qquad\Omega_{\rm phys}=(-1/2,1/2)^2.
$$

 于是 $C_P^2=2/\pi^2$、$A=3$、$K=48/\pi^2$，而 

$$
c_* =\min\left\{\frac\pi{\sqrt{48}},\frac{\pi^2}{1152},\frac1{24}\right\}
 =\frac{\pi^2}{1152}\approx0.00856736.
$$

 选择 

<a id="eq:exampleconstants"></a>

$$
c=1/128=0.0078125,\qquad 0<\eta_x,\eta_y\le1/512=c/4.
\tag{10.1}
$$

 对任意整数 $m\ge2$，令 

<a id="eq:profiles"></a>

$$
\boxed{p(x)=\eta_x[2(|x|-1/2)_+]^m,\qquad
 r(y)=\eta_y[2(|y|-1/2)_+]^m.}
\tag{10.2}
$$

 在所给计算域内方括号值在 $[0,1]$，所以幅度正好不超过 $1/512$。 物理区 $p=r=0$；四个边条只有一个系数为正；四个角方块两个系数都为正。 它们在内界面从零连续起步，属于 $W^{1,\infty}$；$m=2$ 是常用的二次型起步。 正吸收区的最大斜率为 $2m\eta_i$，但主定理并不使用这个斜率上界的大小。

严格的参数检查为 

$$
Kc^2=\frac{3}{1024\pi^2}<1,\quad KS^2\le\frac{3}{16384\pi^2}<1,
$$

 

$$
\frac{8cAK}{\kappa\tau}=\frac9{\pi^2}<1,\qquad
 \frac{8cA\tau}{\kappa}=\frac3{16}<1.
$$

 因此本配置确实满足全部闭合条件，不是只给出一个无法实现的抽象吸收假设。 原文量纲下应取 $\sigma_x^{\rm old}=\epsilon_0p$、$\sigma_y^{\rm old}=\epsilon_0r$。

更一般地，层厚 $\ell_i>0$ 的剖面可取 $\eta_i(\operatorname{dist}(x_i,I_{i,\rm phys})/\ell_i)^m$，截断外边界对应距离 $\ell_i$。 取 $0<\eta_i\le c/4$ 即可，梯度为至多 $m\eta_i/\ell_i$。 改变整个域的长度时必须重新计算 $C_P,K,c_*$。 这一充分条件相当保守；小幅度保证的是本定理的数学耗散，不自动保证给定层厚下高效吸收或很小的外边界反射。

<a id="sec:failures"></a>

## 11　主要候选的失败原因与静态模态

### 11.1　仅把 $a$ 换成常数 $c$ 仍然不够

单层精确导数已在式 (7.7) 给出，其两个 $a-c$ 系数在物理区为负。 这不是纯粹的自由代数方向：取第 5 节的实际兼容初值 

$$
u_0=0,\quad H_0=0,\quad\phi_0=0,\quad E_0=f,\quad P_0=\kappa f,
 \quad q_0=-\tau\kappa f,
$$

 其中非零 $f\in C_c^\infty(\Omega_{\rm phys})$，原 PML 辅助变量全部为零。 原 PDE 决定 $P_{t0}=E_{t0}=0$，故 

$$
\mathcal D_c[U_0](0)=-\mu c(\epsilon+\kappa)\|f\|^2<0.
$$

 因此任何通过该初值的足够正则解均有 $\mathcal F_c[U_0]'(0)>0$。 另一方面 $\lambda_t(0)=\nabla f$，导数层产生 $\mathscr S_1(0)=c\|\nabla f\|^2$，正是 Poincaré 可以利用的缺失控制。 这说明 V7 的增益来自导数层耦合和 Debye 耗散，而不是单个乘子巧合。

### 11.2　V6 椭圆修正的完整导数仍不直接抵消

为核对一个主要非局部候选，设 $\mathcal L:H_0^1(\Omega)\to H^{-1}(\Omega)$ 由固定的有界强椭圆双线性型 

$$
B(z,v)=\int_\Omega C\nabla z\cdot\nabla v+d zv,
 \qquad C=C^T\ge c_0I,\ d\ge0
$$

 定义。令 $z=\mathcal L^{-1}\mathop{\mathrm{div}}(u\nabla a)$，即 $B(z,v)=-\int u\nabla a\cdot\nabla v$，从而 $z_t=\mathcal L^{-1}\mathop{\mathrm{div}}(E\nabla a)$。 对候选 

$$
F=\eta(\lambda,\nabla z)+\frac\eta2B(z,z)
$$

 完整求导得 

<a id="eq:nonlocalfail"></a>

$$
F'=\eta\big[(\lambda_t,\nabla z)+(\lambda-u\nabla a,\nabla z_t)\big].
\tag{11.1}
$$

 因此 $\mathcal E_B+F$ 的导数仍含 $-(u\nabla a,\lambda)$，并新增 $\lambda_t,z_t$ 两项，不能声称直接抵消。 该公式不排除另加结构或不等式后此类修正可能成功；本文不据此作不存在性断言。 本次采用已经闭合的局部时间导数层路线，不使用未证半群稳定性或未来 Gramian。

### 11.3　静态方向没有通过零能量被掩盖

式 (6.10) 不要求耗散对全部状态严格正定。 若本初值类中存在静态解，它仍具有真实的正能量，单调是允许能量保持常数的。 例如在定理允许的单轴退化情形 $r\equiv0$，取 $F\in C_c^\infty(\{x:p(x)>0\})$，支集远离 $p=0$，并令 

$$
u=E=P=q=0,\quad \lambda=(0,F(x)),\quad\phi=\lambda,
 \quad H_x=-F(x)/\mu,\quad H_y=0,\quad Q_x=pF,
$$

 其余辅助变量为零。这是满足原方程与本兼容类的非零静态状态，且 

$$
\mathcal E_7=\frac12\int_\Omega\frac c{p(x)}F(x)^2\,\mathrm dx\,\mathrm dy>0,
 \qquad\mathcal D_7=0.
$$

 所以证明没有借用必然指数衰减或某个可能发散的 Gramian，也没有把该静态磁场当作规范零方向。 本兼容类之外的磁静态背景没有被本定理覆盖，不能未经另证就加入原场并宣称同一定理成立。

<a id="sec:literature"></a>

## 12　与外部文献的模型和定理范围核对

本稿主定理的全部闭合估计均在上文证明，不调用外部 PML 稳定性定理。 以下仅定位方法来源和避免模型错配；不将题名中的 "stability" 自动解释为本题要求的全域单调能量。

**Baffet--Grote--Imperiale--Kachanovska (2019).**

核对上传包所含原论文的 HAL v2（2019-11-15）。其正文第 4 页明确为能量分析假设阻尼在整个所分析域中为常数； 外边界条件见 (2.2)，为 $u=0$ 或 $\partial_\nu u+\phi\cdot\nu=0$。 二维方程是 (2.3)，无 Debye 变量；正文第 5--6 页 Theorem 2.1 与 (2.4)--(2.9) 给出常阻尼单调能量。 PDF 多一页 HAL 封面，所以这些对应 PDF 第 5--7 页。 不能将这个定理直接作为本题物理区--边层--角层连续变剖面的定理。 出版社摘要也明确限定 constant damping coefficients[1]。

**Bécache--Kachanovska--Wess (2023).**

核对上传的正式发表 PDF，ESAIM:M2AN 57, 2451--2491。 第 2456--2458 页 (7)--(15) 是半无限波导的单轴 $x$ 向 PML，$\sigma\in L^\infty$ 且物理区为零，拉伸含材料相关函数 $\zeta(s)$； 电场为二维向量、磁场为标量，PEC 写为切向电场零，标量消元后为 Neumann 条件。 Assumptions 2.9--2.10 指定初值支集和可容许材料/拉伸函数；第 2459 页 Theorem 2.11 是物理波导区的截断误差收敛估计，并非本八变量双轴角层系统的显式瞬时单调能量[2]。 作者网页还列有该文与 2021 波导论文的勘误链接；本次访问该勘误 PDF 失败，因此不引用原文定理中的精细指数常数作为已核准结论，更不依赖它闭合本证明。

**Ludvigsson--Duru--Kreiss (arXiv:2206.08507v1, 2022).**

原文 (1)--(6) 是三维二阶声波方程及反射系数型边界条件，不含 Debye 极化。 第 9 页 Theorem 1 在 Laplace 空间对变系数 PML 给出估计，明确要求 $\Re s>\beta$，其中 $\beta$ 含 $\max\sqrt{\kappa/\rho}|d_i'/d_i|$。 第 11 页正文也指出其直接时域转换给出指数增长型界，不能由此证明相应渐近稳定性。 因此该结果既不能替代本题的 $\mathcal E'\le0$，也不能未经处理就覆盖 $d_i$ 从零起步时可能无界的对数梯度[3]。 本稿没有声称这些文献否定了其他全域能量结构。

<a id="sec:conclusion"></a>

## 13　V6 到 V7 的准确进展及未完成范围

V6 的有效起点是式 (4.3)；其正角域小梯度定理可保留，但内部角域边界通量非正不是外部 PEC 自动保证的。 V7 首先补齐原八变量、归一化、磁场滤波关系及非零初值，再将主问题从点态吸收 $u\nabla a\cdot\lambda$ 改写为式 (9.1) 中的两个时间负项。 式 (9.5) 与式 (9.7) 分别解决它们。 这条证明在 $a=b=0$、$b=0<a$、$b>0$ 上同时有效；没有用人工拼接代替全域估计。

**已完成的最强结果：**对明确兼容、加权图范数有限的足够正则解，在式 (5.3) 的实际可行小幅度剖面条件下，完成原模型的全域单调能量先验定理、双边范数界和原八变量控制，并给出式 (10.2) 的二维配置。

**尚未完成的范围：任意幅度的一般非负分离变系数下，全域单调能量尚未证明。** 这不是对所有能量形式的不存在性结论。现有证明的具体限制在于， $-\mu cAK\|E_t\|^2$ 必须由 Debye 耗散吸收，导致式 (5.2) 的两个材料小量条件； 同时 $S\le c/4$ 用于辅助权重正性与式 (9.3)。 $\kappa\to0$ 时本条件退化，故不能将主定理无条件取极限成无极化 Maxwell 的结果。 没有在本稿证明分数阶、空间变材料、一般二维依赖系数的严格坐标变换、数值离散或完整适定性。

最值得下一步检验的一条具体路线是：保留常数移位与两层能量，*不先用 $R^2\le2\kappa^2v_t^2+2\tau^2R_t^2$ 丢失关联*，而在 $(E,E_t,P_t,P_{tt})$ 的 Debye 约束子空间上联合优化 $c,K$ 和 Young 参数，求出更大的显式幅度容许区间；同时保留式 (9.5) 的空间 PDE 约束。 这会首先检验当前幅度限制有多少属于保守估计，而不是预设任意幅度结论必然成立。

## A　计算验证的内容与边界

交付的 `verify_v7.py` 已实际运行，使用 SymPy 精确化简验证： 常数移位空间恒等式 (7.1)、电块 (7.3)、Debye 块 (7.4)、 约束消元二次型 (8.1)、V6 极化行列式、两个磁辅助初值不变量，以及二维示例的参数不等式。 结果记录在 `verification_output.txt`。 这些是**代数和参数核验**，不是 PDE 能量定理的机器形式化。 全域 Green 公式、Poincaré、加权空间解释、式 (9.5)、耗散闭合及时间积分均由本文人工证明。 本次未运行 Lean，也没有把 "假设 $\mathcal E'\le0$ 再形式化单调性" 当作核心证明。

## 参考文献

[1] D. H. Baffet, M. J. Grote, S. Imperiale, M. Kachanovska. Energy Decay and Stability of a Perfectly Matched Layer For the Wave Equation. *Journal of Scientific Computing*, 81 (2019), 2237--2270. DOI: [10.1007/s10915-019-01089-9](https://doi.org/10.1007/s10915-019-01089-9). 核对版本：HAL hal-01865484v2，正文 §2.1, Theorem 2.1。

[2] É. Bécache, M. Kachanovska, M. Wess. Convergence analysis of time-domain PMLs for 2D electromagnetic wave propagation in dispersive waveguides. *ESAIM: M2AN*, 57 (2023), 2451--2491. DOI: [10.1051/m2an/2023060](https://doi.org/10.1051/m2an/2023060). 核对范围：§§2.2--2.3, (7)--(15), Assumptions 2.9--2.10, Theorem 2.11。

[3] G. Ludvigsson, K. Duru, G. Kreiss. On energy-stable and high order finite element methods for the wave equation in heterogeneous media with perfectly matched layers. [arXiv:2206.08507v1](https://arxiv.org/abs/2206.08507) (2022). 核对范围：§2, §4, Theorem 1（第 9 页）、其后讨论（第 11 页）。
