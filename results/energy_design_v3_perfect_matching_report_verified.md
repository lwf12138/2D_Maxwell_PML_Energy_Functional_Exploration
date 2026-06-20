<!-- ITERIS VERIFIED: goal_success verify-20260620T141636842186Z-goal_success-read-.iteris-goal_prompt.tx assembly verify-20260620T073403963252Z-assembly-updated-stage-3-terminal-report -->
# Energy Design V3 Perfect Matching Report

Problem id: `2d_maxwell_pml_energy_functional_exploration`

终端 artifact: `results/energy_design_v3_perfect_matching_report.md`

## 1. Executive summary

本阶段回答的问题不是“v2 模型是否有单调能量”。这个问题在
`results/energy_design_v2_report_verified.md` 中已经验证：v2 协变阻尼
Maxwell--Debye 吸收层有正的单调能量。但 stage-3 的新问题是：这个模型是否真的是
perfectly matched layer。

结论如下。

1. v2 协变阻尼模型不是 perfectly matched。对于平面 \(x\)-界面、
\(\rho_x=\rho>0,\rho_y=0\)、Laplace 变量 \(s\) 和切向波数 \(k_y\)，物理
Maxwell--Debye 导纳 \(Y_0\) 与 v2 透射导纳 \(Y_{v2}\) 满足
\[
Y_{v2}^2-Y_0^2
=-\frac{\rho}{\mu^2}\left[
\frac{\mu\chi\tau}{(1+\tau s)(1+\tau(s+\rho))}
+\frac{k_y^2}{s^2(s+\rho)}
\right],
\]
所以反射系数
\[
R_{v2}=\frac{Y_0-Y_{v2}}{Y_0+Y_{v2}}
\]
通常不为零。失配有两个来源：Debye 极化率被从
\(\chi/(1+\tau s)\) 改成 \(\chi/(1+\tau(s+\rho))\)，并且斜入射项从
\(k_y^2/s^2\) 改成 \(k_y^2/[s(s+\rho)]\)。

2. 一个更接近标准 PML 的修复模型是 stretched-coordinate Maxwell--Debye
PML：在 Laplace 域中只把空间导数替换为 \(S_i(s)^{-1}\partial_i\)，同时保持
物理 Debye 定律
\[
(1+\tau s)\widehat P=\chi\widehat E.
\]
该模型在常系数平面界面处满足 \(\nu_+=S_x\nu_0\) 和 \(Y_+=Y_0\)，因此连续层面
perfectly matched。

3. 能量方面必须分开陈述。v2 模型有完整的单调耗散恒等式，但它不是精确匹配
PML。标准 stretched-coordinate 修复模型有精确匹配；其朴素物理能量在完整二维
ADE 形式中有符号不定的记忆耦合项，但引入 Baffet 型 time-primitive 变量
\(u_t=E,q_t=P\) 后，在常系数二维 PML 块上得到正的非增能量
\(\mathcal E_{BD}\) 和耗散恒等式。

4. 全计算区域上的“所有非零态严格衰减”不可能成立。若物理区域内
\(\sigma_x=\sigma_y=0\)，取
\[
E=0,\qquad P=0,\qquad H_x=\partial_x\phi,\qquad H_y=\partial_y\phi,
\]
其中 \(\phi\) 光滑且支撑在未阻尼物理区域内，则
\(\partial_xH_y-\partial_yH_x=0\)，这是非零磁能的定常解。任何诚实的耗散恒等式
都必须刻画这个零耗散空间。

当前最强结论是：v2 是稳定吸收层而不是 perfectly matched PML；标准
stretched-coordinate/Baffet-primitive Maxwell--Debye 模型在常系数二维块上同时给出
perfect matching 与非增耗散能量。下一篇 manuscript 不应把 v2 称为 PML。

## Fact index

| fact id | status | verification |
|---|---:|---|
| `fact:2d_maxwell_pml_energy_functional_exploration:alpha1-algebra-balance` | verified | `verification/results/verify-20260619T180514214437Z-fact-alpha-1-pec-balance-and-shifted-mag.json` |
| `fact:2d_maxwell_pml_energy_functional_exploration:edge-pml-linear-obstruction` | verified | `verification/results/verify-20260619T181255226823Z-fact-the-alpha-1-source-model-has-exact-.json` |
| `fact:2d_maxwell_pml_energy_functional_exploration:augmented-gronwall-energy` | verified | `verification/results/verify-20260619T181650715321Z-fact-a-positive-augmented-zeroth-order-e.json` |
| `fact:2d_maxwell_pml_energy_functional_exploration:covariantly-damped-debye-energy` | verified | `verification/results/verify-20260620T022411192181Z-fact-the-covariantly-damped-alpha-1-maxw.json` |
| `fact:2d_maxwell_pml_energy_functional_exploration:v2-covariant-model-not-perfectly-matched` | verified | `verification/results/verify-20260620T064341474739Z-fact-the-v2-covariantly-damped-maxwell-d.json` |
| `fact:2d_maxwell_pml_energy_functional_exploration:standard-stretched-pml-matching-and-1d-energy` | verified | `verification/results/verify-20260620T064808296793Z-fact-the-standard-stretched-coordinate-m.json` |
| `fact:2d_maxwell_pml_energy_functional_exploration:stretched-coordinate-debye-pml-matching-and-energy-gap` | verified | `verification/results/verify-20260620T065326237995Z-fact-the-standard-stretched-coordinate-m.json` |
| `fact:2d_maxwell_pml_energy_functional_exploration:whole-domain-strict-decay-nullspace-obstruction` | verified | `verification/results/verify-20260620T065810059861Z-fact-strict-decay-of-total-electromagnet.json` |
| `fact:2d_maxwell_pml_energy_functional_exploration:baffet-primitive-stretched-debye-2d-energy` | verified | `verification/results/verify-20260620T072508563237Z-fact-a-baffet-type-time-primitive-standa.json` |

Stage-3 proof artifacts:

- `artifacts/references/stage3_literature_reading_record.md`
- `artifacts/proofs/stage3_v2_perfect_matching_test.md`
- `artifacts/proofs/stage3_repaired_model_energy.md`
- `artifacts/proofs/stage3_baffet_debye_2d_energy.md`

## 2. Literature reading record

PDF 页码为本轮用 `pdfminer` 按页抽取时得到的 PDF 页码。若公式提取不完整，本报告只使用
可读的模型结构或自己重新推导的代数，不引用不可读公式作为证据。

| 文献或文件 | 检查位置 | 读到的相关内容 | 本报告中的用途 |
|---|---|---|---|
| `sources/energy_functional_problem.tex` | 全文，特别是模型与任务段 | 给出原八变量 Maxwell--PML/Cole--Cole 模型、PEC、\(\alpha=1\) Debye 化、旧模型 \(M_x,M_y\) 变量与 fallback 要求。 | 定义旧模型和必须处理的 obstruction。 |
| `results/energy_functional_report_verified.md` | 全文 | 已验证旧模型能量代数、edge-PML 线性增长、Gronwall fallback。 | 作为旧模型背景，不替代新的 matching 推导。 |
| `results/energy_design_v2_report.md` 和 `_verified.md` | 全文 | v2 协变阻尼模型有正单调能量；perfect matching 明确未证明。 | 提供要测试的 v2 模型和已验证能量。 |
| `references/references.bib` | 全文 | Berenger、Joly/Becache、Baffet、dispersive PML、CFS/ADE、MPML 文献索引。 | 避免杜撰引用和题名。 |
| Joly 2012 | PDF pp. 6--8, 15--17 | PML 的本质是阻抗匹配/零反射；通过复坐标变换构造；二维中只应拉伸 PML 方向导数；简单各向同性阻尼一般不匹配。 | 定义本文的平面界面导纳测试。 |
| Bécache--Kachanovska--Wess 2023 | PDF pp. 6--8 | 色散波导 PML 在 Laplace 域先消去极化，采用 \(1+\sigma/(s\zeta(s))\) 伸缩；\(\zeta\) 和 admissibility 影响稳定性。 | 支持“保留 \(\varepsilon_D(s)\)，不要改成 \(\varepsilon_D(s+\rho)\)”的修复方向。 |
| Baffet--Grote--Imperiale--Kachanovska 2019 | PDF pp. 4--11 | 二阶波方程 PML 的单调能量不是朴素能量，而是含 shifted/time-integrated 变量的 augmented energy；常系数是清晰能量恒等式的自然范围。 | 指出完整二维 stretched PML 能量需要 Baffet 型结构。 |
| Bécache--Fliss--Kachanovska--Kazakova 2021 | PDF pp. 2--8 | 3D 对角各向异性 Maxwell 中 classical Cartesian PML 可能因 backward waves 不稳定。 | 强调 perfect matching 和 stability 是不同性质。 |
| Huang--Li--Liu 2023 | PDF pp. 1--6 | 等价 Berenger PML 的稳定性分析非平凡；变量阻尼情形仍困难。 | 支持“不能从匹配性自动推出朴素能量单调”。 |
| Meza-Fajardo--Papageorgiou 2008 | PDF pp. 1--2, 26 | M-PML 通过多轴阻尼改善稳定性；稳定性与阻尼比例相关。 | 作为 MPML 候选的背景。 |
| Correia--Jin 2006 | PDF pp. 1--5 | regular PML、CFS-PML、second-order PML 对传播波/倏逝波/低频表现不同。 | 作为 CFS/ADE 候选背景，不作为能量证明。 |
| Feng--Li 2013 | PDF pp. 1--4 | 高阶 stretched-coordinate PML 可用 ADE 实现，结合 CFS 优点。 | 支持 rational stretch 的 ADE 实现。 |
| Ping--Xu--Mao--Yang 2014 | PDF pp. 1--3, 8--10 | second-order M-PML 在弹性长时间计算中稳定有效。 | 支持 MPML 是稳定性修复类。 |
| Xie--Zheng--Cristini--Zhang 2023 | PDF pp. 1--7, 13 | 频移多轴 PML 提升吸收/稳定性；文中明确多轴界面不完全匹配。 | 用于标注 MPML 为 absorbing/stability 而非 exact matching。 |
| `references/main.pdf` | PDF pp. 45--47 等 | 本地笔记给出 stretched-coordinate 与 UPML 的相似性、Cole--Cole/UPML 频域形式。 | 项目背景；不可读公式不作为独立证据。 |
| `references/Super.pdf` | PDF pp. 20--25 | 本地超收敛笔记复述二维 C-CPML 频域/时域形式和能量稳定框架。 | 项目背景；不支持新 matching 结论。 |
| `references/Thesis.pdf` | PDF pp. 144--147 | 二维 C-CPML 中磁场方程的 \((\sigma_y-\sigma_x)H_x\)、\((\sigma_x-\sigma_y)H_y\) 使单调能量困难，只证明有限时间有界。 | 支持旧 C-CPML/八变量模型的能量困难分类。 |

## 3. Perfect matching criterion

设物理半空间为 \(x<0\)，PML 半空间为 \(x>0\)。取 Laplace--Fourier 模式
\[
E,H,P\sim e^{st+ik_y y+\nu x},\qquad \Re s>0.
\]
物理 Maxwell--Debye 介质满足
\[
P+\tau sP=\chi E,\qquad
\varepsilon_D(s)=\epsilon_0\epsilon_\infty+\frac{\chi}{1+\tau s}.
\]
物理方程为
\[
s\varepsilon_D(s)E=\partial_xH_y-\partial_yH_x,
\]
\[
\mu sH_x=-\partial_yE,\qquad \mu sH_y=\partial_xE.
\]
代入 \(\partial_x=\nu_0,\partial_y=ik_y\)，得到
\[
H_x=-\frac{ik_y}{\mu s}E,\qquad
H_y=\frac{\nu_0}{\mu s}E,
\]
\[
\nu_0^2=k_y^2+\mu s^2\varepsilon_D(s).
\]
物理导纳定义为
\[
Y_0=\frac{H_y}{E}=\frac{\nu_0}{\mu s}.
\]

对 \(x=0\) 界面，连续切向量为 \(E\) 与 \(H_y\)。若入射波振幅为 \(1\)，反射振幅为
\(R\)，透射振幅为 \(T\)，则
\[
1+R=T,\qquad Y_0(1-R)=Y_+T.
\]
因此
\[
R=\frac{Y_0-Y_+}{Y_0+Y_+}.
\]
perfect matching 的公式判据是
\[
\boxed{Y_+(s,k_y)=Y_0(s,k_y)\quad\text{对所有出射物理模成立}.}
\]

标准 stretched-coordinate PML 取
\[
S_x(s)=1+\frac{\sigma_x}{s}
\]
并替换
\[
\partial_x\mapsto S_x^{-1}\partial_x,
\]
同时保持 \(\varepsilon_D(s)\) 不变。于是 PML 中 \(\nu_+=S_x\nu_0\)，而
\[
Y_+=\frac{S_x^{-1}\nu_+}{\mu s}
=\frac{\nu_0}{\mu s}=Y_0.
\]
这就是本报告采用的匹配测试。

## 4. Perfect matching test for the v2 model

v2 模型为
\[
\epsilon_0\epsilon_\infty D_\rho E
=\partial_xH_y-\partial_yH_x-D_\rho P,
\]
\[
\mu(\partial_t+\rho_y)H_x=-\partial_yE,\qquad
\mu(\partial_t+\rho_x)H_y=\partial_xE,
\]
\[
P+\tau D_\rho P=\chi E,\qquad D_\rho=\partial_t+\rho,\quad
\rho=\rho_x+\rho_y.
\]

考虑 \(x\)-PML 常系数半空间：
\[
\rho_x=\rho>0,\qquad \rho_y=0.
\]
则
\[
P=\frac{\chi}{1+\tau(s+\rho)}E,\qquad
\varepsilon_\rho(s)
=\epsilon_0\epsilon_\infty+\frac{\chi}{1+\tau(s+\rho)}.
\]
Laplace--Fourier 代数系统是
\[
(s+\rho)\varepsilon_\rho(s)E=\nu H_y-ik_yH_x,
\]
\[
\mu sH_x=-ik_yE,\qquad
\mu(s+\rho)H_y=\nu E.
\]
所以
\[
H_x=-\frac{ik_y}{\mu s}E,\qquad
H_y=\frac{\nu}{\mu(s+\rho)}E,
\]
\[
\nu^2=\mu(s+\rho)^2\varepsilon_\rho(s)+k_y^2\frac{s+\rho}{s}.
\]
v2 透射导纳为
\[
Y_{v2}^2
=\frac{1}{\mu^2}\left(
\mu\varepsilon_\rho(s)+\frac{k_y^2}{s(s+\rho)}
\right).
\]
与
\[
Y_0^2
=\frac{1}{\mu^2}\left(
\mu\varepsilon_D(s)+\frac{k_y^2}{s^2}
\right)
\]
比较，得到精确失配
\[
\boxed{
Y_{v2}^2-Y_0^2
=-\frac{\rho}{\mu^2}\left[
\frac{\mu\chi\tau}{(1+\tau s)(1+\tau(s+\rho))}
+\frac{k_y^2}{s^2(s+\rho)}
\right].}
\]

因此 v2 不满足 \(Y_{v2}=Y_0\)。特别地：

- 即使 \(k_y=0\)，只要 \(\chi\tau\rho\ne0\)，Debye 极化率从
  \(\varepsilon_D(s)\) 变成 \(\varepsilon_\rho(s)\)，阻抗已改变。
- 即使 \(\chi=0\)，只要 \(k_y\ne0\)，斜入射项也从 \(k_y^2/s^2\) 变成
  \(k_y^2/[s(s+\rho)]\)。

结论：v2 的协变 Debye 阻尼有利于能量耗散，但破坏了标准 PML 的
stretched-coordinate 阻抗匹配。

## 5. Candidate repaired PML models

### 5.1 标准 stretched-coordinate Maxwell--Debye PML

推荐的精确匹配修复模型在 Laplace 域写作
\[
\boxed{
s\varepsilon_D(s)\widehat E
=S_x^{-1}\partial_x\widehat H_y
-S_y^{-1}\partial_y\widehat H_x,}
\]
\[
\boxed{
\mu s\widehat H_x=-S_y^{-1}\partial_y\widehat E,\qquad
\mu s\widehat H_y=S_x^{-1}\partial_x\widehat E,}
\]
\[
\boxed{(1+\tau s)\widehat P=\chi\widehat E.}
\]
其中
\[
S_i(s)=1+\frac{\sigma_i}{s},\qquad \sigma_i\ge0.
\]
物理区域 \(\sigma_i=0\)。界面条件为物理切向迹连续；例如 \(x\)-界面连续 \(E,H_y\)。

在时域 ADE 形式中，令
\[
\mathcal A_i=S_i^{-1}=\frac{s}{s+\sigma_i},
\qquad
\mathcal A_i f=f+\psi_i,\quad
(\partial_t+\sigma_i)\psi_i=-\sigma_i f.
\]
则
\[
\epsilon_0\epsilon_\infty E_t+P_t
=\partial_xH_y-\partial_yH_x+\psi_{E,x}-\psi_{E,y},
\]
\[
\mu H_{x,t}=-\partial_yE-\psi_{H_x,y},\qquad
\mu H_{y,t}=\partial_xE+\psi_{H_y,x},
\]
\[
P+\tau P_t=\chi E,
\]
其中
\[
(\partial_t+\sigma_x)\psi_{E,x}=-\sigma_x\partial_xH_y,\qquad
(\partial_t+\sigma_y)\psi_{E,y}=-\sigma_y\partial_yH_x,
\]
\[
(\partial_t+\sigma_y)\psi_{H_x,y}=-\sigma_y\partial_yE,\qquad
(\partial_t+\sigma_x)\psi_{H_y,x}=-\sigma_x\partial_xE.
\]
该模型在连续常系数平面界面处 perfectly matched。

### 5.2 CFS/ADE generalized stretched PML

取更一般的 rational stretch
\[
S_i(s)=\kappa_i+\frac{\sigma_i}{s+\alpha_i},\qquad
\kappa_i\ge1,\quad \sigma_i\ge0,\quad \alpha_i\ge0.
\]
只要仍然只拉伸空间导数，并保持
\[
(1+\tau s)\widehat P=\chi\widehat E,
\]
平面界面处仍有 \(\nu_+=S_x\nu_0\) 和 \(Y_+=Y_0\)。CFS/ADE 版本更适合低频、
倏逝波或长时间误差控制，但完整单调能量需要正的记忆核实现；本报告不声称已完成。

### 5.3 MPML-type damping

MPML 在法向之外增加多轴阻尼，可改善某些模型的长时间稳定性或消除 Jordan 型增长。
但一旦切向 stretch 在界面处非平凡，界面导纳通常改变。已检查的 MPML 文献也明确提示
多轴版本可能不是 exact perfectly matched。因此本报告把 MPML 归类为稳定/吸收修复，
不是本问题的首选 exact matching 修复。

## 6. Energy functional construction

### 6.1 v2 的完整单调能量

已验证的 v2 能量为
\[
\mathcal E_\rho(t)=\frac12\int_\Omega
\left(
\epsilon_0\epsilon_\infty E^2+\mu H_x^2+\mu H_y^2+\chi^{-1}P^2
\right)\,dxdy.
\]
正性来自
\[
\epsilon_0,\epsilon_\infty,\mu,\chi>0.
\]
用 PEC 外边界 \(E=0\) 消去 Maxwell flux，并用
\[
E\,D_\rho P
=\frac{1}{2\chi}\partial_t(P^2)
+\frac{\rho}{\chi}P^2
+\frac{\tau}{\chi}|D_\rho P|^2
\]
可得
\[
\boxed{
\frac{d}{dt}\mathcal E_\rho(t)
=-\int_\Omega\left(
\epsilon_0\epsilon_\infty\rho E^2
+\mu\rho_yH_x^2
+\mu\rho_xH_y^2
+\frac{\rho}{\chi}P^2
+\frac{\tau}{\chi}|D_\rho P|^2
\right)\,dxdy\le0.}
\]
这是 genuine dissipative identity，但它属于不完美匹配的吸收层。

零耗散空间由上式刻画：若
\[
\rho E=0,\quad \rho_yH_x=0,\quad \rho_xH_y=0,\quad \rho P=0,\quad
D_\rho P=0,
\]
并满足 Maxwell 主方程，则耗散为零。物理未阻尼区域中的定常磁场模式属于这种零空间。

### 6.2 标准 stretched-coordinate PML 的朴素能量

对精确匹配的 stretched-coordinate ADE 模型，朴素物理 Debye 能量仍是
\[
\mathcal E_{\rm phys}
=\frac12\int_\Omega
\left(
\epsilon_0\epsilon_\infty E^2+\mu H_x^2+\mu H_y^2+\chi^{-1}P^2
\right)\,dxdy.
\]
使用
\[
E P_t
=\frac{1}{2\chi}\partial_t(P^2)+\frac{\tau}{\chi}P_t^2
\]
和 PEC flux 消去，得到
\[
\frac{d}{dt}\mathcal E_{\rm phys}
=-\int_\Omega\frac{\tau}{\chi}P_t^2\,dxdy
+\int_\Omega
\left[
E(\psi_{E,x}-\psi_{E,y})
-H_x\psi_{H_x,y}
+H_y\psi_{H_y,x}
\right]\,dxdy .
\]
边界项为
\[
\int_{\partial\Omega}E(H_y n_x-H_x n_y)\,ds,
\]
在 PEC 外边界为零，在内部材料/PML 界面由切向迹连续抵消。

最后一行的 ADE 记忆耦合项没有固定符号。因此朴素能量不是完整二维单调能量。一个
完整证明必须加入 Baffet 型 shifted/time-integrated 变量或正的 passive-memory 能量。

### 6.3 法向入射一维 stretched PML 的正耗散恒等式

在 \(x\)-PML 法向入射块 \(k_y=0\) 中，精确 stretched 模型化为
\[
(\partial_t+\rho)(\epsilon_0\epsilon_\infty E+P)=\partial_xH_y,
\]
\[
\mu(\partial_t+\rho)H_y=\partial_xE,
\]
\[
P+\tau P_t=\chi E.
\]
注意这里 Debye law 仍是 \(P+\tau P_t=\chi E\)，不是 v2 的
\(P+\tau(\partial_t+\rho)P=\chi E\)。

取
\[
\boxed{
\mathcal E_{1d,sc}
=\frac12\int_I\left(
\epsilon_0\epsilon_\infty E^2+\mu H_y^2
+\frac{1+\rho\tau}{\chi}P^2
\right)\,dx.}
\]
由
\[
E=\frac{P+\tau P_t}{\chi}
\]
得到
\[
E P_t=\frac{1}{2\chi}\partial_t(P^2)+\frac{\tau}{\chi}P_t^2,
\]
\[
\rho E P
=\frac{\rho}{\chi}P^2+\frac{\rho\tau}{2\chi}\partial_t(P^2).
\]
乘以 \(E,H_y\) 并分部积分后，
\[
\boxed{
\frac{d}{dt}\mathcal E_{1d,sc}
=-\int_I\left(
\rho\epsilon_0\epsilon_\infty E^2
+\mu\rho H_y^2
+\frac{\rho}{\chi}P^2
+\frac{\tau}{\chi}P_t^2
\right)\,dx
+\int_{\partial I}EH_y n_x\,ds.}
\]
在 PEC 或非正通量边界下，这是单调耗散恒等式。该结果说明标准 stretched repair
并非与能量方法冲突；完整二维情形需要下面的 Baffet 型 time-primitive 变量。

### 6.4 常系数二维 Baffet--Debye 正耗散恒等式

对常系数 PML 块，令
\[
e=\epsilon_0\epsilon_\infty,\qquad
a=\sigma_x+\sigma_y,\qquad b=\sigma_x\sigma_y,\qquad a>0,
\]
\[
\Gamma_1=\begin{pmatrix}\sigma_x&0\\0&\sigma_y\end{pmatrix},\qquad
\Gamma_2=\begin{pmatrix}\sigma_y-\sigma_x&0\\0&\sigma_x-\sigma_y\end{pmatrix}.
\]
取 electric primitive \(u\) 和 polarization primitive \(q\)：
\[
E=u_t,\qquad q_t=P,\qquad \tau P_t+P=\chi u_t,\qquad q+\tau P=\chi u.
\]
引入
\[
\lambda=\nabla u+\phi,
\]
并考虑 Baffet 型二维系统
\[
\mu\{e(u_{tt}+a u_t+b u)+P_t+aP+bq\}-\nabla\cdot\lambda=0,
\]
\[
\phi_t+\Gamma_1\phi=\Gamma_2\nabla u.
\]
Laplace 消去 \(\phi\) 得到
\[
\widehat\lambda_x=\frac{S_y}{S_x}\partial_x\widehat u,\qquad
\widehat\lambda_y=\frac{S_x}{S_y}\partial_y\widehat u,\qquad
S_i=1+\frac{\sigma_i}{s}.
\]
又因
\[
\widehat P=\frac{\chi s}{1+\tau s}\widehat u,\qquad
\widehat q=\frac1s\widehat P,
\]
所以该系统等价于
\[
\mu\varepsilon_D(s)s^2\widehat u
=S_x^{-1}\partial_x(S_x^{-1}\partial_x\widehat u)
+S_y^{-1}\partial_y(S_y^{-1}\partial_y\widehat u),
\]
即从标准 stretched-coordinate Maxwell--Debye PML 消去 \(H_x,H_y\) 后得到的二阶方程。
因此它继承 section 5.1 的平面界面 perfect matching。

定义
\[
\alpha=1+2a\tau,\qquad \beta=a+b\tau,\qquad \gamma=a^2+b(1+a\tau).
\]
验证过的 Baffet--Debye 能量为
\[
\boxed{
\begin{aligned}
\mathcal E_{BD}
=\frac12\int_\Omega\{&
\mu e(u_t+a u)^2+|\lambda|^2+|\phi|_{a^{-1}\Gamma_1}^2+\mu e\,b u^2\\
&+\frac{\mu}{\chi}\left(\alpha P^2+2\beta Pq+\gamma q^2\right)
\}\,dxdy .
\end{aligned}}
\]
\(P,q\) 二次型正定，因为
\[
\alpha>0,\qquad
\alpha\gamma-\beta^2
=b+ab\tau+2a^3\tau+b(2a^2-b)\tau^2>0.
\]
其耗散项为
\[
\boxed{
\begin{aligned}
\mathcal D_{BD}
=\int_\Omega\{&
|\lambda|^2_{\Gamma_1(I+a^{-1}\Gamma_1)}
+\frac{b}{a}|\nabla u|^2+\mu e\,ab u^2\\
&+\frac{\mu}{\chi}\left[
\tau P_t^2+\tau(a^2-b)P^2+abq^2
\right]\}\,dxdy .
\end{aligned}}
\]
直接乘以 \(u_t+a u\)，并用 Baffet 恒等式
\[
\lambda_t+\Gamma_1\lambda
=\nabla u_t+(\Gamma_1+\Gamma_2)\nabla u
\]
以及 Debye primitive 乘积恒等式
\[
(P_t+aP+bq)(u_t+a u)
=\frac1\chi\left[
\frac12\partial_t(\alpha P^2+2\beta Pq+\gamma q^2)
+\tau P_t^2+\tau(a^2-b)P^2+abq^2
\right]
\]
得到
\[
\boxed{
\frac{d}{dt}\mathcal E_{BD}(t)
=-\mathcal D_{BD}(t)
+\int_{\partial\Omega}(u_t+a u)\lambda\cdot n\,ds.}
\]
在 PEC 外边界或分块常系数界面的通量抵消条件下，
\[
\mathcal E_{BD}(t)+\int_0^t\mathcal D_{BD}(r)\,dr\le \mathcal E_{BD}(0).
\]
这就是 accepted repaired model 的二维非增/no-abnormal-growth 结论。它不是“所有非零态严格
衰减”：零空间仍包含未阻尼物理区域中的定常 curl-free 磁场模式和 primitive gauge 模式。
对空间连续变化的 damping profile，本报告只声称需另作变量系数能量证明；已验证结论是
常系数及分块常系数传输框架。

## 7. Obstructions and impossibility statements

### 7.1 旧八变量模型的 verified edge obstruction

旧模型中
\[
M_x=Q_x+\mu\frac{\sigma_x}{\epsilon_0}H_x
\]
在 \(x\)-edge、\(\sigma_x=s>0,\sigma_y=0\)、zero-transverse 模式下为常数。取
\[
E=P=P_{z,1}=P_{z,2}=H_y=Q_y=0
\]
且 \(H_x,Q_x\) 空间常数，则
\[
H_x(t)=H_x(0)+\frac{M_x(0)}{\mu}t,
\qquad
Q_x(t)=Q_x(0)-\frac{s}{\epsilon_0}M_x(0)t.
\]
这排除了旧八变量模型对所有变量的无条件正单调能量或长时间一致有界能量。v2 删除
独立的 \(P_{z,i},Q_i\)，所以去掉了这个 Jordan mode，但代价是失去 perfect matching。

### 7.2 全域严格衰减的零空间障碍

如果物理区域内 \(\sigma_x=\sigma_y=0\)，取
\[
E=0,\qquad P=0,\qquad H_x=\partial_x\phi,\qquad H_y=\partial_y\phi,
\]
其中 \(\phi\) 光滑且支撑在该物理区域内，则
\[
\partial_xH_y-\partial_yH_x=0,\qquad
\partial_xE=\partial_yE=0.
\]
所有 PML auxiliary 若初值为零则保持零；该非零磁能态是定常解。因此任何总能量都不可能
对全域所有非零态严格下降。最多能证明
\[
\frac{d}{dt}\mathcal E(t)=-\mathcal D(t),\qquad \mathcal D(t)\ge0,
\]
并准确说明 \(\mathcal D(t)=0\) 的零空间。

### 7.3 Cole--Cole/fractional extension

分数阶极化不能修复与 \(P\) 无关的电磁/PML 失配。旧八变量 edge obstruction 可取
\(P=0\)，v2 matching 失配中即使 \(\chi=0\) 也有斜入射项失配。因此 fractional law 只能在
已经确定的 matched Maxwell PML 上作为正记忆材料能量加入。若要声称 fractional theorem，
必须写出正的 diffusive/memory 表示；本报告不声称该 theorem。

## 8. Recommendation for the next manuscript step

下一步 manuscript 应分成两个互不混淆的 theorem。

**Theorem A: perfect matching.** 使用标准 stretched-coordinate 或 CFS/ADE
Maxwell--Debye PML：
\[
s\varepsilon_D(s)\widehat E
=S_x^{-1}\partial_x\widehat H_y-S_y^{-1}\partial_y\widehat H_x,
\]
\[
\mu s\widehat H_x=-S_y^{-1}\partial_y\widehat E,\qquad
\mu s\widehat H_y=S_x^{-1}\partial_x\widehat E,
\]
\[
(1+\tau s)\widehat P=\chi\widehat E.
\]
证明平面界面处 \(\nu_+=S_i\nu_0\)、\(Y_+=Y_0\)、\(R=0\)。

**Theorem B: energy/stability.** 以 Baffet--Debye primitive 形式作为 exact
stretched-coordinate PML 的能量 theorem。常系数块中使用 \(u_t=E,q_t=P\)，证明
\[
\frac{d}{dt}\mathcal E_{BD}(t)
=-\mathcal D_{BD}(t)
+\int_{\partial\Omega}(u_t+a u)\lambda\cdot n\,ds,
\qquad \mathcal D_{BD}\ge0.
\]
在 PEC 或传输通量抵消条件下得到非增能量和 no-abnormal-growth estimate。变量系数
damping profile 应作为后续独立 theorem，而不是从常系数结论直接推出。

若使用 v2 协变阻尼模型，则 theorem 只能是单调稳定吸收层 theorem，不应称为 PML。
目前已验证的最强结论是：标准 stretched-coordinate/Baffet-primitive Maxwell--Debye
模型在常系数二维块中同时给出 exact matching 与非增耗散能量；全域严格衰减需排除
section 7.2 的零空间。

## Assembly

Fact index 中列出的已验证事实给出旧模型 obstruction、Gronwall fallback、v2 单调能量、
v2 matching 失效、标准 stretched-coordinate matching/1D 能量、Baffet-primitive 二维
常系数能量，以及全域严格衰减的零空间 obstruction。由这些事实组装得到：

- v2 的 \(D_\rho\) Debye law 把物理 \(\varepsilon_D(s)\) 改为
  \(\varepsilon_D(s+\rho)\)，并改变斜入射导纳项，所以不是 perfectly matched。
- 标准 stretched-coordinate Maxwell--Debye PML 保持 \(\varepsilon_D(s)\) 并只拉伸空间导数，
  因此平面界面导纳不变。
- 能量结论必须按模型分类：v2 单调但不匹配；标准 stretched PML 匹配；其朴素能量不单调，
  但 Baffet-primitive 形式在常系数二维块中给出
  \(\frac{d}{dt}\mathcal E_{BD}=-\mathcal D_{BD}\) 加边界通量的非增恒等式。

这回答了 stage-3 目标的核心分歧：v2 不能作为最终 PML；下一步应以标准
stretched-coordinate/Baffet-primitive 模型为 manuscript 的主 theorem，并把变量系数
damping 与 fractional 正记忆表示列为后续工作。
