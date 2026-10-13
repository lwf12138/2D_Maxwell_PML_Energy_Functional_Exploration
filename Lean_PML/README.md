# LeanPML：实际空间、加权状态与能量求导

用途：说明 v0.3.1 如何将 v0.2 的点态公式接入真实 L² 商空间、空间积分及时间求导。学习说明集中在本文件和代码批注；历史 README 见 [入场快照](logs/v0.3.1/initial_files/README.md)，各阶段记录完整保留于 [PROGRESS](PROGRESS.md)。

**v0.3.1 已完成：实际构建、公理审计、调用实例与 PDF 验收均通过。** 本轮只到 v0.3.1；没有推进 primitive/Green 能量律。固定 Lean v4.31.0、mathlib 提交 `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`，未更新依赖。

## 本轮实际增加了什么

| 文件 | 实际对象或结论 | 对应来源 |
|---|---|---|
| [EnergyCalculus](LeanPML/Analysis/EnergyCalculus.lean) | mathlib 的 `Lp ℝ 2 ν`、有界可测系数乘法、交叉项可积、积分/内积、真实时间求导 | 由 (6.2) 推出，原文未单列的分析步骤 |
| [WeightedL2](LeanPML/Analysis/WeightedL2.lean) | 平方根坐标闭子空间、完备性、a.e. 重建、连续单射零延拓、加权范数积分与求导 | (5.5)–(5.6)，§7.1 加权链式法则 |
| [SpatialCoefficients](LeanPML/PML/SpatialCoefficients.lean) | 实际可测 p、r、原始幅度条件、分离变量/矩形入口、正确方向的有界耗散系数 | (5.3)、(5.5)、(7.2) |
| [State](LeanPML/PML/State.lean) | 实际场状态、代数约束、分量路径导数、同源两层、标明条件性的空间算子域 | (6.1)、(6.3)、(6.6) 的时间接口 |
| [Energy](LeanPML/PML/Energy.lean) | F_c、E₇、图范数平方候选、真实空间能量求导、单位矩形非零加权路径实例 | (6.2)–(6.5)，仅定义与内积求导 |
| [EnergyIntegrals](LeanPML/PML/EnergyIntegrals.lean) | 旧块密度可积及积分对应、S 的分量积分非负、D_c/D₇ 合法积分、积分形式求导 | (6.2)、(7.2)、(7.7)–(7.8) 的定义部分 |

测度用 $\nu$，材料参数仍用 $\mu$。矩形入口为整个
$\Omega=(x_0,x_1)\times(y_0,y_1)$ 上的二维 Lebesgue 限制测度，包含物理区、边层与角层。一般测度空间上的引理允许更一般可测系数；`SpatialAbsorption.separated` 明确恢复 $p=p(x),r=r(y)$ 的物理模型。`ofAE` 通过截断选择全点满足幅度条件的可测代表，并证明与原函数 a.e. 相同；这没有把合同的几乎处处条件加强为新的物理限制。W¹∞ 空间导数及其用途仍待后续实现。

## 无界权重和零区如何同时保留

令 $Z=\{p+r=0\}$。加权状态保存的坐标是

$$
X=\sqrt{w}\,\psi\in L^2(\Omega,\nu),\qquad X=0\quad \nu\text{-a.e. 于 }Z.
$$

这是普通 L² 中的具体子空间。它等于“乘以零区示性函数”的有界算子之核，因此闭且完备，继承真实内积。物理辅助场通过

$$
\psi=(\sqrt w)^{-1}X,\qquad \psi=0\text{ 于 }Z
$$

恢复。正区 $w\ge 3/2$ 来自 v0.2.1，故逆平方根不超过 1；零区用单独的 a.e. 条件处理。已证明

$$
\|\psi\|_{L^2}^2\le \|X\|_{L^2}^2
=\int_\Omega w\psi^2\,d\nu.
$$

代码同时证明恢复映射是单射、原函数与平方根坐标可以双向恢复、代表元 a.e. 相等不改变状态。这里没有假设 $w$ 有界，也没有对所有普通 L² 函数构造 $\psi\mapsto w\psi$ 的有界算子。只有 $a,b$ 及其有界多项式系数使用 `boundedMul`。

全零吸收时加权辅助空间只有零元；普通场仍存在，空间耗散仍保留 $c(\|h_x\|_2^2+\|h_y\|_2^2)$。两个标量分量的平方范数明确相加，不使用普通乘积类型的 max 范数冒充欧氏范数。

## 从状态槽到真实时间导数

`FieldState` 保存 $v,V,R,z,\psi_x,\psi_y,\Lambda_x,\Lambda_y$。状态槽 $V$ 本身不证明 $V=v_t$；`StateHasDerivAt` 对每个分量提供实际空间范数中的 `HasDerivAt`。加权分量的证据必须在加权空间中成立，逐点可导或普通 L² 可导不能替代。

`SameSourcePath` 保存 base、first、second 及真实导数：

| 论文对象 | Lean 对应 |
|---|---|
| $U_0=(u,P,q,\varphi)$，速度 $E$，通量 $\lambda$ | `base`：v=u、V=E、R=P、z=q、ψ=φ、Λ=λ |
| $U_1=(E,P_t,P,\varphi_t)$，速度 $E_t$，通量 $\lambda_t$ | `first`：各槽确实来自 base 的导数 |
| $U_0$ 耗散中的 $R_t=P_t$ | `first.R` |
| $U_1$ 耗散中的 $R_t=P_{tt}$ | `second.R` |

导数唯一性给出 first.v=base.V、first.z=base.R。在时间集合内部，对这些邻域等式求导可继续得到导数层的时间坐标对应；不能仅对一个时刻的等式求导。**“导数层满足同一 primitive 系统”仍未证明。**

空间分量目前具体取 $h_i=\Lambda_i-\psi_i\in L^2$。`FieldSpatialConstraint` 使用已构造的零延拓映射连接条件性空间域。该域有明确算子定义域，但尚不是已实现的矩形 H₀¹、弱梯度或零迹；没有把任意 L² 有界算子命名为已实现的 Grad。

## 能量、积分与求导分别证明了什么

$F_c=\mu F_e+\mu F_D+F_{\rm sp}$；电块已包含 $\epsilon/2$，极化块已包含 $1/(2\kappa)$，空间块每项含 $1/2$。`fieldEnergy_eq_integral` 将新的内积定义与旧 `singleLayerEnergy` 密度精确连接；不是另造一套能量。

可积性分别来自普通 L² 平方、L²×L² 的交叉乘积、有界可测系数，以及实际加权成员资格。`fieldEnergyDensity_integrable` 先证明可积，积分表示再拆分求和，不依赖不可积函数积分的总定义。

`hasDerivAt_fieldEnergy` 和 `hasDerivAt_integral_fieldEnergy` 从各分量的真实空间导数推出

$$
\frac{d}{dt}F_c(U(t))
=\mu\,\mathrm{electricRate}(U,\dot U)
+\mu\,\mathrm{polarRate}(U,\dot U)
+\mathrm{spatialRate}(U,\dot U).
$$

例如固定系数算子 $M$ 的交叉项满足
$(\langle MX,Y\rangle)'=\langle MX,\dot Y\rangle+\langle M\dot X,Y\rangle$；
空间平方项贡献 $\langle\Lambda_i,\dot\Lambda_i\rangle+
\langle\psi_i,\dot\psi_i\rangle_w$。这是空间内积求导，不是先逐点微分再未经证明地交换积分。

论文记号 $N_0^2,N_1^2$ 分别是 `graphSquare` 在 `path.base t`、`path.first t` 上的值；$S_0,S_1$ 分别是 `fieldSpatialDissipation ν C (path.base t)` 与 `fieldSpatialDissipation ν C (path.first t)`。这些都是同一实际空间表达式在同源两层上的应用，没有再传入未解释的实数槽。

单层 $D_c$、两层 $D_7$ 已定义为合法积分，**没有证明它们非负**。只证明 (7.2) 的 L² 分量空间耗散积分非负，且全零分支仍有 $c|h|^2$。图范数平方候选 $N^2$ 不直接含独立 $v,z$，尚未对任意原始状态安装范数结构，也没有证明双边能量估计。

材料常数在物理模型中为正；线性积分/求导恒等式对更一般实常数也成立，因此低层分析定理不强加无用正性假设。论文 $K=8\mu(\epsilon+2\kappa)C_P^2$ 在 `energy7` 等专用组合中固定；$C_P$ 仍是参数，并未证明矩形 Poincaré。

实例 `SpaceExample.hasDerivAt_energy` 位于整个单位矩形，取 $c=4,p=1,r=0$。平方根坐标 seed=1 是实际非零加权成员，加权坐标路径 $X_x(t)=(t+1)\,\mathrm{seed}$ 非恒定，对应物理分量 $\psi_x(t)=(t+1)/2$，实际调用单层能量求导定理。该实例只检验空间能量计算接口，不声称满足 PDE 或空间兼容约束。

## 建议先读这三条声明

1. `LeanPML.Analysis.physicalL2_norm_sq_le`：从权重下界得到实际嵌入；先看紧邻的 `physicalL2` 定义。
2. `LeanPML.PML.fieldEnergy_eq_integral`：内积能量与旧密度积分一一对应；可沿调用回看每块的可积性。
3. `LeanPML.PML.hasDerivAt_fieldEnergy`：如何把内积、加权范数求导组装成整个单层求导；再看积分版本及矩形实例。

建议文件顺序：SpatialCoefficients 的原始参数 → WeightedL2 → State → Energy 的定义 → EnergyIntegrals 的表示定理 → Energy 的求导与实例。EnergyCalculus 是被调用的基础工具，可按 F12 从使用处跳转，不必一开始逐条读完。

VS Code 打开整个工程目录。在 Lean 文件里运行 `Lean 4: InfoView: Display Goal`，把光标停在 `have`、`filter_upwards`、`rw`、`exact` 前后，看上下文与 `⊢`。`filter_upwards` 把多个 a.e. 事实在同一满测集上合并；`ring` 只整理已经建立分析依据后的实数代数。F12 跳至项目或 mathlib 声明，悬停查看参数。保存文件、运行构建后，若导入仍旧，执行 `Lean 4: Server: Restart File`；无需重新安装或更新依赖。

关键 mathlib 声明（相对工程根目录的固定源码）：

- `MeasureTheory.Lp`、`Lp.ext`、`Lp.memLp`：`.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`。
- `MeasureTheory.L2.inner_def`、`L2.integrable_inner`、`MemLp.integrable_sq`：`.../MeasureTheory/Function/L2Space.lean`。
- `HasDerivAt.inner`、`HasDerivAt.norm_sq`：`.../Analysis/InnerProductSpace/Calculus.lean`。
- `ContinuousLinearMap.hasFDerivAt`：`.../Analysis/Calculus/FDeriv/Linear.lean`。
- `integral_add`、`integral_const_mul`、`integral_congr_ae`：`.../MeasureTheory/Integral/Bochner/Basic.lean`。
- `Measure.prod_prod`：`.../MeasureTheory/Measure/Prod.lean`；`Real.volume_Ioo`：`.../MeasureTheory/Measure/Lebesgue/Basic.lean`。

## 复现与验证记录

~~~sh
cd '/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML'
python3 scripts/run_logged.py --stage v0.3.1 lake_build lake build
python3 scripts/run_logged.py --stage v0.3.1 axioms_audit lake env lean Audit.lean
~~~

[最终构建](logs/v0.3.1/20261013T002136_137117_lake_build.log)与[独立公理审计](logs/v0.3.1/20261013T002105_759533_axioms_audit.log)均退出 0。正式导入包含 18 个项目模块，审计旧 154 条与新增 109 条，共 263 条实际结果；没有占位公理。修改页均已渲染检查，见 [PDF 验收](logs/v0.3.1/pdf/verification.json)。

实际失败及成功检查全部保存在 [logs/v0.3.1](logs/v0.3.1)，每个 JSON 保存命令、工作目录、退出码与对应完整输出。早期新 import 缺失缓存、API 改写及实例推断失败均保留；曾主动中断过量导入的依赖构建，再收窄 import 编译固定版本，没有改锁文件。

[最终交付核对](logs/v0.3.1/final_checks.json)同时检查导入覆盖、全部新增审计、受保护文件哈希、历史保留和文档链接。

新增正式模块须接入 `LeanPML.lean` 导入链，在 `Audit.lean` 添加相应完整定理名后实际构建、审计。标准 `propext`、`Classical.choice`、`Quot.sound` 不属于占位证明；检查要求没有 `sorryAx` 或自定义占位公理。

## PDF、范围与下一阶段

[PDF 账本](docs/pdf_formalization_marks.md)区分定义录入、实际分析结论与完整 PDE 结论；[指定副本](../results/V7_Maxwell_Debye_PML/V7_global_energy_副本.pdf)已在最终构建/审计通过后更新。本阶段在第 8、9、11 页新增 4 个有范围红勾，分别标加权嵌入、实际积分表示、加权路径求导和空间分量积分非负；第 8、9、11、12 页另有定义/范围说明。18 页及 141 项旧批注保留，共 150 项批注。没有标能量律、正定性或单调性全部完成。

下一阶段 **v0.3.2** 的入口为 `StateHasDerivAt`、`hasDerivAt_integral_fieldEnergy` 及各旧局部块：输入真正的 primitive 演化和逐项列出的 Green/零迹接口，证明单层导数关系，并证明同源导数层满足相同演化。具体矩形弱梯度/零迹、时间与空间微分交换、Green/PEC、Poincaré、图范数双边估计、完整两层耗散非负、最终单调性，以及原八变量对应/解存在唯一性仍未完成。本轮不实现这些下一阶段内容。
