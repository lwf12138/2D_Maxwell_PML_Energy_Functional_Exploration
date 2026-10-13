# LeanPML：具体光滑矩形接口与原模型映射

用途：沿实际函数、L² 商类、四边迹、历史提升这条线阅读 v0.4。本次对齐补齐参数证书、区域幅度入口和古典空间可导包装；旧验收范围的更正见文末。v0.4.1–v0.4.4 已分别完成实现、完整构建、公理审计和假设检查。此前说明见 [v0.4 入场 README](logs/v0.4.1/initial_files/README.md)，阶段历史见 [PROGRESS](PROGRESS.md)。本轮不实施 v0.5，不更新 Lean/mathlib。

## 先读三条声明

1. [ParameterCertificate.lean](LeanPML/Rectangle/ParameterCertificate.lean) 的 `unitSquare_parameter_certificate`：从实际矩形算出 $C_P,A,K$，然后查看 `unitSquare_explicit_smallness` 和阈值等价的调用。
2. [ClassicalSystem.lean](LeanPML/PML/ClassicalSystem.lean) 的 `original_to_primitive_classical_rectangle`：比较原八方程、真实空间可导证据和兼容保持结论；反向见同文件 `primitive_to_original_classical_rectangle`。
3. [RegionalCoefficients.lean](LeanPML/Rectangle/RegionalCoefficients.lean) 的 `RegionalAbsorption.originalRegionalFiniteIntervalProblem`：查看域内幅度条件怎样生成旧框架需要的实现代表，再进入古典映射和具体 Green/Poincaré 构造。

先读每条声明冒号后的结论，再追踪输入和具名 `have`。原 v0.4 的学习路线仍是 Domain → Fields/Boundary → Green/Poincare → TimeSpace/L2Paths → WeightedCalculus/StatePaths → 原系统与实际历史 → ClassicalSystem → RegionalCoefficients。旧 `originalFiniteIntervalProblem_separated` 保留兼容，但其全轴幅度条件较强，不再作为推荐入口。

## 本轮究竟选择了什么光滑类

空间是整个非退化开矩形

$$\Omega=(x_-,x_+)\times(y_-,y_+),\qquad L_x=x_+-x_->0,\quad L_y=y_+-y_->0.$$

`Rect.measure` 复用原工程二维 Lebesgue 限制测度。`measure_eq_closed` 证明四边零测度允许使用闭矩形代表计算体积分；`integral_fubini` 使用真正的 Fubini。全域没有缩成物理区。

| 条件 | 本轮采用的表示 | 与 V7 的差异及用途 |
|---|---|---|
| 空间光滑 | 场切片有全空间 C∞ 技术延拓；PDE 仅在 Ω 内成立 | 强于 H₀¹/H(div) 弱空间。用真实 `fderiv` 定义 x/y 导数，并由连续代表的 a.e. 唯一性证明导数与四边迹良定义 |
| 混合光滑 | 所用原层与导数层联合 C∞ 延拓 | 从二阶导数对称性证明时间—空间交换；交换公式本身不是输入字段 |
| 普通路径 | 闭矩形 K 上 C(K) 一致范数路径连续、相关路径可微 | 比仅逐点可导强。`UniformTimeJet` 明确列出使用的曲线；由 `evalCLM` 识别导数，经 `continuousToL2` 得到真正 L² 的 HasDerivAt |
| 时间延拓 | 技术延拓的正则性可以在全实轴要求 | 原八条演化只在 (0,T)×Ω 要求，PEC、初值及静态条件覆盖 [0,T]；不是全实轴 PDE 解假设 |
| 吸收 | 实际分离 p(x)、r(y)，非负、时间不变、原幅度限制；所选光滑版本另列光滑条件 | 不要求任何吸收正下界，不对 w 作空间求导。尚未覆盖一般 W¹,∞ 弱解类 |
| 加权路径 | √wφ、√wφ_t、√wφ_tt 的实际 L² 成员；加权路径连续与可微 | 普通光滑不能自动推出这些条件。本轮识别其导数，不证明 (5.7)/(5.8) 的加权正则性自动传播 |
| 初值 | 固定任意 u₀、q₀，五个初始不变量为零；u₀ 四边零迹，零区 φ₀=0 | 不默认 u₀=q₀=0，不要求全时段兼容作为原解输入 |
| T=0 | 内部方程为空；必要初始图状态兼容另列 | 特别不能从某个时刻 E=0 推出任意 E_t=0。T>0 时用连续性将内部结果延至端点 |

`SmoothTimeJet` 的 `value/first/second` 各自是真实空间函数，并有 HasDerivAt 绑定；`UniformTimeJet` 只说一致范数可导，不直接给目标 L² 导数。`SmoothZeroOn` 是中间构造需要的兼容**结论**，最终原系统入口必须从真实保持定理填入，不能作为原系统“正则性”假设。

## 四边 Green 与本轮 Poincaré 常数

实际边界数据依次为右、左、上、下的连续函数。边界配对独立定义为这四条一维积分：

$$
\int_\Omega f\,\mathrm{div}\Lambda
=-\int_\Omega(\partial_x f\,\Lambda_x+\partial_y f\,\Lambda_y)
+\int_{y_-}^{y_+}f(x_+,y)\Lambda_x(x_+,y)\,dy
-\int_{y_-}^{y_+}f(x_-,y)\Lambda_x(x_-,y)\,dy
+\int_{x_-}^{x_+}f(x,y_+)\Lambda_y(x,y_+)\,dx
-\int_{x_-}^{x_+}f(x,y_-)\Lambda_y(x,y_-)\,dx.
$$

零迹逐边消去。主线没有分区积分，也不增加磁场法向约束或内部边界条件。光滑代表相同 L² 类时在闭矩形相等，所以迹不是从任意 L² 代表上读点值。梯度、散度仅定义在光滑代表的 L² 像子空间上，不是整个 L² 上的有界算子。

本轮实际证明的是保守常数

$$C_{P,\mathrm{smooth}}=2L_x,\qquad
\|v\|_2^2\le4L_x^2\bigl(\|\partial_xv\|_2^2+\|\partial_yv\|_2^2\bigr).$$

证明对 $(x-x_-)v^2$ 使用 Green/散度公式，再对非负平方积分作估计。于是本轮必须使用

$$K_{\mathrm{smooth}}=32\mu(\epsilon+2\kappa)L_x^2,\qquad
c_{*,\mathrm{smooth}}=\min\left\{K_{\mathrm{smooth}}^{-1/2},\frac{\kappa\tau}{8AK_{\mathrm{smooth}}},\frac{\kappa}{8A\tau}\right\}.$$

`scaleK_rectangle` 精确核验这一替换，`threshold_rectangle_pos` 证明原材料正性下阈值仍为正。旧阶段到此只完成了符号替换，尚缺保守常数下的具体参数证书；本次由 `ParameterCertificate` 补齐。没有证明原文 (5.1) 的最优 π 常数；合同和原文原样保留。

非平凡调用使用四边为零、内部非零的多项式泡函数。已证明其 L² 类非零，并实际调用 Green、Poincaré 和时间路径求导。这是接口调用，不是 PDE 非零解存在性证明。

## 历史提升、五个不变量与零区

`integralLift` 是实际时间积分：

$$u(t,x)=u_0(x)+\int_0^tE(s,x)\,ds,\qquad
q(t,x)=q_0(x)+\int_0^tP(s,x)\,ds.$$

`HistoryL2` 通过连续线性映射与 Bochner 积分交换，连接逐点历史和 L² 历史。FTC 证明初值与导数；固定初始原函数的历史唯一性不等于任意兼容提升的规范唯一性。

先证明五个实际不变量沿时间等于其初始**空间函数**，再使用初始零值：

$$C_D=q+\tau P-\kappa u,\quad C_{z1}=Z_1+\epsilon bu,\quad C_{z2}=Z_2+bq,
\quad C_x=Q_x-p\phi_y,\quad C_y=Q_y+r\phi_x.$$

两个磁不变量核对了 $\lambda=(\mu H_y,-\mu H_x)$ 的方向，并使用已证真实混合求导。场层定理还给出相应实际 L² 等价类相等，未止于某个点的普通实数验证。一般非零初始不变量的保持已覆盖，但其带源 primitive 版本不属于本轮无源主线。

在零吸收区，$p=r=0$ 和辅助演化给 $\phi_t=0$，还须用初始 $\phi_0=0$ 才推出全时段零值。加权恢复映射在零区取零并不能替代这条原场保持证明。普通场与零区 $c|\nabla v|^2$ 仍保留。

## 学习时怎样看目标

用 VS Code 打开整个 Lean_PML 文件夹。把光标放在 `by` 后及每条 `have`、`calc`、`rw` 后，在 Lean InfoView 查看当时的假设与目标。F12 可跳转项目声明和固定 mathlib 源码；尤其比较“导数存在”“导数值识别”“方程代入”三个步骤。导入显示过期时先在工程终端 `lake build`，再执行 **Lean 4: Restart File**；必要时重新打开文件。

关键 mathlib 来源（都来自当前锁定依赖）：

- `ContDiffAt.isSymmSndFDerivAt`：`.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`。
- `integral_divergence_prod_Icc_of_hasFDerivAt_of_le`：`.lake/packages/mathlib/Mathlib/Analysis/Calculus/DivergenceTheorem.lean`。
- `ContinuousMap.evalCLM`：`.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Algebra.lean`。
- `BoundedContinuousFunction.toLp`：`.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LpSpace/ContinuousFunctions.lean`。
- `ContinuousLinearMap.intervalIntegral_comp_comm`、`intervalIntegral.integral_hasDerivAt_right`：固定依赖的 IntervalIntegral 模块；F12 显示实际声明位置。

## 验证与下一步

固定 Lean v4.31.0 / mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`。四阶段命令、失败与修复输出分别保存于 `logs/v0.4.1` 至 `logs/v0.4.4`；每个 `acceptance.json` 只在对应数学及工程检查通过后写为完成。

```bash
cd '/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML'
lake build
lake env lean Audit.lean
```

要另存本次对齐修复的复现日志：

```bash
python3 scripts/run_logged.py --stage v0.4_alignment lake_build lake build
python3 scripts/run_logged.py --stage v0.4_alignment axioms_audit lake env lean Audit.lean
```

下一阶段 v0.5.1 才把具体接口构造接到 `main_energy_estimate_Conditional` 并发布名称清楚的光滑兼容类先验主定理。本轮不创建 MainSmoothRectangle.lean 或 smooth_theorem.md。弱 H₀¹/H(div) 范围、W¹,∞ 的一般实现、精确 π 常数、(5.7)/(5.8) 自动传播、提升规范唯一性和解存在唯一性均不能因本轮接口构造而自动登记完成。

## 最后怎样进入已有能量框架

推荐改用 [RegionalCoefficients.lean](LeanPML/Rectangle/RegionalCoefficients.lean) 的 `RegionalAbsorption.originalRegionalFiniteIntervalProblem`：输入真实八变量、仅闭坐标区间受幅度限制的分离系数、仅内部的原方程、初始五兼容、PEC、初始零区 φ、强正则性和实际历史的坐标识别，返回旧 `FiniteIntervalProblemConditional`。它没有输入现成的条件性问题，也没有输入 Green、Poincaré、混合交换、全时段兼容或目标能量结论。

`LiftIdentified` 将八个光滑时间槽逐一识别为实际积分提升及磁场重构；不是重新选取无关的 u/q。`original_static_closed` 从初始条件产生闭区间两层静态条件；`original_smoothZeroOn` 从原场零区保持产生加权坐标所需零值，再对邻域零函数求真正的一、二阶导数。`originalFiniteIntervalProblem_second_R_continuous` 另给积分平衡所需 P_tt 的实际 L² 连续性。

T=0 时额外的 `InitialDerivativeCompatible` 只要求初始导数层极化关系及零区 φ_t；不能由空内部方程推出。有限区间能量接口只需要内部 E_t 的零迹；若另外要求整个闭区间 E_t 零迹，`BoundaryTime.velocity_PEC_on_Icc` / `twoLayer_zeroBoundary` 明确要求 T=0 时该初始迹。u 与 E 的闭区间零迹则来自 u₀ 零迹、历史积分与 PEC。

底层 `OriginalAt`/`PrimitiveAt` 用真实 `fderiv` 的总定义书写空间导数。其代数方程定理本身不自动产生空间正则性；旧最高入口的具体解释已依靠 `SmoothStateData` 与 `LiftIdentified` 的真实光滑代表。本次把这一步显式化为 `OriginalClassicalOn` / `PrimitiveClassicalOn`；由光滑识别与 $\mu\ne0$ 导出所需空间可导性，再通过带 `_classical_rectangle` 的双向定理恢复全部八式和 PEC。旧代数证明保持成立，不表示方程自动改善正则性。

任意非零初始不变量的时间保持已经证明；把它们设为零后才得到本轮无源 primitive 对应。带非零不变量的额外源项系统未实现，不混入主范围。固定 u₀、q₀ 的历史唯一性也不等于同一原状态的提升规范唯一性。

| 阶段 | 状态 | 完整输出 | 审计声明数（含历史） |
|---|---|---|---|
| v0.4.1 | 已验收 | [构建](logs/v0.4.1/20261013T224101_375806_lake_build.log) / [审计](logs/v0.4.1/20261013T224142_908894_axioms_audit.log) | 410 |
| v0.4.2 | 已验收 | [构建](logs/v0.4.2/20261013T224801_700595_lake_build.log) / [审计](logs/v0.4.2/20261013T225034_426223_axioms_audit.log) | 429 |
| v0.4.3 | 已验收 | [构建](logs/v0.4.3/20261013T230513_776030_lake_build.log) / [审计](logs/v0.4.3/20261013T230651_423759_axioms_audit.log) | 484 |
| v0.4.4 | 已验收 | [构建](logs/v0.4.4/20261013T230822_044824_lake_build.log) / [审计](logs/v0.4.4/20261013T231144_117778_axioms_audit.log) | 537 |

审计仅出现标准 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx`；证明源码无 sorry/admit/自定义占位公理。构建还检查了此前全部模块。源码哈希、受保护文件复核、独立语义审查见 [最终验收](logs/v0.4.4/acceptance.json)、[语义审查](logs/v0.4.4/semantic_review_geometry.md)；PDF 的范围和证据集中在[原标注账本](docs/pdf_formalization_marks.md)。

## v0.4 对齐：参数、区域和真实空间导数

在实际 `unitSquare : Rect`，即 $\Omega=(-1,1)^2$ 上，取 $\epsilon=\kappa=\tau=\mu=1$。从已证明的 $C_P=2L_x$ 得到

$$C_P=4,\quad A=3,\quad K=384,\quad c=\frac1{16384},\quad S=\frac1{65536}=\frac c4.$$

三条阈值条件的左端精确为

$$c^2K=\frac3{2097152}\le1,\qquad8cAK=\frac9{16}\le1,\qquad8cA\tau=\frac3{2048}\le1.$$

`unitSquare_le_threshold` 调用已有 `le_threshold_iff_explicit.mpr` 得到 $c\le c_*$。原文 §10 的 $c=1/128$ 使用另一 Poincaré 常数；在当前 $K=384$ 下第二条变成 $72\le1$，不成立。`oldC_not_le_threshold` 给出正式对照。这里只补数值参数证书，没有提前实现吸收剖面或非零初值族。

`RegionalAbsorption` 只要求 $x\in[x_-,x_+]$ 时 $0\le p(x)\le S$，以及对应 y 条件。内部取

$$\widetilde p(x)=p(\max(x_-,\min(x_+,x))),\quad
\widetilde r(y)=r(\max(y_-,\min(y_+,y))).$$

截回后的函数连续可测且全轴有界，供旧 L² 乘子实现使用；它不必在截回端点光滑。原技术延拓仍可 C∞，但不再限制其域外幅度，也不要求域外 PDE。`coefficients_eq_closed` 和 `coefficients_ae` 证明闭域逐点及体积分 a.e. 一致；`weights_ae`、`weighted_memLp_iff` 保留零区和可能无界的权重。`fieldEnergy_eq_regional_integral`、`fieldDissipation_eq_regional_integral` 连同各自可积性证明，把已有能量、耗散接回原 $p,r$ 的整个矩形积分。

原空间证据仅要求 E、Hx、Hy 可导；primitive 侧要求 u、E、Λx、Λy 可导，没有给 P/Z/Q 增加无关空间条件。`hasDerivAt_spaceDx_of_differentiable` 和 y 版本从真实 Fréchet 可导性推出坐标切片的 HasDerivAt。最终区域入口实际调用“光滑识别 → 古典原解 → 域内系数改写 → 古典 primitive → 有限区间接口”，不是仅增加未被调用的类型标签。

当前仍采用强于 V7 (6.6) 的联合 C∞ 技术延拓、C(K) 一致范数路径条件，以及真实加权成员资格/连续可微性。这些是为兑现接口而选择的正则性输入，**不是由论文弱空间假设推出**。普通光滑没有取代加权正则性；全时段兼容与零区保持则由初值和原演化证明。有限区间问题构造只需要 $\mu\ne0$；使用后续能量定理时仍须原材料正性和对应阈值，不能把这个构造自身当成完整先验定理。

本次逐项范围及历史更正见 [对齐记录](logs/v0.4_alignment/alignment_record.md) 和 [独立语义检查](logs/v0.4_alignment/semantic_review.md)。构建、审计及 PDF 验收结果在本次 [验收记录](logs/v0.4_alignment/acceptance.json) 中登记；旧 v0.4 日志仅对应旧源码。

本次对齐验证： [完整构建](logs/v0.4_alignment/20261014T000055_917026_lake_build.log)、[独立审计](logs/v0.4_alignment/20261014T000341_178705_axioms_audit.log)、[类型检查](logs/v0.4_alignment/20261014T000341_178709_interface_types.log) 均退出 0；共审计590个声明，新增53项。PDF页3/4/7/15已按实际范围对齐，详见[账本](docs/pdf_formalization_marks.md)及[视觉检查](logs/v0.4_alignment/pdf/visual_review.json)。
