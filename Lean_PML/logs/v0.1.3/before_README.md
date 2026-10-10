# LeanPML：Debye 子系统的真实耗散

用途：解释 v0.1.2 如何把两条实际时间微分方程变成能量耗散、有限区间单调性和初值界，并指导你逐行查看 Lean 证明。实际验证及完整日志见 [PROGRESS.md](PROGRESS.md)。旧标量教学代码、[模型合同](docs/model_contract.md)、[PML 范围](docs/scope.md) 和历史日志保持原内容。

## 本阶段的数学对象与主结论

实际函数 $E,P:\mathbb R\to\mathbb R$ 分别表示电场和极化随时间的变化。材料参数 $\epsilon,\kappa,\tau$ 是时间不变的正实数。给定 $T\ge0$，只要求 $E,P$ 在 $[0,T]$ 连续，并在 $(0,T)$ 满足

$$
\epsilon E'(t)=-P'(t),\qquad
\tau P'(t)+P(t)=\kappa E(t).
$$

这正是 [路线图 §3.1、v0.1.2](ROADMAP_lean_PML_revised.md) 的无空间耦合时间子系统。在命名空间 `LeanPML.Debye` 定义

$$
\mathcal E(t)=\frac{\epsilon E(t)^2+P(t)^2/\kappa}{2},
\qquad
\mathcal D(t)=\frac{(\kappa E(t)-P(t))^2}{\kappa\tau}.
$$

`energy`、`dissipation` 都是具体函数定义；定义没有附带能量律、非负性或单调性假设。已证明

$$
\mathcal E(t)\ge0,\qquad
\mathcal E'(t)=-\frac\tau\kappa P'(t)^2=-\mathcal D(t)\le0\quad(t\in(0,T)),
$$

$$
0\le s\le t\le T\Longrightarrow\mathcal E(t)\le\mathcal E(s),
\qquad
0\le\mathcal E(t)\le\mathcal E(0)\quad(t\in[0,T]).
$$

主定理 `antitoneOn_energy` 的实际输入为：（各种假设）

```lean
(ε κ τ T : ℝ) (E P : ℝ → ℝ)
(_hε : 0 < ε) (hκ : 0 < κ) (hτ : 0 < τ) (hT : 0 ≤ T)
(hEcont : ContinuousOn E (Set.Icc 0 T))
(hPcont : ContinuousOn P (Set.Icc 0 T))
(hODE : ∀ t ∈ Set.Ioo 0 T, ∃ dE dP : ℝ,
  HasDerivAt E dE t ∧ HasDerivAt P dP t ∧
  ε * dE = -dP ∧ τ * dP + P t = κ * E t)
```

结论是 `AntitoneOn (energy ε κ E P) (Set.Icc 0 T)`。参数表中没有任何待证能量结论。两个函数的类型在实轴上定义，但一般定理只在开区间要求方程。

| Lean 对象 | 自然语言 |
|---|---|
| `E P : ℝ → ℝ` | 两个真实时间函数 |
| `ε κ τ : ℝ` | 与时间无关的材料常数 |
| `HasDerivAt E dE t` | $E$ 在 $t$ 可导，且导数值为 $dE$ |
| `∃ dE dP, ...` | 在当前时刻有导数值及其真实证据，不要求预先给全轴导数函数 |
| `ContinuousOn E (Set.Icc 0 T)` | 闭区间内连续，端点按相对于区间的连续性理解 |
| `Set.Ioo 0 T` | 开区间 $(0,T)$ |
| `AntitoneOn f (Set.Icc 0 T)` | 两时刻 $s\le t$ 都在区间内时，$f(t)\le f(s)$ |
| `0 ≤ energy ... t ∧ energy ... t ≤ energy ... 0` | 同时给出非负性和初值上界 |

单独给一个叫 `dP` 的实数不能证明它是 $P'$。本项目先要求 `HasDerivAt`，再使用代数方程；`hODE` 中两条导数证据不可省略。

## 两种耗散公式如何从原方程得到

[Debye/ScalarEnergy.lean](LeanPML/Debye/ScalarEnergy.lean) 按下面的纸面顺序证明：

$$
\begin{aligned}
\mathcal E'
&=\epsilon E\,dE+\frac P\kappa dP
&&\text{（平方求导、常数运算与相加）}\\
&=-E\,dP+\frac P\kappa dP
&&\text{（代入 }\epsilon dE=-dP\text{）}\\
&=-\frac{\kappa E-P}{\kappa}\,dP
=-\frac\tau\kappa dP^2
&&\text{（代入 }\tau dP+P=\kappa E\text{）}.
\end{aligned}
$$

第一步的交付仍是 `HasDerivAt`，同时证明导数存在及公式。`ring` 只负责整理代数，不会替代求导规则。`hasDerivAt_energy_rate` 对应路线图 §3.1 的导数平方形式。

第二方程还给出 $\kappa E-P=\tau dP$。由非零分母得到

$$
\mathcal D
=\frac{(\kappa E-P)^2}{\kappa\tau}
=\frac{(\tau dP)^2}{\kappa\tau}
=\frac\tau\kappa dP^2.
$$

这就是 `dissipation_eq_rate`。它是代数连接引理，实际导数身份由调用它的 `HasDerivAt` 定理提供。`hasDerivAt_energy_dissipation` 最后交付

```lean
HasDerivAt (energy ε κ E P) (-dissipation κ τ E P t) t
```

展开 `dissipation` 就得到 $-(\kappa E-P)^2/(\kappa\tau)$。没有把两种公式的等价性当成输入假设。

| 条件 | 使用位置 |
|---|---|
| $\epsilon>0$ | 与 $E^2\ge0$ 一起证明能量非负；初值双边界使用它 |
| $\kappa\ne0$ | 局部第一耗散公式中合法使用 $E=(\tau dP+P)/\kappa$ |
| $\kappa\ne0,\tau\ne0$ | `dissipation_eq_rate` 中 `field_simp [hκ, hτ]` 合法消分母 |
| $\kappa>0,\tau>0$ | $\kappa>0$ 还用于 $P^2/\kappa\ge0$；二者保证 $\kappa\tau>0$，从残差平方非负得到 $\mathcal D\ge0$，并提供上述非零证据 |
| $E,P$ 闭区间连续 | 能量闭区间连续，满足一般时间引理的端点比较条件 |
| 内部真实 ODE | 内部能量 `HasDerivAt` 证据及导数公式 |
| $T\ge0$ | 区分单点/正长度区间，并保证初时刻 $0\in[0,T]$ |

单调性证明本身不用 $\epsilon$ 的符号。主定理用 `_hε` 明确保留用户指定的正材料范围；在能量非负及初值界中，$\epsilon>0$ 确实被使用。局部辅助引理采用它们所需的较少假设，不改变主定理范围。

## 已实现的声明与依赖

以下名称省略共同前缀 `LeanPML.Debye.`。本阶段新增 4 个定义（能量、耗散、两个实例函数）和 20 条定理。

| 定理 | 输入 → 结论／依赖 |
|---|---|
| `energy_nonneg` | $\epsilon,\kappa>0$ → 能量非负；不需要方程 |
| `continuousOn_energy` | 两函数在任意集合连续 → 能量在同集合连续；无方程/符号要求 |
| `hasDerivAt_energy_of_hasDerivAt` | 两个真实点导数 → 未代入 ODE 的求导公式 |
| `hasDerivAt_energy_rate` | 点导数、两方程、$\kappa\ne0$ → $\mathcal E'=-(\tau/\kappa)dP^2$ |
| `dissipation_eq_rate` | 极化代数方程、$\kappa,\tau\ne0$ → 两种耗散表达式相等 |
| `hasDerivAt_energy_dissipation` | 点导数、两方程、$\kappa,\tau\ne0$ → 真实导数为 $-\mathcal D$ |
| `dissipation_nonneg` | $\kappa,\tau>0$ → $\mathcal D\ge0$；无需方程 |
| `energy_deriv_nonpos` | 点导数、两方程、$\kappa,\tau>0$ → 实际能量导数非正 |
| `hasDerivAt_energy_on_Ioo` | 内部 `hODE`、$\kappa,\tau\ne0$ → 内部逐点 `HasDerivAt` |
| `antitoneOn_energy_zero` | 任意参数与函数 → $[0,0]$ 上单调不增；无连续/导数假设 |
| `antitoneOn_energy` | 三正材料、$T\ge0$、两函数闭区间连续、内部 ODE → 闭区间单调不增 |
| `energy_bounds` | 主定理输入和 $t\in[0,T]$ → $0\le\mathcal E(t)\le\mathcal E(0)$ |
| `hasDerivAt_exampleE`、`hasDerivAt_exampleP` | 任意时刻 → 两个显式函数的真实导数公式 |
| `continuous_exampleE`、`continuous_exampleP` | 从上两条真实导数证据推出全轴连续 |
| `example_ode` | 两个已证导数及代数整理 → 全轴两条真实方程 |
| `example_initial` | $\exp(0)=1$ → 两个非零初值、初能量为 1 |
| `example_energy_antitone` | $T\ge0$ → 调用一般主定理获得实例区间单调性 |
| `example_energy_bounds` | $T\ge0,t\in[0,T]$ → 调用一般初值界得到 $0\le\mathcal E(t)\le1$ |

证明连接是：

```text
E、P 的连续性 ──→ energy 连续 ───────────────────────────┐
真实点导数 ──→ 原始求导 ──→ 代入两方程 ──→ -dissipation ├─→ 时间引理 ──→ AntitoneOn
κ、τ 正 ──→ dissipation 非负 ──→ 导数非正 ─────────────┘
ε、κ 正 ──→ energy 非负 ───────────────────────────────→ 与 AntitoneOn 合并为初值界
```

使用的时间引理仍是 v0.1.1 的 `LeanPML.Time.antitoneOn_Icc_of_hasDerivAt_nonpos`。主定理直接交付连续性、真实导数证据和已证明的符号，不重建中值定理。mathlib 的 `deriv` 是总定义；本项目对它作符号结论之前，始终先有 `HasDerivAt` 证据。

## 闭区间、端点与 T=0

比较 $0\le s<t\le T$ 时，中值定理只需要能量在 $[s,t]$ 连续、在 $(s,t)$ 内可导。原假设覆盖这些条件，因此不用端点处的普通双侧导数，也不要求区间外存在解。

$T=0$ 时所有比较都退化为同一点。独立的 `antitoneOn_energy_zero` 不需要参数正性、连续性或导数；主定理零分支直接调用它，不拆解 `hODE`。$(0,0)$ 为空，内部导数条件没有任何待检查的时刻。

## 非零实例如何调用一般定理

取 $\epsilon=\kappa=\tau=1$，定义

$$
E(t)=e^{-2t},\qquad P(t)=-e^{-2t}.
$$

源码先通过真实链式法则证明 $E'=-2e^{-2t}$，再通过取负的求导规则证明 $P'=2e^{-2t}$。在已有导数证据后，才用代数整理验证

$$
E'=-P',\qquad P'+P=E.
$$

连续性由可导性得到，初值由 $\exp(0)=1$ 得到：

$$
E(0)=1,\qquad P(0)=-1,\qquad\mathcal E(0)=1.
$$

`example_energy_antitone` 将正参数、连续性及 `fun t _ => example_ode t` 传给一般主定理。`example_energy_bounds` 调用一般 `energy_bounds`，最后用已证初能量等于 1 改写上界。没有靠数值采样或另算一个指数能量公式绕过一般定理。

这个例子确实提供了一个非零真实解的见证；它不证明一般初值问题的存在唯一性。只在此实例中证明了全实轴方程，一般主定理仍只要求内部 ODE。

## 学习顺序与 InfoView

1. 先读本 README 的数学对象和两种耗散公式。
2. 需要复习单函数求导时读 [LocalEnergy.lean](LeanPML/Tutorial/LocalEnergy.lean)；上一阶段完整练习仍在 [Tutorial/ScalarEnergy.lean](LeanPML/Tutorial/ScalarEnergy.lean)。
3. 读 [Time/Monotonicity.lean](LeanPML/Time/Monotonicity.lean)，复习闭区间连续、内部导数到 `AntitoneOn` 的接口。
4. 按顺序读 [Debye/ScalarEnergy.lean](LeanPML/Debye/ScalarEnergy.lean)：定义 → 非负/连续 → 局部求导 → 消元/符号 → 区间主定理 → 显式实例。
5. 读 [LeanPML.lean](LeanPML.lean)、[Audit.lean](Audit.lean) 和 [PROGRESS.md](PROGRESS.md)，检查构建覆盖和证据。

在 VS Code 用“打开文件夹”打开整个 `Lean_PML` 工程。打开 Debye 文件后，按 `Cmd+Shift+P` 运行 `Lean 4: InfoView: Display Goal`；或用 `Lean 4: InfoView: Toggle InfoView` 显示面板。

- 在 `hasDerivAt_energy_rate` 的 `apply` 前后移动光标：目标从真实导数变成待核对的导数值等式；在 `calc` 各行查看使用了哪条原方程。
- 在 `dissipation_eq_rate` 的 `field_simp` 前查看上下文中的 `hκ : κ ≠ 0`、`hτ : τ ≠ 0`，理解为什么能消分母。
- 在 `hasDerivAt_energy_on_Ioo` 的 `rcases` 后查看 `dE,dP,hE,hP,hMaxwell,hDebye`：导数值和导数证据被同时取出。
- 在主定理的 `apply` 后查看剩余的符号目标；在 `energy_bounds` 的 `constructor` 后看两个子目标；最后对比显式实例调用时参数如何填入。

`⊢` 后是当前目标，上方是已知对象和假设。`intro` 引入对象；`have` 命名事实；`rw` 按等式替换；`exact` 交付证明；`change` 换成定义上相同的表达式；`ring` 检查代数；`norm_num` 处理精确常数计算。代码在各步都有中文批注。

悬停名称查看类型，F12 或右键 “Go to Definition” 查看定义；可用 `Lean 4: InfoView: Toggle Pin` 固定一个状态。若命令行成功而编辑器未刷新，运行 `Lean 4: Server: Restart File`。不需要删代码或插入占位证明。操作依据本机已安装扩展的 [官方手册](</Users/wcli/.vscode/extensions/leanprover.lean4-0.0.237/manual/manual.md:259>)，本轮核对了命令配置，未安装或修改扩展。

## 固定版本、构建与公理审计

| 项目 | 固定值 |
|---|---|
| 工具链 | `leanprover/lean4:v4.31.0` |
| Lean 提交 | `68218e876d2a38b1985b8590fff244a83c321783` |
| Lake | `5.0.0-src+68218e8` |
| mathlib | `v4.31.0`，提交 `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` |
| 配置 | [lean-toolchain](lean-toolchain)、[lakefile.toml](lakefile.toml)、[lake-manifest.json](lake-manifest.json) |

配置和依赖锁定本轮保持不变，没有执行 `lake update` 或改全局默认工具链。Lake 包元数据 `leanPML / 0.0.3` 与研究阶段 v0.1.2 分开记录。

在终端重新运行并保留完整日志：

```sh
cd '/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML'
python3 scripts/run_logged.py --stage v0.1.2 lake_build lake build
python3 scripts/run_logged.py --stage v0.1.2 axioms_audit lake env lean Audit.lean
```

也可以直接运行 `lake build`、`lake env lean Audit.lean`，但上面的记录器会保留每次命令、工作目录、退出码和完整合并输出。新时间戳日志写入 `logs/v0.1.2/`，不会覆盖旧记录。记录器需要 Python 3.9+；Lean 构建本身不依赖 Python。

在有 elan、Git 的新机器上，保留锁定配置，先取需要的缓存再构建：

```sh
lake exe cache get Mathlib.Analysis.Calculus.Deriv.MeanValue Mathlib.Analysis.Calculus.Deriv.Pow Mathlib.Analysis.Calculus.Deriv.Mul Mathlib.Analysis.Calculus.Deriv.Add Mathlib.Analysis.SpecialFunctions.ExpDeriv Mathlib.Tactic.FieldSimp Mathlib.Tactic.Ring Mathlib.Tactic.NormNum
lake build
lake env lean Audit.lean
```

默认目标仍为 `LeanPML` 和 `Audit`；正式入口显式导入三个旧模块和新的 Debye 模块。所有 32 条项目定理（旧 12 条、新 20 条）都在 `Audit.lean` 中列入 `#print axioms`。实际输出和失败修复过程见进度日志。

标准依赖 `propext`、`Classical.choice`、`Quot.sound` 分别是命题外延性、经典选择和商类型基础原则，不是未完成证明；验收检查无 `sorryAx` 或自定义占位公理，并同时检查命题类型。新增正式模块要接入导入链，新定理要接入审计，再实际构建留档。

## 与完整 PML 的联系和下一阶段

[模型合同 §3](docs/model_contract.md) 的完整电场方程也含有 $-P_t$，乘以 $E$ 后出现 $-EP_t$；极化能量求导带来 $(P/\kappa)P_t$。本阶段形式化了二者结合成负耗散平方的时间运算。这为后续极化块的求导与抵消提供可核验的基本步骤。

完整模型还含空间旋度、磁场、PML 系数和辅助量。本阶段没有证明这些剩余项可抵消或受控，也没有构造 V7 的两层能量。仍需原八变量与提升对应、五不变量保持、Green/PEC、时间空间导数交换、加权状态与图范数控制、矩形 Poincaré、两层耗散闭合和积分平衡。合同中点态/空间积分的区分仍保留，不能把本例直接当作空间积分定理。

一般结论是给定解的先验能量估计，允许能量相等；没有证明一般初值问题存在唯一性或严格递减。它不是完整二维 PML 定理。

下一阶段 **v0.1.3 尚未开始**，计划入口 `LeanPML/PML/TimeInvariants.lean`：
从真实 $u'=E,q'=P,\tau P'+P=\kappa E$ 推出 $q+\tau P-\kappa u$ 时间恒定；从 $Z_1'=-\epsilon bE,Z_2'=-bP$ 推出 $Z_1+\epsilon bu$、$Z_2+bq$ 恒定，并证明零初值保持。先明确为固定空间点的时间结果，场空间与磁辅助不变量后续完成。本轮未创建该模块。
