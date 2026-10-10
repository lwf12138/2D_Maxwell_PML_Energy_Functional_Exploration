# LeanPML：真实时间不变量与模型接口

用途：解释 v0.1.3 如何把原方程的真实导数证据变成“保持初值”，再从初始兼容推出全时段兼容。本页是中文阅读入口；实际验证和历史记录见 [PROGRESS.md](PROGRESS.md)。本阶段已完成，未进入 v0.2.1。上一阶段 Debye 教程原文保存在 [修改前 README](logs/v0.1.3/before_README.md)，包括原有批注；旧代码、模型合同、路线图和旧日志保留。

## 数学范围与三个不变量

本阶段固定一个空间点，研究真实函数 $u,q,E,P,Z_1,Z_2:\mathbb R\to\mathbb R$。参数 $\epsilon,\kappa,\tau,b$ 与时间无关。完整模型的 $b=p(x)r(y)$ 可以随空间变化，固定点之后才是这里的实常数；“保持常数”仅指沿时间保持。

在命名空间 `LeanPML.PML` 定义三个时间函数：

$$
C_D(t)=q(t)+\tau P(t)-\kappa u(t),\qquad
C_{z1}(t)=Z_1(t)+\epsilon b u(t),\qquad
C_{z2}(t)=Z_2(t)+bq(t).
$$

这对应 [模型合同 §5.1–5.2](docs/model_contract.md) 的 V7 (2.4) 中三个标量不变量及初始兼容关系。代码定义名为 `CD`、`CZ1`、`CZ2`，定义本身不附带恒定性或兼容性假设。

给定 $T\ge0$，以下三行**分别**列出相应保持定理需要的条件，并非每条定理都要求所有条件。

| 不变量／保持定理 | 在 $[0,T]$ 连续的函数 | 仅在 $(0,T)$ 要求的真实微分方程 |
|---|---|---|
| $C_D$／`CD_eq_initial` | $u,q,P$ | $u'=E,\ q'=P,\ \tau P'+P=\kappa E$ |
| $C_{z1}$／`CZ1_eq_initial` | $u,Z_1$ | $u'=E,\ Z_1'=-\epsilon bE$ |
| $C_{z2}$／`CZ2_eq_initial` | $q,Z_2$ | $q'=P,\ Z_2'=-bP$ |

每条定理对任意 $t\in[0,T]$ 得到 $C(t)=C(0)$，保留任意初始常数。不需要 $E$ 的导数、$E$ 的连续性、教学子系统方程 $\epsilon E'=-P'$ 或磁场数据。

这些恒等式对任意实常参数成立，证明不使用参数正性或非零性。因此它们包含合同的物理范围 $\epsilon,\kappa,\tau>0,\ b\ge0$，并保留 $b=0$；这不改变完整 PML 合同的假设。本阶段没有除以 $b$，也没有吸收正下界。

## 自然语言如何变成 Lean 输入

| Lean 写法 | 含义与用途 |
|---|---|
| `u q E P : ℝ → ℝ` | 随真实时间变化的函数；定义域为实轴不代表方程要求在全轴成立 |
| `κ τ : ℝ` | 与时间无关的常数；使用 `const_mul` 时不产生系数导数项 |
| `Set.Icc 0 T`、`Set.Ioo 0 T` | 闭区间 $[0,T]$、开区间 $(0,T)$ |
| `ContinuousOn u (Set.Icc 0 T)` | 包括端点的区间连续性；用于内部分析结论的端点比较 |
| `HasDerivAt u (E t) t` | $u$ 在时刻 $t$ 可导，并且其导数值是 $E(t)$ |
| `∀ s ∈ Set.Ioo 0 T, ...` | 对每个内部时刻都有对应证据 |
| `∃ dP : ℝ, HasDerivAt P dP s ∧ ...` | 同时提供一个导数值、该值确为实际导数的证据及方程 |
| `hinit : q 0 + τ * P 0 - κ * u 0 = 0` | 只在初时刻要求兼容，不能替换成逐时刻兼容假设 |

例如 `CD_eq_initial` 的导数输入是：

~~~lean
(hu : ∀ s ∈ Set.Ioo 0 T, HasDerivAt u (E s) s)
(hq : ∀ s ∈ Set.Ioo 0 T, HasDerivAt q (P s) s)
(hP : ∀ s ∈ Set.Ioo 0 T, ∃ dP : ℝ,
  HasDerivAt P dP s ∧ τ * dP + P s = κ * E s)
~~~

`dP : ℝ` 单独只是实数；即使改名为 `Pt`，也没有表达导数。`HasDerivAt P dP s` 才把它和实际函数 $P$ 联系起来。三个目标零导数都由这些原方程推出，未作为具体模型的输入。

## 证明链：求导、常值、兼容是三个步骤

[TimeInvariants.lean](LeanPML/PML/TimeInvariants.lean) 的局部证明先用 `add`、`sub`、`const_mul` 对实际函数求导，然后整理导数值：

$$
\begin{aligned}
C_D'(t)&=P(t)+\tau dP-\kappa E(t)=0,\\
C_{z1}'(t)&=-\epsilon bE(t)+\epsilon bE(t)=0,\\
C_{z2}'(t)&=-bP(t)+bP(t)=0.
\end{aligned}
$$

第一行最后一步使用 $\tau dP+P(t)=\kappa E(t)$。Lean 中 `congr_deriv` 用已证明的等式替换导数值，`ring` 整理多项式；它们不承担导数存在性的证明。时间常参数很重要：若 $\tau,\kappa,\epsilon,b$ 是时间函数，求导会出现额外项，当前引理便不能直接应用。

仅在一个时刻导数为零，不能推出一段时间内恒定。[Time/Constancy.lean](LeanPML/Time/Constancy.lean) 接受闭区间连续和**每个内部时刻**的 `HasDerivAt F 0 t`，复用 v0.1.1 的时间单调性接口：

$$
F'\equiv0
\ \Longrightarrow\
F,\ -F\text{ 都单调不增}
\ \Longrightarrow\
F(t)\le F(0),\ -F(t)\le-F(0)
\ \Longrightarrow\
F(t)=F(0).
$$

这里调用 `LeanPML.Time.antitoneOn_Icc_of_hasDerivAt_nonpos`，底层仍使用 mathlib 的中值定理推论，没有重建微积分基础。`ContinuousOn` 的加法、减法和常数乘法规则提供不变量的闭区间连续性。

最后三个 `*_compatibility` 定理额外接收 $C(0)=0$，由 $C(t)=C(0)=0$ 得到：

$$
q(t)+\tau P(t)=\kappa u(t),\qquad
Z_1(t)=-\epsilon bu(t),\qquad Z_2(t)=-bq(t).
$$

代码的 `.trans hinit` 对应“保持初值 + 初值为零”；随后 `sub_eq_zero` 或 `eq_neg_of_add_eq_zero_left` 改写等式。初始兼容是输入，全时段兼容是结论。

## 端点、退化区间和零吸收

比较 $0$ 与 $t\in[0,T]$ 时，中值定理只用闭区间连续和内部可导。因此包含 $t=T$，无需端点普通双侧导数，也不要求区间外的方程。

`eq_initial_on_Icc_zero` 单独证明：$t\in[0,0]$ 就有 $t=0$，任意函数满足 $F(t)=F(0)$。主常值定理显式分出 $T=0$ 分支，不使用连续性或导数条件；$(0,0)$ 为空，无需提供任何内部时刻的导数证据。

$b=0$ 时，原辅助方程化为 $Z_1'=Z_2'=0$，相应不变量就是 $Z_1,Z_2$。`Z1_eq_initial_of_zero_absorption` 和 `Z2_eq_initial_of_zero_absorption` 实例化前述一般保持定理，得到各自保持初值；两个 `*_zero_of_zero_absorption` 再输入零初值，得到整个区间为零。这些专用推论只要求对应 $Z_i$ 的连续性和内部真实零导数。

实例化时选取常零的辅助函数填充已经不影响结论的 $u,E$ 或 $q,P$ 参数。这是证明中选用的函数，不是在要求原模型的这些变量为零。

## 零不变量允许非零状态：正式实例

复用 v0.1.2 已证明导数和连续性的实际函数：

$$
E(t)=e^{-2t},\qquad P(t)=-e^{-2t}.
$$

取 $\epsilon=\kappa=\tau=b=1$，本阶段定义

$$
u(t)=\frac{1-e^{-2t}}2,\qquad q(t)=\frac{1+e^{-2t}}2,\qquad
Z_1(t)=-u(t),\qquad Z_2(t)=-q(t).
$$

源码用真实求导规则证明 $u'=E,q'=P,Z_1'=-E,Z_2'=-P$，再结合已有 $P'=2e^{-2t}$ 验证 $P'+P=E$；连续性由可导性得到。`example_initial_compatibility` 只计算初时刻的三个不变量为零，`example_nonzero_initial` 验证

$$
P(0)=-1,\qquad q(0)=1,\qquad Z_2(0)=-1,\qquad q(0)\ne0.
$$

因此初始兼容约束允许非零原变量 $P,Z_2$，也允许非零提升变量 $q$。它限制的是变量之间的关系，不是要求每个变量为零。

`example_compatibility_on_Icc` 将实例的连续性、真实方程和初始兼容证据，分别交给 `CD_compatibility`、`CZ1_compatibility`、`CZ2_compatibility`。因此任意 $T\ge0$、$t\in[0,T]$ 都满足上述兼容关系。没有用全时段的代数定义直接化简来绕过一般定理。只有这个显式实例证明全轴方程；一般保持定理仍只输入内部方程。

## 新声明与依赖索引

本阶段新增 7 个定义、27 条定理。其中常值接口 2 条，PML 模块 25 条；旧 32 条定理保留，总计 59 条均列入审计。

| 模块／名称 | 输入 → 结论；依赖 |
|---|---|
| `Time.eq_initial_on_Icc_zero` | 单点成员条件 → 任意函数等于初值 |
| `Time.eq_initial_of_hasDerivAt_zero` | $T\ge0$、闭区间连续、内部真实零导数 → 等于初值；调用时间单调性接口 |
| `PML.CD`、`PML.CZ1`、`PML.CZ2` | 三个具体线性组合定义 |
| `PML.hasDerivAt_CD_zero`、`hasDerivAt_CZ1_zero`、`hasDerivAt_CZ2_zero` | 对应实际点导数和原方程 → 局部真实零导数 |
| `PML.continuousOn_CD`、`continuousOn_CZ1`、`continuousOn_CZ2` | 对应组成函数连续 → 不变量连续，适用于任意集合 |
| `PML.CD_eq_initial`、`CZ1_eq_initial`、`CZ2_eq_initial` | 本页首表条件 → 任意初值保持；使用连续性、局部零导数和常值接口 |
| `PML.CD_compatibility`、`CZ1_compatibility`、`CZ2_compatibility` | 上行条件 + 初时刻兼容 → 全闭区间兼容 |
| `PML.Z1_eq_initial_of_zero_absorption`、`Z2_eq_initial_of_zero_absorption` | $T\ge0$、对应 $Z_i$ 连续及内部零导数 → 保持初值；实例化一般保持定理 |
| `PML.Z1_zero_of_zero_absorption`、`Z2_zero_of_zero_absorption` | 上行 + 对应 $Z_i(0)=0$ → 全区间为零 |
| `PML.exampleU`、`exampleQ`、`exampleZ1`、`exampleZ2` | 四个实际函数定义；复用 Debye 的实际 $E,P$ |
| `PML.hasDerivAt_exampleU`、`hasDerivAt_exampleQ`、`hasDerivAt_exampleZ1`、`hasDerivAt_exampleZ2` | 真实求导规则 → 四个全轴导数公式 |
| `PML.example_continuous`、`example_polarization` | 可导性 → 连续性；已有 $P'$ 证据 + 代数 → 极化方程 |
| `PML.example_initial_compatibility`、`example_nonzero_initial` | 精确计算 → 零不变量初值与非零原变量初值 |
| `PML.example_compatibility_on_Icc` | $T\ge0,t\in[0,T]$ → 调用一般定理验证实例的全时段兼容 |

表中名称省略统一前缀 `LeanPML.`；同一行后续名称继承该行的命名空间。

## 阅读顺序与 VS Code InfoView

1. 本 README：先对照三个不变量的假设表与证明链。
2. [Time/Monotonicity.lean](LeanPML/Time/Monotonicity.lean) → [Time/Constancy.lean](LeanPML/Time/Constancy.lean)：读懂如何从导数符号到单调性，再从两向比较到相等。
3. [PML/TimeInvariants.lean](LeanPML/PML/TimeInvariants.lean)：定义 → 局部求导 → 连续性 → 任意初值保持 → 零初始兼容 → 零吸收 → 非零实例。
4. [Debye/ScalarEnergy.lean](LeanPML/Debye/ScalarEnergy.lean)：需要时回看 `exampleE`、`exampleP` 的链式法则及上阶段耗散证明。基础平方求导仍在 [LocalEnergy.lean](LeanPML/Tutorial/LocalEnergy.lean)。
5. [LeanPML.lean](LeanPML.lean) → [Audit.lean](Audit.lean) → [PROGRESS.md](PROGRESS.md)：查看默认构建覆盖和实际证据。

在 VS Code 用“打开文件夹”打开整个 `Lean_PML` 工程，打开目标 `.lean` 文件，用 `Cmd+Shift+P` 运行 `Lean 4: InfoView: Display Goal` 或 `Lean 4: InfoView: Toggle InfoView`。将光标移到以下 tactic 前后：

- `hasDerivAt_CD_zero` 的 `have h`、`apply h.congr_deriv`、`calc`：看真实求导目标如何变成导数值的等式，极化方程在哪一步消去残差。
- `CD_eq_initial` 的 `apply`、`intro s hs`、`rcases`：看逐点目标以及 `dP`、`hdP`、`hDebye` 如何同时进入上下文。
- `eq_initial_of_hasDerivAt_zero` 的 `by_cases`、两个单调性结论与最后的 `exact`：看单点分支、单调性和相等分别如何得到。
- `CD_compatibility` 的 `have hz`、`change`：区分 `hinit` 中的时刻 $0$ 与结论中的时刻 $t$。
- `example_compatibility_on_Icc` 的三个分支：查看实例怎样给一般定理逐项提供证据。

`⊢` 后是当前目标，上方是对象和假设；`intro` 引入量词，`rcases` 拆出存在证据，`exact` 交付证明，`change` 改写为定义上相同的表达式，`simpa` 在化简后复用已有证明。悬停名称看类型，F12 看定义；`Lean 4: InfoView: Toggle Pin` 可固定状态。若编辑器未刷新，用 `Lean 4: Server: Restart File`，无需在正式证明中插入占位代码。主要定义和步骤均有中文批注。

## 固定环境、构建与审计

| 项目 | 固定值 |
|---|---|
| 工具链 | `leanprover/lean4:v4.31.0` |
| Lean 提交 | `68218e876d2a38b1985b8590fff244a83c321783` |
| Lake | `5.0.0-src+68218e8` |
| mathlib | `v4.31.0`，提交 `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` |
| 配置 | [lean-toolchain](lean-toolchain)、[lakefile.toml](lakefile.toml)、[lake-manifest.json](lake-manifest.json) |

本轮未更新依赖或全局默认工具链。Lake 包元数据 `leanPML / 0.0.3` 与研究阶段 v0.1.3 分开记录，配置仍保持原样。

复制到终端即可重新运行并产生新的完整日志：

~~~sh
cd '/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML'
python3 scripts/run_logged.py --stage v0.1.3 lake_build lake build
python3 scripts/run_logged.py --stage v0.1.3 axioms_audit lake env lean Audit.lean
~~~

也可以直接运行 `lake build`、`lake env lean Audit.lean`。上面的记录器需要 Python 3.9+，会在 `logs/v0.1.3/` 留下命令、工作目录、退出码及完整合并输出，保留失败重试，不覆盖旧日志。

本阶段实际证据：[最终默认构建](logs/v0.1.3/20261010T110154_522300_lake_build_retry.log)、[独立公理审计](logs/v0.1.3/20261010T110440_468487_axioms_audit.log)。两者均退出码 0；同名 `.json` 保存元数据。首轮构建的真实错误和修复说明见进度记录。

默认目标仍为 `LeanPML`、`Audit`。正式入口显式导入全部 6 个正式模块；审计共 59 条定理，包含新增 27 条。输出仅含标准基础依赖 `propext`（命题外延性）、`Classical.choice`（经典选择）、`Quot.sound`（商类型基础原则），没有 `sorryAx` 或自定义占位公理。构建与审计确认具体 Lean 命题的证明，模型含义还需结合本页假设表核验。

以后新增正式模块时：

1. 在 `LeanPML/` 对应目录建立文件，使用明确命名空间。
2. 加入 `LeanPML.lean` 的正式导入链，保证默认构建能到达它。
3. 在 `Audit.lean` 为交付定理增加 `#print axioms 完整名称`。
4. 实际执行上述构建与审计，将结果和数学范围记录到对应阶段日志与进度中。

新机器依赖获取仍由 Lake 按现有 manifest 管理；保留锁定文件，不需要用 `lake update` 追随新版本。缓存获取说明见 [上一阶段 README](logs/v0.1.3/before_README.md)，本阶段没有新增 mathlib 外部依赖。

## 与 v0.1.2、完整 PML 和下一阶段的关系

v0.1.2 将无空间耦合子系统的两条方程合成能量导数负平方项，再得到能量单调不增。本阶段使用其中的极化方程和提升/电辅助方程，证明三个线性组合沿时间不变。二者复用真实 `HasDerivAt` 和有限闭区间时间接口；本阶段的三个不变量不需要 $\epsilon E'=-P'$，导数目标是等于零，而非能量导数非正。

本阶段只完成 V7 (2.4) 的三个标量时间不变量在固定空间点的版本，以及对应零初值关系的时间保持。尚未完成：

- 两个磁辅助不变量 $C_x=Q_x-p\phi_y$、$C_y=Q_y+r\phi_x$ 及时间微分与空间梯度交换；
- 实际场空间、几乎处处意义和函数空间正则性；
- 从时间积分构造 $u,q$ 并连接原 PDE 解；
- 完整八变量与 primitive 系统的双向等价；
- Green/PEC、Poincaré、加权图范数、两层能量及完整 PML 耗散定理。

因此 [theorem_inventory 的 T02–T04](docs/theorem_inventory.md) 没有整体实现：T02 的积分提升未做，T03 仅得到三个固定点分量，T04 的 PDE 等价未做。一般非零初始不变量保持，不表示已经把合同的无源兼容初值范围扩展到任意初值。给定函数的条件性保持结论及一个显式实例，也不证明一般初值问题存在唯一性。

下一阶段 **v0.2.1 尚未开始**。按 [路线图](ROADMAP_lean_PML_revised.md)，入口是 `PML/Coefficients.lean`、`PML/Weights.lean`：形式化 $a=p+r,b=pr$ 的符号和小量条件，分别处理零吸收、单向吸收、双向吸收，定义 $w_i$ 与 $\theta_i$ 的退化分支，证明相应界限。特别是 $\theta_i$ 在 $a=0$ 取 $1/2$，不能与能量权重的零延拓混用；不得忽略零分母或加入吸收正下界。本轮未创建这两个模块。
