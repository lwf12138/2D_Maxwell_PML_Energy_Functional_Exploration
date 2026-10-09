# LeanPML：标量平方能量与有限区间单调性

用途：帮助你逐行阅读 v0.1.1 的形式化证明，理解每个假设如何使用，并自行构建与审计。实际验收结果与完整日志见 [PROGRESS.md](PROGRESS.md)。已接受的 [模型合同](docs/model_contract.md) 和 [PML 阶段范围](docs/scope.md) 保持原内容。

## 从自然语言到主定理

给定实际函数 $u:\mathbb R\to\mathbb R$、常数 $\sigma\ge0$ 和终止时间 $T\ge0$。要求 $u$ 在 $[0,T]$ 上连续，且只在 $t\in(0,T)$ 要求

$$
u'(t)=-\sigma u(t).
$$

沿用 v0.0.3 的定义

$$
\mathcal E(t)=\operatorname{energy}(u,t)=\frac{u(t)^2}{2}.
$$

本阶段证明 $\mathcal E$ 在内部可导且 $\mathcal E'(t)=-\sigma u(t)^2\le0$，进而

$$
0\le s\le t\le T\quad\Longrightarrow\quad\mathcal E(t)\le\mathcal E(s),
\qquad
0\le\mathcal E(t)\le\mathcal E(0)\quad(t\in[0,T]).
$$

核心 Lean 声明是：

```lean
theorem antitoneOn_energy (u : ℝ → ℝ) (σ T : ℝ)
    (hσ : 0 ≤ σ) (hT : 0 ≤ T)
    (hcont : ContinuousOn u (Set.Icc 0 T))
    (hode : ∀ t ∈ Set.Ioo 0 T, HasDerivAt u (-σ * u t) t) :
    AntitoneOn (energy u) (Set.Icc 0 T)
```

冒号前列对象和输入假设，冒号后是待证结论。输入没有能量导数非正、单调性或初值界；这些都由证明得出。$u$ 的类型虽然定义在实轴上，主定理并未要求区间外满足方程。$\sigma$ 是固定实数，当前未研究时变耗散。

| Lean 写法 | 自然语言 | 在证明中的用途 |
|---|---|---|
| `Set.Icc 0 T` | 闭区间 $[0,T]$ | 最终比较范围，包含端点 |
| `Set.Ioo 0 T` | 开区间 $(0,T)$ | 唯一要求微分方程的时刻集合 |
| `ContinuousOn u (Set.Icc 0 T)` | $u$ 在闭区间内连续 | 传给平方能量，再用于中值定理的端点比较 |
| `HasDerivAt u d t` | $u$ 在 $t$ 可导，导数值为 $d$ | 把数值 $d$ 与真实导数联系起来 |
| `hσ : 0 ≤ σ` | 耗散参数非负 | 与平方非负一起证明导数非正 |
| `hT : 0 ≤ T` | 时间区间不反向 | 主证明区分零/正长度，并保证 $0\in[0,T]$ |
| `AntitoneOn (energy u) (Set.Icc 0 T)` | 较晚时刻能量不大于较早时刻 | 不等号允许相等，不是严格递减 |
| `A ∧ B` | 两个结论同时成立 | 初值界给出非负与上界两部分 |

## 建议阅读顺序与证明链

1. [LocalEnergy.lean](LeanPML/Tutorial/LocalEnergy.lean)：复习已有 `energy` 定义和 `hasDerivAt_energy`，本轮没有改动这个文件。
2. [Monotonicity.lean](LeanPML/Time/Monotonicity.lean)：阅读通用时间引理和单点区间引理；这里暂时不涉及具体能量。
3. [ScalarEnergy.lean](LeanPML/Tutorial/ScalarEnergy.lean)：按源码顺序阅读，从非负和连续性，一直读到主定理、初值界和负耗散对照例。
4. [LeanPML.lean](LeanPML.lean) 与 [Audit.lean](Audit.lean)：查看正式导入链和逐项公理审计。
5. [PROGRESS.md](PROGRESS.md)：核对真实命令、成功及失败日志、当前范围与历史记录。

主要声明的命名空间是 `LeanPML.Tutorial`；一般时间引理位于 `LeanPML.Time`。

| 声明 | 输入与结论 |
|---|---|
| `energy_nonneg` | 任意 $u,t$，得到 $0\le\mathcal E(t)$；不需要 ODE |
| `continuousOn_energy` | 任意集合上的 $u$ 连续，推出能量在同集合连续 |
| `hasDerivAt_energy_on_Ioo` | 内部 ODE，得到内部能量可导及公式；不要求 $\sigma\ge0$ |
| `energy_deriv_nonpos` | 某时刻的真实 ODE 与 $\sigma\ge0$，推出该时刻实际能量导数非正 |
| `antitoneOn_Icc_of_hasDerivAt_nonpos` | 一般函数闭区间连续、内部真实导数及符号，推出整个闭区间单调不增 |
| `antitoneOn_Icc_self` | 任意函数在 $[a,a]$ 上单调不增，无连续/导数假设 |
| `antitoneOn_energy_zero` | 任意 $u$ 的能量在 $[0,0]$ 上单调不增，无参数、连续/导数假设 |
| `antitoneOn_energy` | 参数条件、原函数连续性、内部 ODE，推出 $[0,T]$ 上单调不增 |
| `energy_bounds` | 与主定理相同的输入，再给 $t\in[0,T]$，得到 $0\le\mathcal E(t)\le\mathcal E(0)$ |
| `exp_solves_negative_damping` | 证明 $e^t$ 满足 $\sigma=-1$ 时的真实 ODE |
| `negative_damping_counterexample` | 证明 exp 连续、上述 ODE 成立、能量在 $0$ 可导且导数为 $1>0$ |

纸面证明中的四步在代码中各有对应：

- **导数存在与公式**：`hasDerivAt_energy` 使用平方和除常数的求导规则，输出仍是 `HasDerivAt`。
- **导数符号**：`energy_deriv_nonpos` 用 `.deriv` 取得等式，再用 $-\sigma\le0$、$u(t)^2\ge0$ 判断乘积符号。mathlib 的 `deriv` 是总定义，单独写它不能替代导数存在证据；这里始终先有 `HasDerivAt`。
- **时间单调性**：调用 [mathlib 的中值定理推论](.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/MeanValue.lean)，精确名称为 `antitoneOn_of_hasDerivWithinAt_nonpos`。`interior_Icc` 将闭区间的内部转换成开区间，`.hasDerivWithinAt` 将普通导数证据限制到内部集合。
- **初值界**：从 `AntitoneOn` 取早时刻 $0$、晚时刻 $t$，再与能量非负合并。

`intro` 引入任意对象和假设；`have` 命名中间事实；`rw` 用等式改写；`apply` 用已有定理把大目标化成其输入条件；`exact` 交付与当前目标匹配的证据；`constructor` 拆分“且”的两项；`change` 换成定义上相同、写法更明确的目标。源码在使用处均有中文说明。

## 为什么不用端点双侧导数

比较 $s<t$ 时，中值定理需要能量在 $[s,t]$ 连续，在 $(s,t)$ 内可导。由于 $[s,t]\subseteq[0,T]$ 且 $(s,t)\subseteq(0,T)$，已有假设就够了。即使 $s=0$ 或 $t=T$，也不必添加这两个端点的普通双侧导数。这里的 `ContinuousOn` 在端点只要求相对于区间的连续性。

$T=0$ 时，两时刻都只能等于 $0$，比较退化为 $\mathcal E(0)\le\mathcal E(0)$。源码单独证明了不带连续性和导数假设的结论；主定理的零分支直接调用它。$(0,0)$ 为空，内部方程也无须提供任何时刻的导数证据。

## 修改耗散参数的练习

求导公式不需要 $\sigma\ge0$。取 $\sigma=-1$ 和 $u(t)=e^t$，仍然有

$$
u'(t)=e^t=-\sigma u(t),
\qquad
\mathcal E'(0)=-(-1)e^{2\cdot0}=1>0.
$$

`negative_damping_counterexample` 正式证明了连续性、真实 ODE、`HasDerivAt (energy Real.exp) 1 0` 以及实际导数严格为正。去掉耗散符号条件后，求导步骤仍合法；失败的是由 $\sigma\ge0$ 推出 $-\sigma\le0$ 的符号步骤，不能再交付给一般单调性引理所需的非正条件。

这个声明精确展示 $t=0$ 的导数符号变化，没有另外形式化某个闭区间上 `AntitoneOn` 的否定。只有这个显式例子的方程被证明对所有实数成立；主定理仍只假设 $(0,T)$ 内的方程。正式文件没有故意留错的练习分支。

## 在 VS Code 查看每步目标

本机已安装 Lean 4 扩展。用“打开文件夹”打开本工程根目录 `Lean_PML`，再打开 `ScalarEnergy.lean`，等待 Lean 处理结束。不要只打开脱离工程的单个文件。

1. 按 `Cmd+Shift+P`，运行 `Lean 4: InfoView: Display Goal`。也可运行 `Lean 4: InfoView: Toggle InfoView`；本机 Mac 默认快捷键为 `Cmd+Shift+Enter`。
2. 从 `energy_deriv_nonpos` 开始，把光标依次放到 `by`、`rw`、`exact` 所在步骤附近，观察 InfoView 的变化。移动到步骤前后，可以比较改写前后的状态。
3. InfoView 中 `u : ℝ → ℝ`、`hσ : 0 ≤ σ` 等是已知对象和证据；`⊢` 后是仍需证明的目标。`rw` 后应看到导数目标变成乘积非正。
4. 阅读主定理时，比较两个 `·` 分支；在 `apply` 后观察剩余的导数符号目标。在 `energy_bounds` 的 `constructor` 后观察两个目标。
5. 悬停声明名称查看类型；右键选择 “Go to Definition”，或用 F12（部分 Mac 键盘需 Fn+F12），跳到已有定理。对比本地 mathlib 的实际输入条件，不能只根据定理名称猜含义。可用 `Lean 4: InfoView: Toggle Pin` 固定一个位置的目标。

这些操作不需要删去已完成代码或插入占位证明。InfoView 显示的是光标对应位置的状态；文件末尾没有待证目标是正常的。若命令行构建已通过而编辑器状态未刷新，可运行 `Lean 4: Server: Restart File`。

说明依据本机已安装的 [Lean 4 扩展官方手册](</Users/wcli/.vscode/extensions/leanprover.lean4-0.0.237/manual/manual.md:259>) 与其命令配置；本轮没有安装或修改编辑器扩展。

## 固定环境与终端复现

| 项目 | 固定值 |
|---|---|
| 正式模块根 | `LeanPML` |
| Lean 工具链 | `leanprover/lean4:v4.31.0` |
| Lean 提交 | `68218e876d2a38b1985b8590fff244a83c321783` |
| Lake | `5.0.0-src+68218e8` |
| mathlib | `v4.31.0`，提交 `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` |
| 锁定配置 | [lean-toolchain](lean-toolchain)、[lakefile.toml](lakefile.toml)、[lake-manifest.json](lake-manifest.json) |

三个配置文件本轮保持不变；Lake 包元数据仍为 `leanPML / 0.0.3`，与当前研究阶段 v0.1.1 分开记录。依赖由 Lake 管理，传递依赖按 manifest 的 `rev` 重现，不需要运行 `lake update`，也没有修改全局默认工具链。

复制以下命令：

```sh
cd '/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML'
lake env lean --version
lake env lake --version
lake build
lake env lean Audit.lean
```

若换机器且已安装 elan、Git，保留锁文件并先获取所需缓存：

```sh
lake exe cache get Mathlib.Analysis.Calculus.Deriv.Pow Mathlib.Analysis.Calculus.Deriv.Mul Mathlib.Tactic.Ring Mathlib.Analysis.Calculus.Deriv.MeanValue Mathlib.Analysis.SpecialFunctions.ExpDeriv Mathlib.Tactic.NormNum
lake build
lake env lean Audit.lean
```

保存自己运行的完整日志（需要 Python 3.9+）：

```sh
python3 scripts/run_logged.py --stage v0.1.1 my_build lake build
python3 scripts/run_logged.py --stage v0.1.1 my_audit lake env lean Audit.lean
```

日志写入 `logs/v0.1.1/`：`.log` 保留完整合并输出，`.json` 保存完整参数、工作目录、开始/结束时间及真实退出码。每次生成新文件，失败也保留；旧版不带 `--stage` 的命令仍写入 `logs/v0.0.3/`。

## 构建、审计与范围

默认目标仍是 `LeanPML`、`Audit`。导入链包含：

```text
LeanPML.lean
  ├─ Tutorial/LocalEnergy.lean
  ├─ Time/Monotonicity.lean
  └─ Tutorial/ScalarEnergy.lean（复用上述两模块）
Audit.lean → LeanPML.lean
```

每条项目定理均在 `Audit.lean` 用 `#print axioms` 审计。常见标准依赖是 `propext`（命题外延性）、`Classical.choice`（经典选择）、`Quot.sound`（商类型的基础原则）。验收要求没有 `sorryAx` 或自定义占位公理，而非要求依赖列表为空。必须同时阅读声明，核对自然语言确实被正确翻译。

新增正式模块需接入 `LeanPML.lean` 的导入链，新增定理需接入 `Audit.lean`，再构建、审计并留档。仅创建文件不会自动保证本配置检查了它。

本阶段是对给定函数的先验能量结论，未证明解的存在、唯一性、严格递减或二维 PML 主定理。下一阶段 **v0.1.2 尚未开始**：以实际 $E(t),P(t)$ 和 Debye 子系统两条导数方程为输入，定义 $\frac12(\epsilon E^2+P^2/\kappa)$ 并推导耗散；入口文件计划为 `LeanPML/Debye/ScalarEnergy.lean`，可复用本阶段的一般时间引理。该文件本轮未创建。
