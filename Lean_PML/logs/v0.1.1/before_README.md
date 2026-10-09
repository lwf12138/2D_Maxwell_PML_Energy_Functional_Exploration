# LeanPML：最小可信构建与局部能量求导

用途：说明如何阅读、构建和审计这个 Lean 工程。当前阶段为 **v0.0.3**；具体命令结果、日志及验收状态见 [PROGRESS.md](PROGRESS.md)。已接受的 [模型合同](docs/model_contract.md) 和 [阶段范围](docs/scope.md) 保留原内容。

## 当前 Lean 证明了什么

唯一新定理是 `LeanPML.Tutorial.hasDerivAt_energy`。给定实际函数 $u:\mathbb R\to\mathbb R$、实数 $\sigma,t$，以及 $u$ 在 $t$ 可导且导数为 $-\sigma u(t)$ 的证据，定义

$$
\mathcal E(s)=\frac{u(s)^2}{2},
$$

证明 $\mathcal E$ 在 $t$ 可导，而且

$$
\mathcal E'(t)=-\sigma u(t)^2.
$$

实际 Lean 声明为：

```lean
theorem hasDerivAt_energy (u : ℝ → ℝ) (σ t : ℝ)
    (hu : HasDerivAt u (-σ * u t) t) :
    HasDerivAt (energy u) (-σ * (u t) ^ 2) t
```

`HasDerivAt f d t` 同时表达“函数 f 在 t 可导”和“导数值为 d”。输入只给 u 的导数；输出给能量函数的导数，没有把输出预设为假设。

证明中的 `(hu.pow 2).div_const 2` 使用真实的平方求导和除以常数规则；u 的微分方程已经代入 `hu` 的导数值。最后 `congr_deriv (by ring)` 用代数恒等式整理导数表达式。详细中文批注见源码。

这条求导恒等式对任意实数 $\sigma$ 成立，所以没有额外要求 $\sigma\ge0$。这不改变 PML 模型合同中吸收非负的条件。**本工程当前未证明导数非正、有限区间单调性、Debye 子系统或二维 PML 主定理。** 这些仍按路线图逐步推进。

## 推荐阅读顺序

1. 本 README：先了解命题范围与运行方式。
2. [LocalEnergy.lean](LeanPML/Tutorial/LocalEnergy.lean)：从 `energy` 定义读到唯一的 `HasDerivAt` 定理，逐行对照中文注释。
3. [LeanPML.lean](LeanPML.lean)：了解正式导入入口如何把模块接进库。
4. [Audit.lean](Audit.lean)：了解如何查看新定理的传递公理依赖。
5. [lakefile.toml](lakefile.toml)、[PROGRESS.md](PROGRESS.md)：了解默认构建目标、版本锁定和实际验证证据。

## 固定的环境

| 项目 | 固定或实际核验的值 |
|---|---|
| Lake 工程根目录 | 当前 `Lean_PML` 目录 |
| 包名／包版本 | `leanPML` / `0.0.3` |
| 正式 Lean 模块根 | `LeanPML` |
| Lean 工具链 | `leanprover/lean4:v4.31.0` |
| 实际 Lean | `4.31.0`，提交 `68218e876d2a38b1985b8590fff244a83c321783` |
| 实际 Lake | `5.0.0-src+68218e8`，随该 Lean 工具链使用 |
| mathlib 版本 | `v4.31.0` |
| mathlib 精确提交 | `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` |
| 直接及传递依赖锁定 | [lake-manifest.json](lake-manifest.json)，共 9 个包 |

[lean-toolchain](lean-toolchain) 只选择本工程的工具链，不修改 elan 全局默认值。[lakefile.toml](lakefile.toml) 直接将 mathlib 锁到上述提交；manifest 保存所有包解析后的提交。有些传递依赖的 `inputRev` 写 `main` 或 `master`，实际重现使用的是 manifest 中的固定 `rev`。

依赖由 Lake 获取到本项目的 `.lake/packages`，没有把其他项目作为路径依赖，也没有通过符号链接共享它们的工作目录。`.lake/` 是可重新生成的目录，已忽略；工具链、配置、锁文件、源码和验证日志需要保留。mathlib 的缓存命令可复用本机已经下载的压缩缓存，本次确实命中了已有缓存。

## 在你的终端重新运行

已有当前依赖时，复制下面几行即可：

```sh
cd '/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML'
lake env lean --version
lake env lake --version
lake build
lake env lean Audit.lean
```

默认构建目标是 `LeanPML` 和 `Audit` 两个库。导入关系为：

```text
LeanPML.lean → LeanPML/Tutorial/LocalEnergy.lean
Audit.lean   → LeanPML.lean
```

增量 `lake build` 可以复用已检查的构建产物；需要当前审计正文时，另外运行 `lake env lean Audit.lean`。

在另一台已有 elan、Git 的机器上，保留上述配置与 manifest 后，可先获取本阶段所需 mathlib 模块及其传递依赖的缓存，再执行构建与审计：

```sh
lake exe cache get Mathlib.Analysis.Calculus.Deriv.Pow Mathlib.Analysis.Calculus.Deriv.Mul Mathlib.Tactic.Ring
lake build
lake env lean Audit.lean
```

这会按工程配置使用指定工具链，并由 Lake 获取缺失依赖。常规重现保留锁文件，不必运行 `lake update`。本次首次生成锁文件时实际用了 `MATHLIB_NO_CACHE_ON_UPDATE=1 lake update`，只关闭当次 mathlib 更新钩子的全库缓存获取，随后按需获取缓存；没有改变数学证明或全局工具链。

若希望自己的执行也留下独立日志，可使用项目提供的 Python 3.9+ 标准库脚本：

```sh
python3 scripts/run_logged.py my_build lake build
python3 scripts/run_logged.py my_audit lake env lean Audit.lean
```

每次生成新时间戳文件，不覆盖旧记录。`logs/v0.0.3/*.log` 保留合并后的完整标准输出和错误输出；同名 `.json` 保存参数列表、可复制命令、工作目录、开始/结束时间、退出码和耗时。脚本以实际命令退出码结束，失败也会留档。核心 Lean 构建不依赖 Python。

## 怎样理解公理审计

本次构建及独立审计实际报告：

```text
'LeanPML.Tutorial.hasDerivAt_energy' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- `propext`：命题外延性，将逻辑等价的命题视为相等。
- `Classical.choice`：经典选择原则。
- `Quot.sound`：商类型中，被关系识别的代表元具有相同商值。

这些是本例使用的 Lean/mathlib 基础依赖，不能把它们误报为未完成证明。本次输出没有 `sorryAx`，也没有项目自定义的占位公理。源码没有使用 `sorry`、`admit` 或自定义 `axiom`。公理审计仍需配合阅读定理的输入和输出；它不会自动判断自然语言是否被准确表达。

## 新增正式 Lean 文件时如何接入

1. 把模块放在 `LeanPML/` 下，并在 `LeanPML.lean` 中增加对应的 `import LeanPML.子目录.模块名`，或保证它可沿正式入口的导入链到达。仅创建文件不会自动使其进入本配置的默认构建。
2. 给新增交付定理命名，并在 `Audit.lean` 增加对应的 `#print axioms 完整定理名`。
3. 运行并留档 `lake build`、`lake env lean Audit.lean`；核对模块覆盖、公理依赖和数学语义。
4. 更新 `PROGRESS.md` 的已实现条目及范围；必要时另行登记与已接受合同的差异，不能为通过构建默改假设。

下一阶段是 **v0.1.1**：在闭区间连续、内部可导等明确假设下，完成能量导数非正与 `AntitoneOn`，处理端点及 $T=0$，不预设整条实轴上的方程。本轮没有开始该阶段。
