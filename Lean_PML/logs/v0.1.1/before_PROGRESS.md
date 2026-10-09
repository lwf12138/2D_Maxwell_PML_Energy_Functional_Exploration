# LeanPML 阶段进度与实际验证记录

用途：记录本工程当前真正实现并运行通过的内容，以及尚未完成的范围。更新日期：2026-10-06（Asia/Shanghai）。历史材料中的“本轮”仍指它们各自的记录日期；当前工程状态以本文件为准。

**v0.0.3：已完成。** 实际默认构建和独立公理审计均退出 0；本阶段仅实现最小局部求导定理，没有推进 v0.1.1 或 PML 主定理。用户已接受的 v0.0.2 数学合同保持原内容。

## 1. 本阶段交付

| 文件 | 实际作用 |
|---|---|
| [lean-toolchain](lean-toolchain) | 为本工程固定 Lean v4.31.0 |
| [lakefile.toml](lakefile.toml) | 固定 mathlib 提交，设置 `LeanPML`、`Audit` 两个默认库目标 |
| [lake-manifest.json](lake-manifest.json) | Lake 实际解析生成的 9 个依赖包的提交锁定清单 |
| [LeanPML/Tutorial/LocalEnergy.lean](LeanPML/Tutorial/LocalEnergy.lean) | 中文批注的 `energy` 定义及唯一新定理 |
| [LeanPML.lean](LeanPML.lean) | 正式模块导入入口，导入 LocalEnergy |
| [Audit.lean](Audit.lean) | 导入正式入口，对新定理执行 `#print axioms`；自身也进入默认构建 |
| [.gitignore](.gitignore) | 忽略可重建的 `.lake/` 等，不忽略源码、锁文件与日志 |
| [scripts/run_logged.py](scripts/run_logged.py) | 标准库命令记录器；保存完整输出、命令、目录、时间和退出码 |
| [README.md](README.md) | 阅读顺序、数学含义、复现命令、公理解释及新增模块接入方式 |
| [logs/v0.0.3](logs/v0.0.3) | 本阶段真实执行日志、元数据及输入文件哈希 |

已实现定理为 `LeanPML.Tutorial.hasDerivAt_energy`：

$$
\operatorname{HasDerivAt}(u,-\sigma u(t),t)
\Longrightarrow
\operatorname{HasDerivAt}\left(s\mapsto\frac{u(s)^2}{2},-\sigma u(t)^2,t\right).
$$

输入只涉及 u 在 t 的真实导数。平方求导、除以常数与导数值代数整理都已进入证明；没有求显式解，没有假设能量导数公式。该局部恒等式不使用 $\sigma\ge0$，与以后证明导数非正所需条件分开。

## 2. 工具链、依赖与隔离范围

- 实际 Lean：`4.31.0`，`arm64-apple-darwin24.6.0`，提交 `68218e876d2a38b1985b8590fff244a83c321783`。
- 实际 Lake：`5.0.0-src+68218e8`，随 Lean v4.31.0 使用。
- 实际 elan：`4.2.3 (b6cec7e10 2026-06-08)`；未修改全局默认 `stable`。
- mathlib：`v4.31.0`，提交 `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`。已在新工程核对标签解析、实际 Git HEAD、manifest 和 mathlib 自带 `lean-toolchain` 一致。
- manifest 中 9 个依赖的实际 Git HEAD 均与各自固定 `rev` 一致。`inputRev` 中的分支名仅保留来源信息，当前复现依据 `rev`。
- 初次依赖解析由本工程中的 Lake 完成。其他项目仅用于只读核对已有版本，没有使用它们的目录作为路径依赖，也没有改变其配置。
- mathlib 缓存工具为所需三个导入及其传递依赖解压了 1946 个已缓存文件；本次无需新下载缓存。项目自己的三个 Lean 模块随后实际编译。

记录覆盖工程祖先路径，未发现适用的 `AGENTS.md`。初始读取材料与其他项目配置、elan 设置的字节快照见 [input_hashes.json](logs/v0.0.3/input_hashes.json)；[末次检查](logs/v0.0.3/20261006T151005_361176_final_checks.log) 确认其中 14 个文件的字节均未改变。

## 3. 实际命令及完整日志

以下各条命令的工作目录均为：

```text
/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML
```

每条操作由 `python3 scripts/run_logged.py 标签 命令...` 执行。`.log` 是未经删节的合并输出，`.json` 保存完整参数列表、工作目录、开始和结束时间、退出码及耗时。表中的 Python 检查命令为简述，其完整 `-c` 参数保存在 JSON 中。

| 实际操作／命令 | 退出码 | 输出／元数据 |
|---|---|---|
| `command -v`、`elan --version`、工具链列表及显式 v4.31.0 候选版本探测 | 0 | [输出](logs/v0.0.3/20261006T150010_961344_candidate_environment.log) · [完整命令](logs/v0.0.3/20261006T150010_961344_candidate_environment.json) |
| `MATHLIB_NO_CACHE_ON_UPDATE=1 lake update` | 0 | [输出](logs/v0.0.3/20261006T150044_383600_lake_update.log) · [元数据](logs/v0.0.3/20261006T150044_383600_lake_update.json) |
| Python：输入文档、其他项目配置和 elan 设置哈希；AGENTS 定位 | 0 | [输出](logs/v0.0.3/20261006T150130_026848_input_snapshot.log) · [完整命令](logs/v0.0.3/20261006T150130_026848_input_snapshot.json) |
| Python/Git：只读核对已有相关工程的配置及 mathlib 标签 | 0 | [输出](logs/v0.0.3/20261006T150310_215210_reference_versions.log) · [完整命令](logs/v0.0.3/20261006T150310_215210_reference_versions.json) |
| `lake exe cache get Mathlib.Analysis.Calculus.Deriv.Pow Mathlib.Analysis.Calculus.Deriv.Mul Mathlib.Tactic.Ring` | 0 | [输出](logs/v0.0.3/20261006T150314_508502_mathlib_cache.log) · [元数据](logs/v0.0.3/20261006T150314_508502_mathlib_cache.json) |
| `lake env lake --version` | 0 | [输出](logs/v0.0.3/20261006T150328_832226_project_lake_version.log) · [元数据](logs/v0.0.3/20261006T150328_832226_project_lake_version.json) |
| Python/Git：逐包核对 manifest 与实际提交、mathlib 标签和工具链 | 0 | [输出](logs/v0.0.3/20261006T150328_832509_dependency_lock.log) · [完整命令](logs/v0.0.3/20261006T150328_832509_dependency_lock.json) |
| `lake env lean --version` | 0 | [输出](logs/v0.0.3/20261006T150328_832608_project_lean_version.log) · [元数据](logs/v0.0.3/20261006T150328_832608_project_lean_version.json) |
| **`lake build`** | **0** | [构建输出](logs/v0.0.3/20261006T150357_739595_lake_build.log) · [元数据](logs/v0.0.3/20261006T150357_739595_lake_build.json) |
| **`lake env lean Audit.lean`** | **0** | [独立审计输出](logs/v0.0.3/20261006T150431_846159_axioms_audit.log) · [元数据](logs/v0.0.3/20261006T150431_846159_axioms_audit.json) |
| Python：既有文件保护、源码占位检查、构建覆盖、审计记录及文档链接核对 | 0 | [末次检查输出](logs/v0.0.3/20261006T151005_361176_final_checks.log) · [完整命令](logs/v0.0.3/20261006T151005_361176_final_checks.json) |

构建日志明确含 `Built LeanPML.Tutorial.LocalEnergy`、`Built LeanPML` 和 `Built Audit`。结尾的 `1967 jobs` 包含依赖任务，不是本项目新定理数量；本项目只新增一条定理。

上述依赖、构建和审计执行均成功，没有被删去的失败重试。缓存工具的可执行文件链接曾输出警告 `ld64.lld: warning: directory not found for option -L/usr/local/lib`；该条日志完整保留，命令随后退出 0，正式证明构建及审计也成功。没有为消除此警告修改全局目录或工具链。

## 4. 公理审计与验收

独立审计实际输出为：

```text
'LeanPML.Tutorial.hasDerivAt_energy' depends on axioms: [propext, Classical.choice, Quot.sound]
```

依赖为命题外延性、经典选择和商类型的标准基础原则；没有 `sorryAx` 或项目自定义占位公理。源码未使用 `sorry`、`admit` 或自定义 `axiom`。因此验收不是“公理列表为空”，而是确认无未证明占位，并检查实际命题仍对应用户要求。

| v0.0.3 验收项 | 实际结论 |
|---|---|
| 选定并固定实际可用环境 | v4.31.0 候选通过，无需更换版本 |
| 保存工具链、Lake 配置和依赖锁定清单 | 三项配置已保存，mathlib 直接锁定提交，传递提交已逐包核对 |
| 正式模块和审计均参与默认构建 | 两默认目标及显式导入链；构建日志逐项可见 |
| 最小真实函数求导证明 | 新定理直接使用 `HasDerivAt`，带中文批注，实际编译通过 |
| 构建与独立公理审计 | 两命令均退出 0，完整输出和元数据已保存 |
| 可复现及新增文件接入说明 | README 已给终端命令、阅读顺序、导入与审计步骤 |
| 数学范围 | 保留已接受的 v0.0.2 合同，本轮只完成局部标量求导 |

## 5. 本轮发现的记录差异与影响

1. `ROADMAP_lean_PML_revised.md` 的 v0.0.2 部分（约第 427 行）仍写“待在项目中实现”，但随后任务已经勾选完成；`docs/scope.md` 第 126 行的“v0.0.3 本轮未开始”属于 v0.0.2 的历史交接。本轮按用户已接受的范围推进，以本进度记录登记新状态，不回写旧文档，也不改变数学假设。
2. 当前路线图 SHA-256 为 `0a9d82f53c655dbae0eb3166f2176a10c681e0357f68ba64f023c29e794d43d0`，与旧 scope 中记录的 `16c14617…` 已不同。本轮重新读取当前阶段及相邻阶段，并保存当前输入哈希；不凭旧哈希推断具体改动原因。
3. `docs/source_inventory.md` 第 3 行链接到 `math_preview.html`，本轮工作目录中未找到该目标。这影响旧文档的快捷预览，不影响模型合同、Lean 构建或本 README 的 Markdown 数学公式；本轮保留旧文件。
4. `docs/scope.md` 的 Q01–Q13 数学/API 待核验项继续保留。它们属于后续 PDE 形式化任务，本轮没有据此改动模型条件，也没有宣称已解决。

## 6. 下一步与交接

**下一阶段：v0.1.1，尚未开始。** 在当前真实导数引理基础上，加入非负耗散条件、闭区间连续和内部导数假设，完成 $[0,T]$ 上的能量单调不增，处理端点与 $T=0$；不得为省事假设整个实轴上都有方程。

进一步的 Debye 子系统、时间不变量、二维 PML、Green/Poincaré、图范数控制和耗散闭合仍未实现。既有 theorem_inventory 中的 T01–T37 仍是计划；本轮的教学求导例子不使任何 PML 主结论自动完成。

新增正式文件时，按 README 将它接入 `LeanPML.lean` 的导入链，把新定理加入 `Audit.lean`，再执行并记录默认构建和独立审计。本阶段没有创建提交、发布或改动其他项目。
