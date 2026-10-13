# 定位 Lean PML 材料来源清单

> 阅读提示：请使用支持 LaTeX 数学公式的 Markdown 预览。行内公式使用 `$...$`，独立公式使用 `$$...$$`；源码视图会显示这些标记。代码名称、路径和哈希保留等宽字体。也可直接[打开公式阅读版](math_preview.html)。

核查日期：2026-10-06（Asia/Shanghai）。阶段：v0.0.1。

本轮已定位并读取路线图要求的 S1–S7 材料，登记 28 份关键文件的实际路径、用途和 SHA-256，确认外部标量工程存在。完成的是材料与历史状态清点；本轮没有运行 Lean、Lake、SymPy 或 LaTeX，没有重新审定完整 PDE 证明。每项数学结论的状态见 [结论状态表](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML/docs/claim_ledger.md)。

## 路径与阅读方式

- 研究根目录：`/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration`。
- 本阶段工作目录：`/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML`。
- 外部标量工程：`/Users/wcli/Desktop/资料/graduate_student/博/Lean_study/ScalarDissipation`。
- 下表中的研究文件名相对于研究根目录，标量文件名相对于外部标量工程；所有链接指向本机实际绝对路径。
- 这里的“只读来源”指本轮只读取、登记原文件，没有改动其内容或文件权限。哈希用于识别文件版本，不证明文件中的数学结论正确。
- 路线图中的 S3、S6 各包含两份文件，因此分别标成 a、b。清单覆盖本阶段所需证据，不宣称逐一审计全部历史文件、PDF 或第三方论文。

推荐先读 S1 的原模型与目标，再读 S2 的定理 6.1 和 §13，随后用 S5 了解旧 Lean 的实际覆盖。S3a 可帮助定位每条假设的用途。

## 路线图与必要来源

| 编号 | 类别 | 文件 | 本轮用途 |
|---|---|---|---|
| R | 工作流审查 | [Lean_PML/ROADMAP_lean_PML_revised.md](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML/ROADMAP_lean_PML_revised.md) | 本次 v0.0.1 的任务边界 |
| S1 | 纸面证明／原问题 | [sources/energy_functional_problem.tex](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/sources/energy_functional_problem.tex) | 原八变量、极化、边界及能量目标 |
| S2 | 纸面证明 | [results/V7_Maxwell_Debye_PML/V7_global_energy.md](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/results/V7_Maxwell_Debye_PML/V7_global_energy.md) | V7 定理 6.1 及 §§2、5–11；待形式化底稿 |
| S3a | 工作流审查 | [results/V7_Maxwell_Debye_PML/proof_audit.md](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/results/V7_Maxwell_Debye_PML/proof_audit.md) | V7 自审：假设用途与结论边界 |
| S3b | 工作流审查 | [results/V7_Maxwell_Debye_PML/README.md](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/results/V7_Maxwell_Debye_PML/README.md) | V7 交付范围与历史验证自述 |
| S4 | 工作流审查 | [results/v6_mathematical_completeness_review_20260924.md](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/results/v6_mathematical_completeness_review_20260924.md) | V6 数学完整性与全域估计缺口 |
| S5 | 工作流审查 | [results/lean_core_theorem_coverage_review_20260924.md](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/results/lean_core_theorem_coverage_review_20260924.md) | 旧 Lean 命题范围及历史构建成败 |
| S6a | Lean 源码 | [results/v6_tex/NonlocalMemoryStrictPML.lean](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/results/v6_tex/NonlocalMemoryStrictPML.lean) | V6 十条辅助代数／标量代理定理 |
| S6b | Lean 源码 | [verification/algebra/VariableCoefficientBaffet.lean](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/verification/algebra/VariableCoefficientBaffet.lean) | V5 六条多项式／标量吸收定理 |
| S7 | 符号脚本 | [results/V7_Maxwell_Debye_PML/verify_v7.py](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/results/V7_Maxwell_Debye_PML/verify_v7.py) | SymPy 代数及含浮点比较的参数核验 |

**S0 的可访问性：** 本轮在研究工程、其父目录 `further_PML` 的可见文件列表及 `Lean_study` 中未定位到名为 `ROADMAP_lean.md` 的原路线图；未搜索全盘或压缩包内部。现有同名片段、别名或 `ROADMAP.md` 不自动视为 S0。本阶段所需 S1–S7 均可读取，S0 缺失不阻止本阶段完成；关于原路线图的比较只按 R 的历史叙述记录，不声称重新完成 S0 对照。

## 旧代码、运行记录和配置

| 编号 | 类别 | 文件 | 本轮用途 |
|---|---|---|---|
| H1 | 构建日志／脚本运行记录 | [results/V7_Maxwell_Debye_PML/verification_output.txt](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/results/V7_Maxwell_Debye_PML/verification_output.txt) | V7 脚本历史输出；本次未复跑 |
| H2 | 构建日志／运行记录 | [results/v6_tex/verification_outputs.md](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/results/v6_tex/verification_outputs.md) | V6 历史 Lean/SymPy 命令和退出码 |
| H3 | 构建日志／运行记录 | [results/v5_variable_coefficient_baffet/verification_outputs.md](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/results/v5_variable_coefficient_baffet/verification_outputs.md) | V5 早期环境失败及符号／工作流记录 |
| H4 | 工作流审查 | [results/v6_tex/VERIFICATION_STATUS.json](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/results/v6_tex/VERIFICATION_STATUS.json) | 历史状态摘要；不等于完整 PDE 形式化 |
| H5 | 工作流审查 | [lean_verification/README.md](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/lean_verification/README.md) | 旧 Lake 工程模板说明；不提供构建通过证据 |
| L1 | Lean 源码 | [lean_verification/PMLVerification/VariableCoefficientBaffet.lean](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/lean_verification/PMLVerification/VariableCoefficientBaffet.lean) | S6b 的旧 Lake 工程副本 |
| L2 | Lean 源码 | [verification/algebra/NewEnergyFunctional.lean](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/verification/algebra/NewEnergyFunctional.lean) | S5 曾记录构建失败的文件 |
| C1 | Lean 源码／工程配置 | [lean_verification/lean-toolchain](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/lean_verification/lean-toolchain) | 旧工程声明的编译器版本 |
| C2 | Lean 源码／工程配置 | [lean_verification/lakefile.toml](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/lean_verification/lakefile.toml) | 旧工程依赖及默认构建目标 |
| C3 | Lean 源码／工程配置 | [lean_verification/lake-manifest.json](/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/lean_verification/lake-manifest.json) | 旧工程依赖提交 |

旧材料的分类原则：

- **纸面证明：** 模型、定理和数学推导，例如 S1、S2；不因为存在 PDF 就视为 Lean 证明。
- **Lean 源码：** 实际定义和定理，例如 S6a、S6b、L1、L2；必须结合命题范围及新的编译结果使用。
- **符号脚本：** 例如 S7；它计算或化简给定表达式，没有自动核验实际 PDE 的全部分析步骤。
- **构建日志：** 例如 H1–H3 中记录的命令和输出；只说明所记录时间、环境和文件的运行情况。LaTeX 日志只反映文稿编译。
- **工作流审查：** 例如 S3–S5、H4；`verified`、`ok: true`、`goal_success` 是相应工作流的判断，不是完整 PDE 的 Lean 证明项。
- 工具链和依赖文件作为 Lean 工程配置单独注明；H5 当前只是 GitHub 配置模板，不能当作构建成功记录。

## 外部标量工程

| 编号 | 类别 | 文件 | 本轮用途 |
|---|---|---|---|
| T0 | Lean 源码 | [ScalarDissipation.lean](/Users/wcli/Desktop/资料/graduate_student/博/Lean_study/ScalarDissipation/ScalarDissipation.lean) | 标量工程正式导入入口 |
| T1 | Lean 源码 | [ScalarDissipation/Energy.lean](/Users/wcli/Desktop/资料/graduate_student/博/Lean_study/ScalarDissipation/ScalarDissipation/Energy.lean) | 真实求导到全实轴单调性及初值界 |
| T2 | Lean 源码 | [ScalarDissipation/Examples.lean](/Users/wcli/Desktop/资料/graduate_student/博/Lean_study/ScalarDissipation/ScalarDissipation/Examples.lean) | 指数解与能量定理调用实例 |
| T3 | Lean 源码 | [Audit.lean](/Users/wcli/Desktop/资料/graduate_student/博/Lean_study/ScalarDissipation/Audit.lean) | 标量定理公理依赖审计命令 |
| T4 | Lean 源码／工程配置 | [lean-toolchain](/Users/wcli/Desktop/资料/graduate_student/博/Lean_study/ScalarDissipation/lean-toolchain) | 标量工程声明的编译器版本 |
| T5 | Lean 源码／工程配置 | [lakefile.toml](/Users/wcli/Desktop/资料/graduate_student/博/Lean_study/ScalarDissipation/lakefile.toml) | 标量工程依赖与默认构建目标 |
| T6 | Lean 源码／工程配置 | [lake-manifest.json](/Users/wcli/Desktop/资料/graduate_student/博/Lean_study/ScalarDissipation/lake-manifest.json) | 标量工程依赖提交 |
| T7 | 构建日志／运行记录 | [README.md](/Users/wcli/Desktop/资料/graduate_student/博/Lean_study/ScalarDissipation/README.md) | 标量说明与 2026-09-23 验证自述 |

本轮从配置文件读到：

- 标量工程和旧 PML 工程均声明 `leanprover/lean4:v4.31.0`。
- 两者均声明 mathlib `v4.31.0`，依赖清单记录提交 `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`。
- 这些是**配置证据**，没有据此断言当前环境已成功构建。新 `LeanPML` 工具链的实际验证属于 v0.0.3。
- T0 导入 `ScalarDissipation.Energy` 和 `ScalarDissipation.Examples`；T3 是单独运行的公理审计文件。
- T1 使用真实 `HasDerivAt` 假设。其 `energy_antitone` 假设方程在整个实数轴上成立，T1 的初值界也保留该假设；这不能直接算作路线图要求的、仅在有限区间给定方程的版本。
- T7 记载 2026-09-23 的构建与公理审计通过。本轮确认该记录存在，未重新执行对应命令。

路线图关于“标量工程没有随上传材料提供”“当时没有可调用 Lean/Lake”的句子描述的是此前核查环境。本轮已确认本机标量工程可读；Lean/Lake 当前可运行性留待 v0.0.3 实测。

## 版本比对与历史状态

| 检查 | 本轮结果 | 解释 |
|---|---|---|
| S1 的 SHA-256 对照 R | 一致 | 原问题文件与路线图登记版本一致 |
| S2 的 SHA-256 对照 R | 一致 | V7 正文与路线图登记版本一致 |
| S5 的 SHA-256 对照 R | 一致 | Lean 覆盖审查与路线图登记版本一致 |
| S6b 与 L1 字节内容比对 | 一致 | 两个路径是同一份 V5 代码，不计为两项独立证明 |
| S1–S7 及支持文件可读性 | 下列 28 份文件均可读 | 未复制原始文件或依赖缓存 |

历史记录需保留其先后关系：

1. H3 记录 V5 早期 `lean` 不在 PATH，以及脱离 Lake 环境找不到 Mathlib 的失败。
2. S5 在 2026-09-24 的审查中记录，V5 与 V6 的相应文件曾在 Lake/mathlib 环境返回退出码 0。
3. H2 单独记录 V6 在 2026-07-14 的退出码 0 和修复经过。
4. S5 还记录 L2 曾返回退出码 1，出现类型类／实例及未关闭目标问题。本轮没有修复或重新编译它。
5. H1 保留 V7 脚本的历史成功输出。S7 源码包含精确代数化简，也包含 `float` 参数比较；输出中的 “ALL EXACT ALGEBRA CHECKS PASSED” 不能使浮点部分成为 Lean 精确证书。

## SHA-256 快照

本轮使用 Python 标准库按文件字节计算下列 SHA-256。编号对应上表；完整长度用于后续检测来源是否变更。

```text
R    a11280c6bbce2e374a552bda42cca67718971f1d35ff5b7eb26cecbcb14afeba
S1   1e09c1b702ced748ff0c4598ce2f578a8d55dd2f8b31599c7584b7d28bcf0e72
S2   0a7f73a25cb119eeb75b3e7b3c3f2fbb3b319250f3354ed4dcad0ecff8eff4fb
S3a  a2b2ac0a54c5dd8e0fa43c45d4a21185b5d433d5a94c4fb0680f41baec7ffa9a
S3b  d3ae475405dc37223fb26cea02a8d75428b5418938e96fcd4c604f1bdacb5996
S4   70174234f025aa23760cc18f0b429444116fbcdc3c42130bdcaff5f451531648
S5   6e23d28c0af71285258e1f9a183df127bbdc528a716199fe9cf1dc066e39024e
S6a  6b4870ee64127c392e0d6f2683bb59487694d8133b8529e0b050a9c5ad3fe831
S6b  446183da48cc6c63ad586e8b6fb8d23d61ed8110c9f5d2154bb4c75e436ee33a
S7   b75741634d92b9c241133e04f3b80b040cdcea203db26359704704b4e5f91799
H1   f02c957814a3008638296ebebd99475e317c246abd921a2a64d3039dfdbcbd31
H2   6953fcccc71e7eaa26e1e0fbed8ecb7bffa6c93ede61e7010d08b06c092981eb
H3   6451be490de8137c90f3b735683680e66026960e8c4f579c3c310774ce4c0080
H4   6cac6d29e1ba5bfbc6c2ff24576362855503d632253ee6a044655ebde98572a9
H5   fe92d8fd0afe0f796556fd7cfb590aa6e2badb97ff48f7804e0022e117736080
L1   446183da48cc6c63ad586e8b6fb8d23d61ed8110c9f5d2154bb4c75e436ee33a
L2   0894a564d03ab7a84982a99f8d729a21889a6e6d5f9eb6837c50901e97182287
C1   efac0b94923b2d8b6840cd35be9177ad0fc5ab2332f4f4311c98712cee92fdee
C2   b6cb80208007d20bdedd912d6b938250c9ac41d8107aeff31e9e95956b0420d0
C3   a15c26a2c3da8a43baab0a9683b9dbcd6e9d48c1c9413aaa2f4dab1c0708aae3
T0   15686defd9f41edffa87e96defae676b8c08c81faf154edb15331744aac33f14
T1   8462f20f55213002b5cbc120f68987751d7267876c3a822a863ba8085ed663c9
T2   fc7b631d2277a885bbba6508916d2b69d32251a752476e3e62d0d2b48bbc4769
T3   1a96646cfa6251eef8ab8d6ce4edba9f703c861f20267dde1c840fd4842ff6a3
T4   efac0b94923b2d8b6840cd35be9177ad0fc5ab2332f4f4311c98712cee92fdee
T5   6c45f06d0575e5a0192b5d75cd08abc9b8fe15c7af7d7054deaccf4a0a89a6af
T6   a19050fed07fc09d48d3955c33404614246881d7a5bd01da5f84ca9fa1efd1f9
T7   0e1490ca549cbbbf0981dc91399bb30a7c15273d13a9213dd9f12168a243e86e
```

以后可在本机终端对单个文件复核，例如：

```sh
shasum -a 256 '/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/results/V7_Maxwell_Debye_PML/V7_global_energy.md'
```

上面是供后续使用的复核命令；本轮哈希由 Python 读取计算，没有将示例命令冒充已执行记录。

## 本轮执行与完成状态

| 操作 | 实际结果 |
|---|---|
| 使用 `rg` 定位，`sed`／`cat`／`rg` 读取来源、配置和声明 | 完成材料定位与相关内容核对 |
| 首次 Python 元数据统计 | 因标准输入编码问题退出 1，未修改源文件 |
| 改用 ASCII 转义脚本重新统计 | 退出 0；28 份文件可读，三个基线哈希一致，V5 副本一致 |
| Lean／Lake 构建、SymPy 重跑、LaTeX 编译 | 本轮未执行，不能据本轮清点宣称重新通过 |

v0.0.1 完成项：

- [x] S1–S7 的实际来源、哈希和用途可追踪。
- [x] 旧材料按纸面证明、Lean 源码、符号脚本、构建日志、工作流审查分类。
- [x] 确认标量工程实际位置，并登记其范围、配置与历史记录。
- [x] 建立本清单与 `claim_ledger.md`，明确区分本轮观察和历史验证。

本轮仅新增上述两份文档；原来源及路线图保留不变。下一项任务为 **v0.0.2：建立原模型与主定理语义合同**，本轮未开始。
