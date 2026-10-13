# LeanPML：单层能量不是终点

用途：说明 v0.2.4 的初值计算、真实局部求导、实际积分及其边界。纸面推导与声明表集中在 [single_layer_failure.md](docs/single_layer_failure.md)，代码见 [SingleLayer.lean](LeanPML/PML/Obstructions/SingleLayer.lean)；本轮不另建阅读指南。历史进度见 [PROGRESS](PROGRESS.md)，上一版 README 留在 [阶段快照](logs/v0.2.4/before_README.md)。

本阶段研究 V7 §11.1：**单层耗散在指定兼容初值上可以为负**。这说明单层恒等式本身不足以给出单调性；并未构造一条完整二维 PDE 反例解。模块包含 5 个定义、20 条定理，均接入正式入口和审计。

## 已证明什么

| 层次 | 结果及条件 | 来源 |
|---|---|---|
| 定义组合 | 电块与极化块乘 μ，空间块直接相加；已有 ε、κ 分母与 1/2 不重复计算 | (6.2)、(7.7) |
| 初始代数 | q₀+τP₀=κu₀，五个不变量的初始数值为零；支撑条件用于 bq₀=0 | (2.4)、§11.1 |
| 初始导数 | 原方程初值推出 dP=dE=0，另提供绑定实际 E、P 的 HasDerivAt 版本 | (2.1)、§11.1 |
| 点态耗散 | D_initial(ξ)=−μc(ε+κ)ξ²；正材料参数下非正，ξ≠0 时严格负 | §11.1 未编号公式 |
| 实际积分 | 全开矩形上的初始密度可积，积分等于 −μc(ε+κ)∫f²；严格负额外要求 ∫f²>0 | 同上 |
| 真实局部时间 | 从实际一阶、二阶导数调用旧块求导，初始密度导数为 μc(ε+κ)ξ² | §11.1 局部时间计算 |
| 第二层 | 辅助演化初值推出 l′(0)=V；零区分量密度为 c(gₓ²+gᵧ²)，另有实际分量积分 | §11.1 末句、(7.2) |

三个耗散块的贡献是

$$
\mu D_e=-\mu\epsilon c\xi^2,\qquad
\mu D_D=-\mu\kappa c\xi^2,\qquad D_{\mathrm{sp}}=0.
$$

它们之和为 $D_{\mathrm{initial}}(\xi)=-\mu c(\epsilon+\kappa)\xi^2$。积分域是整个 $\Omega=(x_0,x_1)\times(y_0,y_1)$，采用二维 Lebesgue 测度。代码只要求几乎处处 $f(x)\ne0\Rightarrow p(x)=r(x)=0$，允许 $f=0$ 的吸收层有非零系数。没有把任意实数冒充平方范数，也没有把整个计算域改成物理区。

## 建议先读三条声明

在 [SingleLayer.lean](LeanPML/PML/Obstructions/SingleLayer.lean) 先看定义，再按顺序读（统一前缀为 `LeanPML.PML.Obstructions`）：

1. `initial_compatibility`：初始条件如何代入，为什么 Z₂ 项需要支撑条件。
2. `initialDissipation_eq`：三个旧块如何合成负耗散；`ring` 只处理代数。
3. `initialDissipation_rectangle_integral`：点态公式如何成为全域实际积分；跳转至它调用的 `initialDissipation_integral` 查看 `filter_upwards` 和积分线性性。

随后读 `hasDerivAt_initial_localEnergy`，辨别函数、导数值及 `HasDerivAt` 证据，再读第二层分量定理。代码将说明放在关键 `have`、`calc` 附近，简单步骤保持简短。

VS Code 中打开整个工程目录，在 Lean 文件里运行 `Lean 4: InfoView: Display Goal`。将光标移到 `have`、`apply`、`rw`、`calc` 前后，观察上下文与 `⊢` 目标。悬停查看类型，按 F12 跳到项目引理或 mathlib 定义；精确源码位置列于学习文档。导入未刷新时，保存并构建，再运行 `Lean 4: Server: Restart File`，无需更新依赖。

## 构建与审计

固定环境保持：Lean `v4.31.0`；Lake `5.0.0-src+68218e8`；mathlib `v4.31.0`，提交 `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`。工具链和依赖锁文件未改。本轮只补编译锁定依赖中此前未缓存的积分模块。

~~~sh
cd '/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML'
python3 scripts/run_logged.py --stage v0.2.4 lake_build lake build
python3 scripts/run_logged.py --stage v0.2.4 axioms_audit lake env lean Audit.lean
~~~

[最终构建日志](logs/v0.2.4/20261011T231924_138774_lake_build.log)和[独立公理审计日志](logs/v0.2.4/20261011T231954_467990_axioms_audit.log)保留完整输出；同名 JSON 记录命令、目录、时间和退出码。早期缺失 `.olean` 与函数改写失败也保存在同目录。正式构建包含 12 个证明模块、根入口和 Audit；审计覆盖原 134 条及新增 20 条，共 154 条。

`propext`、`Classical.choice`、`Quot.sound` 是标准基础公理，分别支持命题外延性、经典选择和商类型；它们不等于占位证明。验收检查没有 `sorryAx` 或自设占位公理。新增正式模块必须加入 `LeanPML.lean` 顶部导入，并在 `Audit.lean` 添加完整定理名后重新实际验证。

## PDF 标注与未完成范围

仅更新指定 [V7 PDF 副本](../results/V7_Maxwell_Debye_PML/V7_global_energy_副本.pdf) 的第 15 页 §11.1，范围、备份与验证见 [既有标注账本](docs/pdf_formalization_marks.md)。初值选择不是证明完成；红勾区分“初始兼容”“点态初值代数”“初值积分计算”“分量版；梯度接口待完成”。完整 PDE 初始能量率没有完成勾。

原文 §11.1 将单层导数交叉引用为 (7.7)，实际导数式是 (7.6)、耗散式是 (7.7)。负耗散公式没有编号，不能称为 §11.2 的 (11.1)。已记录差异，没有改原文、模型合同或路线图。

尚缺：从非零光滑紧支撑函数得到正平方积分的空间证明、真实梯度及其支撑性质、混合微分交换、原解与提升变量对应、Green/PEC、一般空间积分求导、Poincaré、两层闭合，以及原 PDE 解存在唯一性。因此，“给定足够正则解并适用完整能量律时初始增长”仍是条件性 PDE 解释。

下一阶段 **v0.3.1** 的入口是实际 L² 内积、加权状态与能量定义，计划模块为 `Analysis/EnergyCalculus.lean`、`PML/State.lean`、`PML/Energy.lean`。需要把局部块放入真实函数空间，保留无界权重与零区条件；本轮没有提前实现。
