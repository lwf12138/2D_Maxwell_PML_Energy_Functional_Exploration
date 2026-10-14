# PDF 形式化标注账本（截至 v0.3.1）

用途：把红勾连接到实际可编译定理、当前审计及准确范围。定义录入不算证明；真实空间积分/内积求导仍不等于 PDE 能量律。

## v0.3.1 新增记录：实际 L²、加权表示与积分求导（2026-10-13）

本节为追加记录；下面 v0.2.4、v0.2.3 及注释修订历史全部保留。本轮只修改实际/印刷第 **8、9、11、12 页**，新增 **4 个矢量红勾和 5 个定义/范围说明**。

### 当前证据与来源版本

- **B31**：[正式构建](../logs/v0.3.1/20261013T002136_137117_lake_build.log)／[命令、目录、退出码](../logs/v0.3.1/20261013T002136_137117_lake_build.json)，退出 0。
- **A31**：[独立公理审计](../logs/v0.3.1/20261013T002105_759533_axioms_audit.log)／[命令、目录、退出码](../logs/v0.3.1/20261013T002105_759533_axioms_audit.json)，退出 0。
- 本次审计 263 条定理（旧 154 条、新 109 条），无 sorryAx，仅标准 propext、Classical.choice、Quot.sound。主要新定理已在正式导入链中。
- [机器证据计划](../logs/v0.3.1/pdf/annotation_plan.json)逐项核对新勾定理的完整名称、源文件哈希和本次审计；同时重新核对旧 24 项标注的全部定理仍在本次审计中。
- [来源核对](../logs/v0.3.1/pdf/source_review.md)、[源文件哈希](../logs/v0.3.1/pdf/input_hashes.json)、[页码和旧批注快照](../logs/v0.3.1/pdf/read_only_inspection.json)：V7 MD/TEX/原 PDF、模型合同、工具链与依赖锁定均未变。
- 路线图进入本轮前只把 v0.2.4 四项改为已勾选；v0.3.1–v0.3.3 文字未改，见[差异记录](../logs/v0.3.1/pdf/roadmap_preexisting_diff.patch)。没有用历史勾选代替本轮构建。
- §11.1 的既有交叉引用疑点保留：(7.6) 是能量导数关系，(7.7) 是耗散定义。本轮未修改原文。

### 四个新红勾

#### v0.3.1 / weighted-embedding

- 页码：实际第 **8** 页；印刷页码 **8**。
- 定位：(5.6) 后“该空间连续嵌入 L²(Ω)²”。
- 类别：**实际 L² 分析；连续嵌入**。
- Lean 文件：[Energy.lean](../LeanPML/PML/Energy.lean)。
- 完整定理名：`LeanPML.PML.auxiliary_embedding_square`、`LeanPML.PML.physical_zero_on_absorption_zero`。
- 实际假设和结论：实际加权空间使用 √wψ 的 L² 闭子空间；恢复映射在全域 ν-a.e. 上定义，零吸收区为零，两个分量满足普通 L² 平方和不超过加权平方和。可测性和正区权重间隙由 SpatialAbsorption 原始条件推导。
- 未完成接口：具体矩形 Sobolev/零迹/真实弱梯度及演化保持仍待完成；本勾不覆盖 (5.7)–(5.8)。
- PDF 旁注：**✓ 加权空间嵌入；含零区处理**。
- 证据：**B31 + A31**。

#### v0.3.1 / energy-integral-inner

- 页码：实际第 **9** 页；印刷页码 **9**。
- 定位：(6.2) 实际积分/内积表示及由该式推出的路径求导（原文未单列）。
- 类别：**实际积分；实际 L²/加权空间时间求导**。
- Lean 文件：[EnergyIntegrals.lean](../LeanPML/PML/EnergyIntegrals.lean)。
- 完整定理名：`LeanPML.PML.fieldEnergyDensity_integrable`、`LeanPML.PML.fieldEnergy_eq_integral`、`LeanPML.PML.hasDerivAt_integral_fieldEnergy`。
- 实际假设和结论：真实 FieldState 的三个旧块密度可积，F_c 的内积表达与整个 ν 空间上的密度积分相等；各分量在其实际普通/加权空间中 HasDerivAt 时，积分能量导数为 fieldEnergyRate。未交换未经证明的逐点导数与积分。
- 未完成接口：primitive 方程、真实梯度、Green/PEC 尚未代入，导数未化为 −D_c；不代表正定性、图范数等价或 PDE 能量律。
- PDF 旁注：**✓ 积分/内积表示；非 PDE 能量律**。
- 证据：**B31 + A31**。

#### v0.3.1 / weighted-time

- 页码：实际第 **11** 页；印刷页码 **11**。
- 定位：(7.2) 后“加权空间的时间链式法则由 ψ∈C¹(L²_w) 保证”。
- 类别：**实际加权空间时间求导**。
- Lean 文件：[WeightedL2.lean](../LeanPML/Analysis/WeightedL2.lean)。
- 完整定理名：`LeanPML.Analysis.hasDerivAt_weighted_half_norm_sq`、`LeanPML.Analysis.hasDerivAt_physicalL2`。
- 实际假设和结论：在已构造的实际加权内积空间上，由 HasDerivAt X Xdot t 推出 ‖X‖²/2 的导数为内积，并由连续恢复映射得到物理 L² 路径导数。需要该加权范数下的导数，普通 L²/逐点可导不能代替。
- 未完成接口：一般辅助 PDE 的加权正则性传播、真实空间梯度和 Green/PEC 仍待完成；不把本链式法则等同于整个 (7.2) 能量恒等式。
- PDF 旁注：**✓ 加权空间求导；需该空间；路径可导**。
- 证据：**B31 + A31**。

#### v0.3.1 / spatial-integral

- 页码：实际第 **11** 页；印刷页码 **11**。
- 定位：(7.2) 的 L² 分量密度积分与非负子结论。
- 类别：**实际积分；分量耗散非负**。
- Lean 文件：[EnergyIntegrals.lean](../LeanPML/PML/EnergyIntegrals.lean)。
- 完整定理名：`LeanPML.PML.fieldSpatialDissipation_integrable`、`LeanPML.PML.fieldSpatialDissipation_eq_integral`、`LeanPML.PML.fieldSpatialDissipation_nonneg`、`LeanPML.PML.fieldSpatialDissipation_of_zeroAbsorption`。
- 实际假设和结论：四个有界可测耗散系数按方向乘实际 L² 分量平方，密度可积且积分非负；全零吸收 a.e. 时 S=c(‖h_x‖²+‖h_y‖²)。h=Λ−ψ 是 L² 分量，零区贡献保留。
- 未完成接口：真实 h=∂ᵢv 接口未实现；本轮未单独形式化 Ω₊/Z 两个限制积分的分区等式，也未证明空间块与 primitive/Green 组合后的能量律。
- PDF 旁注：**✓ 分量积分非负；真实梯度；接口待完成**。
- 证据：**B31 + A31**。

### 实际空间、定义说明与未完成部分

- [WeightedL2.lean](../LeanPML/Analysis/WeightedL2.lean) 中 `LeanPML.Analysis.weightedSubspace_isClosed`、`weighted_completeSpace` 已证明平方根坐标空间为闭子空间并完备；`physicalL2_injective`、`physicalL2_weightedOfFunction`、`weightedOfFunction_congr` 处理双向恢复和代表元独立；`weighted_norm_sq_eq_integral`、`weighted_inner_eq_integral` 给出实际加权积分表示。它们均在 A31 中；本勾没有假设 w 本质有界。
- [SpatialCoefficients.lean](../LeanPML/PML/SpatialCoefficients.lean) 用实际可测 p/r 和原始幅度条件构造系数；分离入口保留 p(x)、r(y)，a.e. 入口选择等价的良好代表。ν 可以取整个开矩形限制测度，未缩域。
- 第 8 页 (5.5)–(5.6) 增加实际加权表示说明，**定义本身不打完成勾**。新增嵌入勾与已有“下界/无界；系数性质”勾分别对应分析和点态代数。
- 第 9 页页底说明 (6.2)–(6.5) 已有实际 L²/积分定义。`FieldState` 的 V 是速度坐标；`StateHasDerivAt` 绑定各分量真实导数，`SameSourcePath` 连接同一来源的两层；内部的导数层时间关系另经邻域等式推出。空间域/弱梯度/零迹仍是显式 Conditional 接口。
- (6.4) 的 `energy7` 和 (6.5) 的 `graphSquare7` 使用 `scaleK` 与同源路径。`graphSquare` 仍是图范数平方候选，未证明其零分离或能量双边估计。
- 第 11 页 (7.7) 只标“实际积分定义；符号未定”。`fieldDissipationDensity_integrable`、`fieldDissipation_eq_integral` 已连接旧三个块和实际积分，但 D_c 不被声明非负。
- 第 12 页 (7.8) 只标“左式实际定义；右式能量律仍待完成”。`twoLayerDissipation_integrable`、`twoLayerDissipation_eq_integral` 保证定义合法；`dissipation7` 用同源 first.R/second.R 表示 P_t/P_tt，未证明 D₇ 非负或 E₇′=−D₇。
- 第 11 页旧“空间积分待完成”“仅系数界；非空间积分”批注完整保留；页底新增 v0.3.1 限定，说明新勾覆盖实际分量积分和范数路径求导，旧勾保留历史范围。没有把新证明扩大为 primitive/Green 组合后的恒等式。
- **不打完成勾：** (6.7)–(6.10)、(7.5)–(7.8) 的完整能量律、(9.5)–(9.7)、具体梯度/零迹/Green/Poincaré、完整 PDE 对应、解存在唯一性。T10、T11、T12、T15、T17、T18 仍按已实现子结论逐项登记，不整体标记完成。

### 备份、编辑、视觉验收与可重复性

- 新建[修改前副本](../logs/v0.3.1/pdf/before_v0.3.1_20261013T002329.pdf)；[备份信息](../logs/v0.3.1/pdf/backup.json)。旧阶段及用户原有备份未覆盖。
- 修改前 SHA-256：`f318a9a0e4ac0721f61fffc601388e16be4e568b4efcbb3b2de3e9ad19a2b757`。
- 修改后 SHA-256：`9b55183d444b9efa91e873dbbef1d7e73756962106f9c51d0de108f78b49c2ac`。
- [标注证据脚本](../logs/v0.3.1/pdf/build_mark_plan.py)、[矢量编辑脚本](../logs/v0.3.1/pdf/annotate_pdf.py)、[重新打开/渲染脚本](../logs/v0.3.1/pdf/verify_pdf.py)和[视觉/像素核验脚本](../logs/v0.3.1/pdf/record_visual_qa.py)保留；稳定标记 ID 与计划哈希防止重复叠加。
- [编辑日志](../logs/v0.3.1/20261013T002336_826429_pdf_annotate.log)、[重新打开及渲染日志](../logs/v0.3.1/20261013T002342_329628_pdf_verify_render.log)、[视觉验收日志](../logs/v0.3.1/20261013T002436_189341_pdf_visual_qa.log)均退出 0；[机器验收](../logs/v0.3.1/pdf/verification.json)、[逐页视觉记录](../logs/v0.3.1/pdf/visual_review.json)。
- 18 页、页面尺寸与页序不变；原文可选文本保留，141 项旧批注/链接全部保留；新增 9 项后总计 150 项。
- 已打开并逐页检查全部修改页 8、9、11、12。侧栏 6pt、说明 6.5–7pt 的嵌入中文和矢量勾清晰；没有裁切或遮挡正文、公式、编号、页码及旧批注。标记框之外渲染像素完全相同；其余 14 页内容流字节相同。
- 只读准备曾因脚本名 inspect.py 遮蔽标准库而失败，改名后成功；定位预检曾发现第 11 页页底说明碰页码，在编辑前下移修复。两类失败和成功日志均保留，未把未运行或失败命令登记为通过。

---

# PDF 形式化标注账本（截至 v0.2.4）

用途：把 PDF 旁的每个红勾连接到当前可编译的 Lean 定理、实际公理审计和明确的范围限制。定义与假设的录入不算证明；局部时间结论不算完整空间/PDE 结论。

## v0.2.4 新增记录：§11.1 初值计算（2026-10-11）

本节是当前追加记录；下方 v0.2.3 及后续注释修订记录全部保留为历史。v0.2.4 仅修改实际/印刷第 **15** 页，不重画旧红勾。

### 当前证据与版本

- **B24**：[正式构建](../logs/v0.2.4/20261011T231924_138774_lake_build.log)／[命令、目录、退出码](../logs/v0.2.4/20261011T231924_138774_lake_build.json)，退出 0。
- **A24**：[独立公理审计](../logs/v0.2.4/20261011T231954_467990_axioms_audit.log)／[命令、目录、退出码](../logs/v0.2.4/20261011T231954_467990_axioms_audit.json)，退出 0。
- 全工程 154 条定理均在本次审计中；仅有标准 `propext`、`Classical.choice`、`Quot.sound`。无 `sorryAx` 或自定义证明占位公理。
- [本轮机器证据计划](../logs/v0.2.4/pdf/annotation_plan.json)核对新模块正式导入、完整定理名、源码哈希及审计。还逐项确认旧计划全部 20 项标注所引用定理仍出现在本次审计中，不重复添加旧勾。
- [来源只读核对](../logs/v0.2.4/pdf/source_review.md)与[哈希/页码/原批注快照](../logs/v0.2.4/pdf/read_only_inspection.json)：V7 MD/TEX/原 PDF、已接受模型合同未变。路线图在进入本轮前仅将 v0.2.3 四项勾选；v0.2.4/v0.3.1 数学任务未改，本轮未写路线图。
- §11.1 首段“精确导数见 (7.7)”的交叉引用不准确：**(7.6) 是能量导数关系，(7.7) 是耗散表达式**。本轮仅增加旁注提醒，原文保留。§11.1 负耗散式没有编号，未误标为 §11.2 的 (11.1)。

### 新增红勾的范围

### v0.2.4 / initial-compatibility

- PDF 页码：实际第 **15** 页；印刷页码 **15**。
- 定位：§11.1 未编号初值行：仅对应初始兼容关系；均为 §11.1 的未编号内容。
- 验证类别：**点态代数**。
- Lean 文件：[SingleLayer.lean](../LeanPML/PML/Obstructions/SingleLayer.lean)。
- 完整定理名：`LeanPML.PML.Obstructions.initial_compatibility`。
- 已验证范围：u₀=0、P₀=κξ、q₀=−τκξ、原辅助量与φ₀为零，ξ非零处p=r=0时，五个初始不变量的数值为零。只标兼容的代数核验，初值选择本身不算证明。
- 未完成接口：磁不变量的时间保持、真实梯度/提升、完整兼容函数空间成员资格仍待完成。
- 本轮新增红勾：**✓ 初始兼容；已核验；仅点态数值**。
- 证据：**B24 + A24**；上述声明均在正式导入链和本次审计输出中。

### v0.2.4 / initial-density

- PDF 页码：实际第 **15** 页；印刷页码 **15**。
- 定位：§11.1 未编号负耗散公式：点态初值密度；均为 §11.1 的未编号内容。
- 验证类别：**点态代数**。
- Lean 文件：[SingleLayer.lean](../LeanPML/PML/Obstructions/SingleLayer.lean)。
- 完整定理名：`LeanPML.PML.Obstructions.initialDissipation_eq`、`LeanPML.PML.Obstructions.initialDissipation_nonpos`、`LeanPML.PML.Obstructions.initialDissipation_neg`。
- 已验证范围：三个旧块直接组合，κ≠0及ξ≠0处p=r=0推出D_initial(ξ)=−μc(ε+κ)ξ²；材料及c正性推出非正，ξ≠0时严格负。
- 未完成接口：不是一条已存在的完整PDE解；完整空间能量律、初始解存在性未完成。
- 本轮新增红勾：**✓ 点态初值代数；材料正性**。
- 证据：**B24 + A24**；上述声明均在正式导入链和本次审计输出中。

### v0.2.4 / initial-integral

- PDF 页码：实际第 **15** 页；印刷页码 **15**。
- 定位：§11.1 未编号负耗散公式：实际特殊初值积分；均为 §11.1 的未编号内容。
- 验证类别：**实际积分**。
- Lean 文件：[SingleLayer.lean](../LeanPML/PML/Obstructions/SingleLayer.lean)。
- 完整定理名：`LeanPML.PML.Obstructions.initialDissipation_integral`、`LeanPML.PML.Obstructions.initialDissipation_integral_neg`、`LeanPML.PML.Obstructions.initialDissipation_rectangle_integral`。
- 已验证范围：实际测度m和函数f,p,r，平方可积与几乎处处支撑条件推出密度可积及∫D_initial=−μc(ε+κ)∫f²；包含全开矩形的二维Lebesgue限制测度入口。严格负额外要求∫f²>0。
- 未完成接口：尚未形式化非零光滑紧支撑函数的正L²范数、Lp等价类范数接口；不是一般时间积分求导、PDE能量律或解存在。
- 本轮新增红勾：**✓ 初值积分计算；须平方可积；严格负须正积分**。
- 证据：**B24 + A24**；上述声明均在正式导入链和本次审计输出中。

### v0.2.4 / second-layer-components

- PDF 页码：实际第 **15** 页；印刷页码 **15**。
- 定位：§11.1 λ_t(0)=∇f 和 S₁(0)=c‖∇f‖²：仅分量接口与其积分；均为 §11.1 的未编号内容。
- 验证类别：**真实局部时间；分量代数；实际分量积分**。
- Lean 文件：[SingleLayer.lean](../LeanPML/PML/Obstructions/SingleLayer.lean)。
- 完整定理名：`LeanPML.PML.Obstructions.hasDerivAt_initial_flux`、`LeanPML.PML.Obstructions.secondLayerSpatialInitial_zero`、`LeanPML.PML.Obstructions.secondLayerSpatialInitial_eq`、`LeanPML.PML.Obstructions.secondLayerSpatialInitial_integral`。
- 已验证范围：真实HasDerivAt辅助演化在h₀=l₀=0时给l′(0)=V；复用零吸收空间耗散得c(gx²+gy²)。分量的独立支撑条件与平方可积性给实际分量积分c(∫gx²+∫gy²)。
- 未完成接口：V、gx、gy与真实∂ᵢf的梯度对应、混合微分交换、梯度支撑性质、Poincaré和两层闭合未完成。
- 本轮新增红勾：**✓ 分量及其积分；梯度接口；待完成**。
- 证据：**B24 + A24**；上述声明均在正式导入链和本次审计输出中。


### 本轮只登记、不打完成红勾的内容

- §11.1 的初值选择是输入；旁边“初始兼容已核验”只指从这些数据推出的五个初始数值关系，不代表存在满足全 PDE/边界/正则性的解。
- (6.2)、(7.7)：`singleLayerEnergy`、`singleLayerDissipation` 直接组合既有三个局部块；这里只登记定义对应，不为定义录入打“已证明”勾。
- `LeanPML.PML.Obstructions.initial_derivative_values` 是原方程初值的代数化简；`hasDerivAt_initial_fields_zero` 从真实导数证据得到 E、P 的初始零导数。原磁旋度/提升/空间迹的兑现仍不在这一包装定理中。
- `LeanPML.PML.Obstructions.hasDerivAt_initial_localEnergy` 与 `initial_localEnergy_rate_pos` 已证明真实**局部时间密度**的初始导数及正号。PDF 正文的 $\mathcal F_c[U_0]'(0)>0$ 指完整空间能量，故这里**不打完整 PDE 求导完成勾**；页底注明它仍依赖完整能量律及解存在/正则性接口。
- `singleLayerEnergy_initial` 的特殊初值能量代数值已核验；未因此证明一般正定性或单调性。
- 未给 (6.7)–(6.10)、(7.5)–(7.8)、(9.5)–(9.7) 的完整结论添加完成勾。Poincaré、一般加权路径积分求导、Green/PEC、两层闭合仍待完成。
- 旧图例描述截至 v0.2.3 的空间接口状态；本页新增说明明确区分已经完成的**特殊初值积分**与尚未完成的**一般 PDE 空间能量律**，不改写旧用户批注。

### 备份、编辑和视觉验收

- 新建[修改前副本](../logs/v0.2.4/pdf/before_v0.2.4_20261011T232305.pdf)，不覆盖任何旧阶段备份；[备份哈希记录](../logs/v0.2.4/pdf/backup.json)。
- 修改前 SHA-256：`0735771fa5d38adc70a74f21be3c109b490d1c91587414f874ac0c2d049409be`。
- 修改后 SHA-256：`f318a9a0e4ac0721f61fffc601388e16be4e568b4efcbb3b2de3e9ad19a2b757`。
- [定位与证据脚本](../logs/v0.2.4/pdf/build_mark_plan.py)、[矢量标注脚本](../logs/v0.2.4/pdf/annotate_pdf.py)、[保留性与渲染脚本](../logs/v0.2.4/pdf/verify_pdf.py)均保留。稳定标记 ID 和计划哈希防止重跑重复叠加。
- [编辑日志](../logs/v0.2.4/20261011T232336_537816_pdf_annotate.log)、[重新打开/渲染日志](../logs/v0.2.4/20261011T232342_713491_pdf_verify_render.log)均退出 0；[机器验收](../logs/v0.2.4/pdf/verification.json)、[视觉验收](../logs/v0.2.4/pdf/visual_review.json)。
- 18 页及原始页面尺寸/页序不变；全部原文可选文本和 135 项原批注保留。本次新增 **4 个矢量红勾与 2 个范围说明**，总批注 141 项。
- 已重新打开最终 PDF，并渲染本轮全部修改页（第 15 页）逐页检查。侧栏 6pt 和页底 7pt 中文可见，勾号清晰，没有裁切、覆盖公式/编号/正文或旧批注。
- 准备脚本第一次因 pypdf 将 `/Annots` 返回间接对象而失败，目标 PDF 尚未编辑；修复读取方式后成功。保留[原失败](../logs/v0.2.4/20261011T232305_726240_pdf_evidence_plan.log)与[成功重试](../logs/v0.2.4/20261011T232326_564193_pdf_evidence_plan_retry.log)，同一新备份经哈希确认后复用，未覆盖。

---

## 以下为 v0.2.3 历史记录

## 来源与保护

- 目标仅为 `results/V7_Maxwell_Debye_PML/V7_global_energy_副本.pdf`；原 PDF、MD、TEX 及既有“标注前备份”保持原样。
- 副本为 18 页，实际页序号从 1 开始，逐页与印刷页码 1–18 相同。修改前已有 16 处红勾/说明批注以及 110 个链接；全部保留。
- 本轮修改前备份：[带阶段和时间的副本](../logs/v0.2.3/pdf/before_v0.2.3_20261010T232231.pdf)。
- 修改前 SHA-256：`066b6d82f7539c0270b343ab162f5553f8728f120ec03b34b8438dd467a31a1d`。
- 原正文 SHA-256 仍为 `0a7f73a25cb119eeb75b3e7b3c3f2fbb3b319250f3354ed4dcad0ecff8eff4fb`。现有副本的 18 页抽取文字都以原 PDF 全页文字为前缀；额外内容为此前标注。未将另一版本公式混入。
- [输入版本、页面与原批注快照](../logs/v0.2.3/pdf/before_inspection.json)；[坐标及机器可核对计划](../logs/v0.2.3/pdf/annotation_plan.json)。

## 当前源码、构建与审计证据

- **B**：[本轮默认构建](../logs/v0.2.3/20261010T232910_472603_lake_build_retry.log)／[命令、目录、退出码](../logs/v0.2.3/20261010T232910_472603_lake_build_retry.json)，退出 0。
- **A**：[本轮独立审计](../logs/v0.2.3/20261010T232931_121820_axioms_audit_retry.log)／[命令、目录、退出码](../logs/v0.2.3/20261010T232931_121820_axioms_audit_retry.json)，退出 0。
- [证据核对脚本](../logs/v0.2.3/pdf/build_mark_plan.py)重新读取当前声明、正式根入口和这次审计。134 条定理逐项审计，仅有标准 `propext`、`Classical.choice`、`Quot.sound`；没有 `sorryAx`。
- 下列每项都使用 **B + A**，不单凭旧 PROGRESS 打勾。定义另列，不伪装成已证明定理。具体源码 SHA-256 已写入机器计划，PDF 编辑前再次检查未变。

## 逐项登记

### old-01：(2.4) 的 CD

- 页码：实际第 **4** 页；印刷页码 **4**。
- 类型：**局部时间**。
- 文件：[LeanPML/PML/TimeInvariants.lean](../LeanPML/PML/TimeInvariants.lean)。
- 完整定理名：`LeanPML.PML.hasDerivAt_CD_zero`、`LeanPML.PML.CD_eq_initial`、`LeanPML.PML.CD_compatibility`。
- 已核验的准确范围：(2.4) 仅 CD：固定空间点的真实导数为零和区间常值；初始零兼容推出全时段兼容。u,q的积分构造、函数空间尚未形式化。
- 未完成接口：时间积分提升、实际场正则性及另外两个磁不变量。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“CD；局部时间”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### old-02：(2.4) 的 CZ1、CZ2

- 页码：实际第 **4** 页；印刷页码 **4**。
- 类型：**局部时间**。
- 文件：[LeanPML/PML/TimeInvariants.lean](../LeanPML/PML/TimeInvariants.lean)。
- 完整定理名：`LeanPML.PML.hasDerivAt_CZ1_zero`、`LeanPML.PML.hasDerivAt_CZ2_zero`、`LeanPML.PML.CZ1_eq_initial`、`LeanPML.PML.CZ2_eq_initial`。
- 已核验的准确范围：(2.4) 仅 CZ1、CZ2 的真实求导及常值保持，允许 b=0。磁辅助不变量 Cx、Cy 尚未形式化。
- 未完成接口：磁辅助 Cx、Cy；不是五个不变量全部完成。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“CZ1/CZ2；局部时间”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### old-03：(2.5) 中 Z1、Z2 两项

- 页码：实际第 **4** 页；印刷页码 **4**。
- 类型：**局部时间**。
- 文件：[LeanPML/PML/TimeInvariants.lean](../LeanPML/PML/TimeInvariants.lean)。
- 完整定理名：`LeanPML.PML.CZ1_compatibility`、`LeanPML.PML.CZ2_compatibility`、`LeanPML.PML.Z1_zero_of_zero_absorption`、`LeanPML.PML.Z2_zero_of_zero_absorption`。
- 已核验的准确范围：(2.5) 仅 Z1=-εbu、Z2=-bq 的固定空间点版本，从初始兼容和原时间方程推出全时段兼容。Qx,Qy重构与完整时域等价未完成。
- 未完成接口：Qx、Qy 重构及完整双向 PDE 等价。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“Z1/Z2；初值保持”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### old-04：(5.2) 定义后的 A、K、c* 正性

- 页码：实际第 **7** 页；印刷页码 **7**。
- 类型：**代数；定义不计证明**。
- 文件：[LeanPML/PML/Coefficients.lean](../LeanPML/PML/Coefficients.lean)。
- 完整定理名：`LeanPML.PML.materialA_pos`、`LeanPML.PML.scaleK_pos`、`LeanPML.PML.threshold_pos`。
- 已核验的准确范围：(5.2) A、K、c* 的定义及正性已验证；CP只是给定正参数。(5.1)的矩形Poincaré不等式尚未证明。
- 未完成接口：CP 仅为给定正参数；矩形 Poincaré (5.1)。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“参数代数；正性已证”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### old-05：(5.3) 邻旁的阈值等价子结论

- 页码：实际第 **7** 页；印刷页码 **7**。
- 类型：**假设；派生代数**。
- 文件：[LeanPML/PML/Coefficients.lean](../LeanPML/PML/Coefficients.lean)。
- 完整定理名：`LeanPML.PML.le_threshold_iff_explicit`。
- 已核验的准确范围：(5.3) 仅 c≤c* 与 c²K≤1、8cAK≤κτ、8cAτ≤κ 的双向等价；L∞吸收场及空间幅度条件未在本阶段构造。
- 未完成接口：(5.3) 本身是输入；尚无 L∞ 场和空间幅度模型。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“阈值等价；实数条件”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### old-06：(5.4) 全部系数界

- 页码：实际第 **7** 页；印刷页码 **7**。
- 类型：**代数**。
- 文件：[LeanPML/PML/Coefficients.lean](../LeanPML/PML/Coefficients.lean)。
- 完整定理名：`LeanPML.PML.absorptionSum_le_half`、`LeanPML.PML.absorptionProduct_le_c_sq_sixteenth`、`LeanPML.PML.absorptionSum_mul_sub_product_nonneg`、`LeanPML.PML.le_threshold_iff_explicit`、`LeanPML.PML.c_mul_tau_bounds`。
- 已核验的准确范围：(5.4) 从非负p,r、幅度限制和精确阈值推出所列 a,b,ac-b,c²K,cτ 的界。是固定空间点的实数代数，保留零吸收。
- 未完成接口：从点值界提升到实际空间场。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“全部系数界；固定点”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### old-07：(5.5) 分支定义与零区值

- 页码：实际第 **8** 页；印刷页码 **8**。
- 类型：**定义；派生代数**。
- 文件：[LeanPML/PML/Weights.lean](../LeanPML/PML/Weights.lean)。
- 完整定理名：`LeanPML.PML.weights_of_sum_zero`。
- 仅作定义登记：`LeanPML.PML.energyWeightX`、`LeanPML.PML.energyWeightY`；不因此添加完成红勾。
- 已核验的准确范围：(5.5) w的正吸收分支和零延拓定义及分支性质；零区取0。尚未构造(5.6)的加权函数空间。
- 未完成接口：定义本身不是待证结论；(5.6) 加权空间。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“权重分支；含零吸收”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### old-08：(5.5) 后 w≥3/2 和可能无界

- 页码：实际第 **8** 页；印刷页码 **8**。
- 类型：**代数**。
- 文件：[LeanPML/PML/Weights.lean](../LeanPML/PML/Weights.lean)。
- 完整定理名：`LeanPML.PML.energyWeights_lower_bound`、`LeanPML.PML.energyWeights_unbounded`。
- 已核验的准确范围：正吸收分支w≥3/2，及满足幅度限制的趋零吸收族无统一有限上界。下界不适用于零延拓；未证明加权空间嵌入。
- 未完成接口：下界限 a>0；加权空间构造及嵌入。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“下界/无界；系数性质”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### old-09：(7.2) 后耗散权重有界子结论

- 页码：实际第 **11** 页；印刷页码 **11**。
- 类型：**代数**。
- 文件：[LeanPML/PML/Weights.lean](../LeanPML/PML/Weights.lean)。
- 完整定理名：`LeanPML.PML.dissipationPlus_bounds`、`LeanPML.PML.dissipationPlus_le_five_quarters`、`LeanPML.PML.dissipationMinus_bounds`。
- 已核验的准确范围：(7.2) 仅分式耗散系数非负及有界性已证；未证明空间积分或全域恒等式。零区c|∇v|²仍按原文保留。
- 未完成接口：全积分 (7.2) 和空间时间链式法则。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“仅系数界；非空间积分”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### old-10：(7.3)

- 页码：实际第 **11** 页；印刷页码 **11**。
- 类型：**局部时间；代数**。
- 文件：[LeanPML/PML/LocalElectric.lean](../LeanPML/PML/LocalElectric.lean)。
- 完整定理名：`LeanPML.PML.electric_rate_identity`、`LeanPML.PML.hasDerivAt_electricEnergyAlong`、`LeanPML.PML.hasDerivAt_electricEnergyAlong_exampleU`。
- 已核验的准确范围：(7.3) 电块代数与实际时间函数HasDerivAt求导。二阶证据直接针对deriv v；Fe含ε/2，完整能量还需μ和空间积分。De未宣称非负。
- 未完成接口：实际场、μ 因子、空间积分；De 未证非负。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“局部时间；真实求导”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### old-11：(7.4) 前未编号移位约束

- 页码：实际第 **11** 页；印刷页码 **11**。
- 类型：**局部时间**。
- 文件：[LeanPML/PML/LocalDebye.lean](../LeanPML/PML/LocalDebye.lean)。
- 完整定理名：`LeanPML.PML.polar_constraint_derivative`、`LeanPML.PML.polar_shifted_constraint`。
- 已核验的准确范围：由真实导数与邻域内z+τR=κv，推出κv_t=R+τR_t，再推出移位约束。单点兼容不足以求导。
- 未完成接口：场层兼容、微分与积分的接口。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“兼容求导；邻域关系”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### old-12：(7.4)

- 页码：实际第 **11** 页；印刷页码 **11**。
- 类型：**局部时间；代数**。
- 文件：[LeanPML/PML/LocalDebye.lean](../LeanPML/PML/LocalDebye.lean)。
- 完整定理名：`LeanPML.PML.polar_rate_algebra`、`LeanPML.PML.hasDerivAt_polarQuadratic`、`LeanPML.PML.hasDerivAt_polarEnergy`、`LeanPML.PML.hasDerivAt_polarEnergy_on_Ioo`、`LeanPML.PML.hasDerivAt_example_polarEnergy`。
- 已核验的准确范围：(7.4) Q逐项真实求导，再由邻域兼容和κ≠0证明FD=Q/(2κ)的HasDerivAt恒等式；含开区间入口和非零路径实例。未乘μ、未空间积分；DD未宣称非负。
- 未完成接口：实际场、μ 因子、空间积分；DD 未证非负。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“局部时间；真实求导”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### old-13：(8.1)

- 页码：实际第 **12** 页；印刷页码 **12**。
- 类型：**代数**。
- 文件：[LeanPML/PML/LocalDebye.lean](../LeanPML/PML/LocalDebye.lean)。
- 完整定理名：`LeanPML.PML.polarQuadratic_eq_reduced`、`LeanPML.PML.polarEnergy_eq_reduced`。
- 已核验的准确范围：(8.1) 在单点z+τR=κv下精确重写Q，及由调用者得到FD表达式（仍除以2κ）。不是完整能量正定性。
- 未完成接口：Q 到 FD 仍除 2κ；完整能量正定性。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“约束消元；代数已证”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### old-14：(8.2)

- 页码：实际第 **12** 页；印刷页码 **12**。
- 类型：**代数**。
- 文件：[LeanPML/PML/LocalDebye.lean](../LeanPML/PML/LocalDebye.lean)。
- 完整定理名：`LeanPML.PML.polar_coefficients_bounds_of_local_conditions`、`LeanPML.PML.polar_coefficients_bounds_of_threshold`。
- 已核验的准确范围：(8.2) 全部四组界，保留3/4、5/4、37/64、9/16；最高入口从材料正性、c≤c*及吸收幅度推导中间界，没有预设目标界。
- 未完成接口：空间范数估计和后续正定性。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“四组系数界；全部已证”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### old-15：(9.2) 前 θ 分支及 0≤θ≤1、和为1

- 页码：实际第 **14** 页；印刷页码 **14**。
- 类型：**代数；定义不计证明**。
- 文件：[LeanPML/PML/Weights.lean](../LeanPML/PML/Weights.lean)。
- 完整定理名：`LeanPML.PML.theta_partition`。
- 仅作定义登记：`LeanPML.PML.thetaX`、`LeanPML.PML.thetaY`；不因此添加完成红勾。
- 已核验的准确范围：(9.2)前的θ分支定义、0≤θ≤1及θx+θy=1；零区各取1/2。J的空间积分、(9.3)、(9.5)未形式化。
- 未完成接口：J 空间积分与 (9.3)、(9.5)。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“分配权重；分支已证”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### old-16：(9.6) 后文字中的 KS²≤1/16

- 页码：实际第 **14** 页；印刷页码 **14**。
- 类型：**代数**。
- 文件：[LeanPML/PML/Coefficients.lean](../LeanPML/PML/Coefficients.lean)。
- 完整定理名：`LeanPML.PML.scale_mul_amplitude_sq_le_sixteenth`。
- 已核验的准确范围：本句中KS²≤1/16的系数代数已证；(9.6)完整空间估计及耗散分配未证明。
- 未完成接口：完整 (9.6) 空间估计与耗散分配。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“KS²≤1/16；代数已证”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### zero-preservation：§5.2：在 Z 上 φ_t=0，因此 φ₀=0 保持（未编号）

- 页码：实际第 **8** 页；印刷页码 **8**。
- 类型：**局部时间**。
- 文件：[LeanPML/PML/LocalSpatial.lean](../LeanPML/PML/LocalSpatial.lean)。
- 完整定理名：`LeanPML.PML.zeroSpatial_compatibility_preserved`。
- 已核验的准确范围：固定点两个时间函数闭区间连续，内部真实辅助演化；非负吸收且 a=0，从初始 l(0)=h(0) 推出整段 l=h，包括 T=0。
- 未完成接口：不是 (5.7) 一般积分解公式、五个不变量整体、加权正则性或 PDE 提升。。
- 本轮红勾：**新增**，旁注明确为“✓ 时间保持；须初值 f=0；空间接口待证”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### spatial-positive：(7.1) 的正吸收分支

- 页码：实际第 **10** 页；印刷页码 **10**。
- 类型：**局部时间**。
- 文件：[LeanPML/PML/LocalSpatial.lean](../LeanPML/PML/LocalSpatial.lean)。
- 完整定理名：`LeanPML.PML.spatial_weight_balance`、`LeanPML.PML.spatial_rate_identity`、`LeanPML.PML.hasDerivAt_spatialAuxiliary`、`LeanPML.PML.hasDerivAt_spatialEnergy_pos`、`LeanPML.PML.hasDerivAt_spatialEnergy2D`。
- 已核验的准确范围：a>0 下权重平衡、数值恒等式，以及真实时间 h'=V、l'=V+σⱼh−σᵢl 推出的 Fsp 求导；包含两个方向。
- 未完成接口：h 与真实空间梯度、混合导数交换、可测可积、空间积分、Green/PEC 未实现。。
- 本轮红勾：**新增**，旁注明确为“✓ 局部时间版；空间接口待证；积分待完成”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### spatial-zero：(7.1) 后零吸收区未编号二维公式

- 页码：实际第 **10** 页；印刷页码 **10**。
- 类型：**局部时间**。
- 文件：[LeanPML/PML/LocalSpatial.lean](../LeanPML/PML/LocalSpatial.lean)。
- 完整定理名：`LeanPML.PML.hasDerivAt_zeroSpatialComponent`、`LeanPML.PML.hasDerivAt_zeroSpatial2D`、`LeanPML.PML.hasDerivAt_spatialEnergy_zero`、`LeanPML.PML.zeroSpatial_compatibility_preserved`。
- 已核验的准确范围：h 的实际时间导数给出 h²/2 和双分量平方和的导数；接回分支能量时明确需要 l=h，保留 c(hx²+hy²)。
- 未完成接口：p=r=0 不自动给出兼容；完整 PDE 中零辅助量来源、实际梯度及空间积分仍待兑现。。
- 本轮红勾：**新增**，旁注明确为“✓ 局部时间版；零区须兼容；空间接口待证”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### spatial-pointwise：(7.2) 被积式的点态非负与独立零区密度（不是整式）

- 页码：实际第 **11** 页；印刷页码 **11**。
- 类型：**代数；点态**。
- 文件：[LeanPML/PML/LocalSpatial.lean](../LeanPML/PML/LocalSpatial.lean)。
- 完整定理名：`LeanPML.PML.spatialDissipation_nonneg`、`LeanPML.PML.spatialDissipation2D_nonneg`、`LeanPML.PML.spatialDissipation2D_of_sum_zero`。
- 已核验的准确范围：0≤p,r≤S≤c/4、c>0 下，两个方向的分支密度非负；零区精确为 c(hx²+hy²)。
- 未完成接口：该勾只指被积子表达式；没有完成 (7.2) 积分算子、可积性、加权路径求导或全域能量恒等式。。
- 本轮红勾：**新增**，旁注明确为“✓ 点态非负；空间积分；待完成”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

## 对旧勾的限定与本轮图例

| 位置 | 本轮处理 | 原因 |
|---|---|---|
| 第 1 页上方空白 | 新增三行图例，无完成勾 | 区分代数、真实时间、空间/PDE；明确假设与定义不计证明 |
| 第 7 页 (5.3) 左侧 | 增加“(5.3) 为输入；旧勾仅指阈值等价” | 保留原勾，但排除把小量假设本身当结论的歧义 |
| 第 8 页 (5.5) 左侧 | 增加“(5.5) 为定义；旧勾仅指零分支计算” | 保留原勾，准确对应 `weights_of_sum_zero`；不能用定义录入代表证明完成 |
| 第 11 页 (7.3)、(7.4) 旧旁注下方 | 各补“积分待完成” | 旧局部时间勾不扩展为空间积分结果 |

以上不删除、不改写任何用户旧批注。第 8 页新“时间保持”只定位于未编号零区保持句，不覆盖邻近 (5.7) 或 (5.8)。第 11 页新点态勾位于被积子表达式左侧，未给 (7.2) 整个积分编号打全完成勾。

## 不打完成勾的内容

- (2.4) 的两个磁辅助不变量、(2.5) 的磁场重构、(2.6) 完整 primitive/PDE 对应。
- (5.1) 矩形 Poincaré，(5.6) 加权空间及嵌入，(5.7) 一般积分表示和 (5.8) 加权正则性估计。
- (6.1) 在局部极化路径中是明确的邻域兼容输入；(6.2) 只有局部块定义，完整积分能量不是本轮结论。
- (6.7)–(6.10) 的图范数等价、最终耗散、单调性及场控制；(7.5)–(7.8) 的 Green/边界和整体能量恒等式。
- (9.5)–(9.7) 的空间估计和耗散闭合。旧第 14 页勾仅覆盖 θ 的代数性质与 KS²≤1/16，不能覆盖这些整体结论。
- v0.0.3、v0.1.1、v0.1.2 的教学标量与无空间 Debye 能量，以及一般时间单调/常值接口，均已在当前正式导入和审计中复核；它们没有可直接等同的完整 V7 公式，因此不硬给论文 PDE 结论打勾。
- v0.1.3 的非零实例、v0.2.2 的局部路径、v0.2.3 的四区代数和非零路径均是上述定理的正式调用证据；不额外冒充完整二维解。

## 编辑、复核与可重复性

- [编辑脚本](../logs/v0.2.3/pdf/annotate_pdf.py)只叠加矢量线条和嵌入字体文字；保留原页面大小、页序、公式和可选中文本。
- 每个新增标记使用稳定 ID `LeanPML.v0.2.3.*`；PDF 元数据保存计划哈希。重复运行同一计划直接跳过，不重复画勾；若用户在此后改变副本，脚本拒绝从旧备份覆盖。
- 改前备份只新建，不覆盖旧“标注前备份”。实际操作记录、标记定位和渲染均保存在 [本阶段 PDF 日志目录](../logs/v0.2.3/pdf)。
- 当前状态：**编辑与最终视觉验收已通过；见下方证据。**

## 最终编辑与视觉验收结果

- [初次编辑日志](../logs/v0.2.3/20261010T233326_922813_pdf_annotate.log)保留真实失败：目标已写入后，统计旧批注数遇到间接对象取值错误；并非公式核对失败。修复统计后，[重试](../logs/v0.2.3/20261010T233406_456228_pdf_annotate_retry.log)识别同一计划已在 PDF 中，未重复画勾，退出 0。
- [独立重新打开、核对和渲染](../logs/v0.2.3/20261010T233406_716661_pdf_verify_render.log)，退出 0；[逐页视觉与像素核验](../logs/v0.2.3/20261010T233454_140775_pdf_visual_qa.log)，退出 0。
- [最终核验数据](../logs/v0.2.3/pdf/verification.json)：18 页不变；126 个旧批注/链接全部保留；新增 4 个红勾和 5 个图例/限定说明，当前共 135 个批注/链接。
- 修改页 1、7、8、10、11 均已查看最终渲染。红勾及中文可见，没有裁切、遮公式或遮旧批注；标记矩形之外的渲染像素与改前完全相同。其余 13 页内容流字节不变。原文可选文本逐页保留。
- 最终副本 SHA-256：`0735771fa5d38adc70a74f21be3c109b490d1c91587414f874ac0c2d049409be`。
- 使用已有 PDF 技能、pypdf/reportlab 叠加和 pdftoppm 渲染；未安装依赖，未修改原始 PDF/MD/TEX。

## 2026-10-11 注释变更说明

本次只为 LocalSpatial 的注释补充公式与页码，PDF 和红勾没有变动。历史标注计划中的源码 SHA-256 对应 [本次保留的修改前源码](../logs/v0.2.3/comments_20261011T211945/before_LocalSpatial.lean)，继续作为 2026-10-10 标注时的证据，不改写历史哈希。
[逐字比较](../logs/v0.2.3/comments_20261011T211945/comment_only_check.json)确认剔除注释后的 Lean 代码完全相同；[新构建](../logs/v0.2.3/20261011T212242_143462_comments_lake_build.log)和[新审计](../logs/v0.2.3/20261011T212322_994625_comments_axioms_audit.log)退出 0。定理范围、定义、假设、公理依赖和红勾范围均未变化。

同日进一步精简注释，PDF 与定理范围仍未变化；[当前源码核对](../logs/v0.2.3/comments_short_20261011T214308/check.json)和[构建及默认审计](../logs/v0.2.3/20261011T214335_015307_shortened_comments_build.log)保留，历史哈希不覆盖。

同日按阅读反馈补齐关键证明过渡，保持公式与简短实例；仅注释及一处换行改变。[最新源码核对](../logs/v0.2.3/comments_readable_20261011T214656/comment_only_check.json)和[实际构建及默认审计](../logs/v0.2.3/20261011T214957_195523_readable_comments_build.log)通过。PDF、定理和标注范围未变，以上记录作为历史保留。


## v0.3.2–v0.3.3：条件性能量律、图范数及重构控制（2026-10-13）

本节追加当前范围，保留上述历史和全部用户批注。当前指定副本为 18 页，原 150 项批注全部保留，新增 12 个带范围红勾、6 条说明，共 168 项批注。修改页实际页序与印刷页码均为 10、11、12、13。

构建与独立公理审计分别完成：

- v0.3.2：[构建](../logs/v0.3.2/20261013T095839_225389_lake_build.log)／[审计](../logs/v0.3.2/20261013T100104_046897_axioms_audit.log)，均退出 0，288 条公理输出。
- v0.3.3：[构建](../logs/v0.3.3/20261013T100156_159842_lake_build.log)／[审计](../logs/v0.3.3/20261013T100321_602582_axioms_audit.log)，均退出 0，316 条公理输出，包含全部旧声明与本轮 53 条新增正式定理。
- 仅标准 propext、Classical.choice、Quot.sound；无 sorryAx、自定义占位公理。28 项既有标注账目中的定理全部再次与当前审计核对。
- [来源版本复核](../logs/v0.3.3/pdf/source_review.md)记录 V7 原文、模型合同、锁文件未变及路线图入场差异。原始 md/tex/pdf 未修改。

标注中“条件性空间”表示实际 L²/加权空间上的定理已经证明，但一般 Green、迹、Poincaré 与时间交换仍需在具体矩形上兑现。定义和输入接口本身不打完成勾。

### graph-bound：(6.7)

- PDF 实际页序 **10**，印刷页码 **10**。
- 类型：条件性空间结论。本轮新增红勾：**是**；可见限定文字：“条件性图范数界 / Poincaré 接口”。
- 源码：[Coercivity.lean](../LeanPML/PML/Coercivity.lean)。
- 完整定理名：`LeanPML.PML.energy7_bounds_Conditional`、`LeanPML.PML.energy7_zero_Conditional`。
- 准确已证范围：实际同源两层能量与同一 graphSquare7 的精确 1/4、1 双边界；材料正性、原阈值、两层极化/空间约束及零迹 Poincaré 接口下成立，能量零则两层全部坐标零。
- 未完成接口：具体矩形 Poincaré、完整原 PDE 对应；不是裸八变量范数等价或单调性。
- 当前证据：[最终构建](../logs/v0.3.3/20261013T100156_159842_lake_build.log)、[独立审计](../logs/v0.3.3/20261013T100321_602582_axioms_audit.log)；源码 SHA-256 `0f7102688b3921fea128f8978874e4feea34cd3082b228c732f6019471d87e04`。

### physical-fields：(6.10)

- PDF 实际页序 **10**，印刷页码 **10**。
- 类型：条件性空间结论。本轮新增红勾：**是**；可见限定文字：“兼容重构下 / L² 控制”。
- 源码：[PhysicalControl.lean](../LeanPML/PML/PhysicalControl.lean)。
- 完整定理名：`LeanPML.PML.physicalControl_Conditional`。
- 准确已证范围：PhysicalControlBounds.physical：实际 L² 重构 E、H、P 的原常数控制 (4/μ)E7；由同源图界与材料条件推得。
- 未完成接口：原八变量 PDE 与 primitive 双向等价、提升唯一性。
- 当前证据：[最终构建](../logs/v0.3.3/20261013T100156_159842_lake_build.log)、[独立审计](../logs/v0.3.3/20261013T100321_602582_axioms_audit.log)；源码 SHA-256 `e20d6fd889b662f824c048a05f2408180b679b570efd788a27df8f19c49a4595`。

### single-balance：(7.6)，并使用 (7.7) 既有定义

- PDF 实际页序 **11**，印刷页码 **11**。
- 类型：条件性空间结论／真实时间求导。本轮新增红勾：**是**；可见限定文字：“条件性空间 / 能量恒等式 / Green/正则性 / 接口”。
- 源码：[BalanceAbstract.lean](../LeanPML/PML/BalanceAbstract.lean)。
- 完整定理名：`LeanPML.PML.hasDerivAt_fieldEnergy_boundary_Conditional`、`LeanPML.PML.hasDerivAt_fieldEnergy_zeroTrace_Conditional`。
- 准确已证范围：已有真实空间能量和耗散，从 StateHasDerivAt、primitive 主/辅助演化、兼容及空间导数关系与一般 Green 接口推出含边界 HasDerivAt；零迹下边界消失。
- 未完成接口：具体矩形域/Green/迹与正则性实例；不表示 D_c≥0。
- 当前证据：[最终构建](../logs/v0.3.3/20261013T100156_159842_lake_build.log)、[独立审计](../logs/v0.3.3/20261013T100321_602582_axioms_audit.log)；源码 SHA-256 `8adb3558e5e487befcb337791da05c8e16947fb10700a7c0ae126a7bbe099d3f`。

### two-balance：(7.8) 右侧真实两层能量恒等式

- PDF 实际页序 **12**，印刷页码 **12**。
- 类型：条件性空间结论／真实时间求导。本轮新增红勾：**是**；可见限定文字：“条件性两层 / 恒等式 / 需空间接口 / 未证耗散闭合”。
- 源码：[BalanceAbstract.lean](../LeanPML/PML/BalanceAbstract.lean)。
- 完整定理名：`LeanPML.PML.hasDerivAt_energy7_Conditional`。
- 准确已证范围：从 I 内原层 primitive 演化，经同源真实邻域求导推出导数层同系统，两层分别零迹，固定同一K，实际证明 HasDerivAt energy7 (-dissipation7) t，t∈interior I。
- 未完成接口：具体矩形 Green/迹/微分交换仍是接口；没有 D7≥0、积分平衡或时间单调性。
- 当前证据：[最终构建](../logs/v0.3.3/20261013T100156_159842_lake_build.log)、[独立审计](../logs/v0.3.3/20261013T100321_602582_axioms_audit.log)；源码 SHA-256 `8adb3558e5e487befcb337791da05c8e16947fb10700a7c0ae126a7bbe099d3f`。

### spatial-control：(8.3)

- PDF 实际页序 **12**，印刷页码 **12**。
- 类型：条件性空间结论。本轮新增红勾：**是**；可见限定文字：“空间约束下 / 梯度控制 / 函数控制需 / Poincaré 接口”。
- 源码：[Coercivity.lean](../LeanPML/PML/Coercivity.lean)。
- 完整定理名：`LeanPML.PML.gradient_square_le_spatialBudget`、`LeanPML.PML.state_norm_sq_le_spatialBudget`。
- 准确已证范围：实际加权零延拓与 Λ=∇v+ψ 推出梯度平方≤2B_sp；一般零迹 Poincaré 接口下进一步得到位移平方≤2CP²B_sp。
- 未完成接口：梯度和 Poincaré 的具体矩形实现；第二条不代表已经证明 Poincaré 本身。
- 当前证据：[最终构建](../logs/v0.3.3/20261013T100156_159842_lake_build.log)、[独立审计](../logs/v0.3.3/20261013T100321_602582_axioms_audit.log)；源码 SHA-256 `0f7102688b3921fea128f8978874e4feea34cd3082b228c732f6019471d87e04`。

### lower-bound：§8.1 末尾未编号 F_c≥N²/4

- PDF 实际页序 **12**，印刷页码 **12**。
- 类型：条件性空间结论。本轮新增红勾：**是**；可见限定文字：“条件性下界 / Poincaré 接口”。
- 源码：[Coercivity.lean](../LeanPML/PML/Coercivity.lean)。
- 完整定理名：`LeanPML.PML.fieldEnergy_bounds_Conditional`。
- 准确已证范围：由旧约束消元、原阈值推出系数界、实际可积密度 Young 估计与零迹 Poincaré 吸收，证明 N²/4≤F_c。
- 未完成接口：具体矩形 Poincaré；非任意独立点态矩阵正定。
- 当前证据：[最终构建](../logs/v0.3.3/20261013T100156_159842_lake_build.log)、[独立审计](../logs/v0.3.3/20261013T100321_602582_axioms_audit.log)；源码 SHA-256 `0f7102688b3921fea128f8978874e4feea34cd3082b228c732f6019471d87e04`。

### upper-bound：§8.2 末尾未编号 F_c≤N²

- PDF 实际页序 **13**，印刷页码 **13**。
- 类型：条件性空间结论。本轮新增红勾：**是**；可见限定文字：“条件性上界 / Poincaré 接口”。
- 源码：[Coercivity.lean](../LeanPML/PML/Coercivity.lean)。
- 完整定理名：`LeanPML.PML.fieldEnergy_bounds_Conditional`。
- 准确已证范围：同一能量/图平方的精确上界；使用原材料与阈值，保留零状态。原文末尾严格 <B_sp 在 B_sp=0 不成立，正式证明采用足够的非严格估计。
- 未完成接口：具体矩形 Poincaré。原文严格号未改动，疑点已记账。
- 当前证据：[最终构建](../logs/v0.3.3/20261013T100156_159842_lake_build.log)、[独立审计](../logs/v0.3.3/20261013T100321_602582_axioms_audit.log)；源码 SHA-256 `0f7102688b3921fea128f8978874e4feea34cd3082b228c732f6019471d87e04`。

### aux-u-phi：(8.4)

- PDF 实际页序 **13**，印刷页码 **13**。
- 类型：条件性空间结论。本轮新增红勾：**是**；可见限定文字：“兼容重构下 / L² 控制”。
- 源码：[PhysicalControl.lean](../LeanPML/PML/PhysicalControl.lean)。
- 完整定理名：`LeanPML.PML.physicalControl_Conditional`。
- 准确已证范围：PhysicalControlBounds.displacement、auxiliary：u 平方≤8CP²E7、物理φ平方和≤4E7。 从原材料阈值、受约束同源图界及实际L²有界乘子推得。
- 未完成接口：给定兼容提升的重构控制；完整原 PDE 等价及提升规范唯一性仍待完成。
- 当前证据：[最终构建](../logs/v0.3.3/20261013T100156_159842_lake_build.log)、[独立审计](../logs/v0.3.3/20261013T100321_602582_axioms_audit.log)；源码 SHA-256 `e20d6fd889b662f824c048a05f2408180b679b570efd788a27df8f19c49a4595`。

### aux-q：(8.5)

- PDF 实际页序 **13**，印刷页码 **13**。
- 类型：条件性空间结论。本轮新增红勾：**是**；可见限定文字：“兼容重构下 / L² 控制”。
- 源码：[PhysicalControl.lean](../LeanPML/PML/PhysicalControl.lean)。
- 完整定理名：`LeanPML.PML.physicalControl_Conditional`。
- 准确已证范围：PhysicalControlBounds.primitivePolar：实际 q=κu−τP，精确系数16κ²CP²+8κτ²/μ。 从原材料阈值、受约束同源图界及实际L²有界乘子推得。
- 未完成接口：给定兼容提升的重构控制；完整原 PDE 等价及提升规范唯一性仍待完成。
- 当前证据：[最终构建](../logs/v0.3.3/20261013T100156_159842_lake_build.log)、[独立审计](../logs/v0.3.3/20261013T100321_602582_axioms_audit.log)；源码 SHA-256 `e20d6fd889b662f824c048a05f2408180b679b570efd788a27df8f19c49a4595`。

### aux-z1：(8.6)

- PDF 实际页序 **13**，印刷页码 **13**。
- 类型：条件性空间结论。本轮新增红勾：**是**；可见限定文字：“兼容重构下 / L² 控制”。
- 源码：[PhysicalControl.lean](../LeanPML/PML/PhysicalControl.lean)。
- 完整定理名：`LeanPML.PML.physicalControl_Conditional`。
- 准确已证范围：PhysicalControlBounds.electricMemory：实际 Z1=−εbu，精确8ε²S⁴CP²E7。 从原材料阈值、受约束同源图界及实际L²有界乘子推得。
- 未完成接口：给定兼容提升的重构控制；完整原 PDE 等价及提升规范唯一性仍待完成。
- 当前证据：[最终构建](../logs/v0.3.3/20261013T100156_159842_lake_build.log)、[独立审计](../logs/v0.3.3/20261013T100321_602582_axioms_audit.log)；源码 SHA-256 `e20d6fd889b662f824c048a05f2408180b679b570efd788a27df8f19c49a4595`。

### aux-z2：(8.7)

- PDF 实际页序 **13**，印刷页码 **13**。
- 类型：条件性空间结论。本轮新增红勾：**是**；可见限定文字：“兼容重构下 / L² 控制”。
- 源码：[PhysicalControl.lean](../LeanPML/PML/PhysicalControl.lean)。
- 完整定理名：`LeanPML.PML.physicalControl_Conditional`。
- 准确已证范围：PhysicalControlBounds.polarMemory：实际 Z2=−bq，精确S⁴(16κ²CP²+8κτ²/μ)E7。 从原材料阈值、受约束同源图界及实际L²有界乘子推得。
- 未完成接口：给定兼容提升的重构控制；完整原 PDE 等价及提升规范唯一性仍待完成。
- 当前证据：[最终构建](../logs/v0.3.3/20261013T100156_159842_lake_build.log)、[独立审计](../logs/v0.3.3/20261013T100321_602582_axioms_audit.log)；源码 SHA-256 `e20d6fd889b662f824c048a05f2408180b679b570efd788a27df8f19c49a4595`。

### aux-qxy：(8.8)

- PDF 实际页序 **13**，印刷页码 **13**。
- 类型：条件性空间结论。本轮新增红勾：**是**；可见限定文字：“兼容重构下 / L² 控制”。
- 源码：[PhysicalControl.lean](../LeanPML/PML/PhysicalControl.lean)。
- 完整定理名：`LeanPML.PML.physicalControl_Conditional`。
- 准确已证范围：PhysicalControlBounds.magneticAuxiliary：Qx=pφy、Qy=−rφx，平方和≤4S²E7，方向与缩放正确。 从原材料阈值、受约束同源图界及实际L²有界乘子推得。
- 未完成接口：给定兼容提升的重构控制；完整原 PDE 等价及提升规范唯一性仍待完成。
- 当前证据：[最终构建](../logs/v0.3.3/20261013T100156_159842_lake_build.log)、[独立审计](../logs/v0.3.3/20261013T100321_602582_axioms_audit.log)；源码 SHA-256 `e20d6fd889b662f824c048a05f2408180b679b570efd788a27df8f19c49a4595`。


### 只作说明而不打证明勾

- 第 11 页 (7.5)：“Green 接口／具体矩形证明待完成”；一般接口输入不记为已证明具体 Green。
- 第 10–13 页顶部新增当前范围说明。第 11 页“积分待完成”、第 12 页“右式能量律仍待完成”等旧文字原样保留，顶部明确它们属于历史范围；当前新增勾只覆盖条件性定理。
- 第 13 页 §8.2：原文严格 `< B_sp` 在 B_sp=0 时不成立。说明实际 Lean 使用足够的非严格估计，并保留零状态与 1/4、1 原常数。
- (6.2)、(7.7) 定义并非因本轮重新获得完成勾。没有给 (6.8)–(6.9)、(9.5)–(9.7)、完整 D₇ 非负、最终单调性、矩形 PDE 主定理新增整体完成勾。
- 全部旧标记保留；本轮没有删除或重新定位原批注，也没有重复叠加同一 ID。

### 编辑保护、定位与验收

- [修改前备份](../logs/v0.3.3/pdf/before_v0.3.2-v0.3.3_20261013T100551.pdf)；[备份及哈希](../logs/v0.3.3/pdf/backup.json)。原哈希 `9b55183d444b9efa91e873dbbef1d7e73756962106f9c51d0de108f78b49c2ac`。

- [标注脚本](../logs/v0.3.3/pdf/annotate_pdf.py)、[定位及证据计划](../logs/v0.3.3/pdf/annotation_plan.json)、[定位预检](../logs/v0.3.3/pdf/coordinate_preflight.json)。红勾由矢量折线绘制；范围文字使用嵌入中文字体。稳定 ID 与计划哈希防止重复叠加；目标外部变化时停止写入。
- [实际 PDF 编辑日志](../logs/v0.3.3/20261013T100559_337529_pdf_annotate.log)、[渲染日志](../logs/v0.3.3/20261013T100607_874052_pdf_render.log)、[最终验证日志](../logs/v0.3.3/20261013T100735_806250_pdf_verify.log)。
- [结构/证据验收](../logs/v0.3.3/pdf/verification.json)、[逐页视觉检查](../logs/v0.3.3/pdf/visual_review.json)：重新打开副本，四页均以 Poppler 150 dpi 渲染并逐页检查，标记清晰、无限定文字裁切、无正文/公式/编号遮挡。原页序、页面框、可选文本以及未改页面提取文本保持。
- 最终 PDF SHA-256：`c9d5b114e9de7befb92e001ccc1486227acef27c8c0933fc688722eaf3ca44a3`。


## v0.3.4–v0.3.5：第 9 节与条件性有限区间结论（2026-10-13）

用途：把本轮实际证明、PDF 标记与真实构建证据逐项连接。以下是追加记录；上方所有标记及历史说明保留。两个阶段已分别通过验收，最终当前工程审计 369 条声明，没有 sorryAx，仅标准 propext、Classical.choice、Quot.sound。

条件性表示 Lean 证明了列明分析接口下的结论，不表示具体矩形 Green、迹、精确 Poincaré 常数及时间/空间微分交换已经证明。定理 6.1 的抽象分析核心已闭合；原八变量完整 PDE 对应、提升唯一性及解存在唯一性仍未完成。

### 本轮新增标记

实际页序与印刷页码一致。红勾只覆盖下表的结论；(9.2) 的定义另有文字说明，不作为已证明结论。

| 页序／印刷页 | 公式或定位 | 类型 | 红勾旁的可见限定文字 |
|---|---|---|---|
| 10／10 | (6.8) | 条件性空间结论 | ✓ 条件性；耗散闭合；精确剩余量 |
| 10／10 | (6.9) | 条件性空间结论 | ✓ 条件性单调；与积分平衡；闭区间版本 |
| 13／13 | (9.1) | 条件性空间结论 | ✓ 条件性；耗散下界；同源两层 |
| 14／14 | (9.2) 的可积性、非负性子结论 | 实际 L² 积分子结论 | ✓ J可积、非负；实际L²积分 |
| 14／14 | (9.3) | 条件性空间结论 | ✓ 空间约束下；积分估计；含零吸收区 |
| 14／14 | (9.4) | 条件性空间结论 | ✓ 原辅助演化；推出；需时间；空间交换接口 |
| 14／14 | (9.5) | 条件性空间结论 | ✓ 同源路径下；梯度估计；空间算子接口 |
| 14／14 | (9.6) | 条件性空间结论 | ✓ Poincaré；接口下的；吸收估计 |
| 14／14 | (9.7) | 条件性空间结论 | ✓ 真实Debye；导数关系下；吸收估计 |
| 14／14 | (9.7) 后未编号剩余耗散下界 | 条件性空间结论 | ✓ 条件性；耗散闭合；两类预算保留 |

#### 10 页：(6.8)

- Lean 文件：[DissipationClosure.lean](../LeanPML/PML/DissipationClosure.lean)。
- 完整定理：`LeanPML.PML.dissipation7_lower_Conditional`、`LeanPML.PML.dissipation7_nonneg_Conditional`。
- 准确范围与条件：(6.8) 的精确剩余耗散下界与非负性；原层演化、同源真实路径和共同迹 Poincaré 下，时间在内部。
- 剩余接口：具体矩形 Green、迹、精确 Poincaré 与时间/空间交换；完整原八变量 PDE 对应、提升唯一性与解存在唯一性。
- 本轮新增矢量红勾；稳定标记 ID `LeanPML.v0.3.5.main-dissipation`。
- 实际证据：[构建](../logs/v0.3.5/20261013T214810_766115_lake_build.log)／[独立公理审计](../logs/v0.3.5/20261013T214845_382134_axioms_audit.log)，退出码均为 0。当前最终复核还通过 v0.3.5 的完整导入和全部审计。

#### 10 页：(6.9)

- Lean 文件：[MainAbstract.lean](../LeanPML/PML/MainAbstract.lean)。
- 完整定理：`LeanPML.PML.energy7_antitoneOn_Conditional`、`LeanPML.PML.energy7_integral_balance_Conditional`、`LeanPML.PML.main_energy_estimate_Conditional`。
- 准确范围与条件：(6.9) 有限闭区间单调不增与真实时间积分平衡；两层分量闭区间连续和静态兼容，内部真实演化；积分平衡另需 second.R=P_tt 连续。
- 剩余接口：具体矩形 Green、迹、精确 Poincaré 与时间/空间交换；完整原八变量 PDE 对应、提升唯一性与解存在唯一性。
- 本轮新增矢量红勾；稳定标记 ID `LeanPML.v0.3.5.main-balance`。
- 实际证据：[构建](../logs/v0.3.5/20261013T214810_766115_lake_build.log)／[独立公理审计](../logs/v0.3.5/20261013T214845_382134_axioms_audit.log)，退出码均为 0。当前最终复核还通过 v0.3.5 的完整导入和全部审计。

#### 13 页：(9.1)

- Lean 文件：[DissipationClosure.lean](../LeanPML/PML/DissipationClosure.lean)。
- 完整定理：`LeanPML.PML.fieldDissipation_lower`、`LeanPML.PML.debye_relations_Conditional`、`LeanPML.PML.dissipation7_preliminary_Conditional`。
- 准确范围与条件：由实际场单层余项积分与真实兼容求导，得到 (9.1)，保留两项负项；未把单层耗散非负作为输入。
- 剩余接口：具体矩形 Green、迹、精确 Poincaré 与时间/空间交换；完整原八变量 PDE 对应、提升唯一性与解存在唯一性。
- 本轮新增矢量红勾；稳定标记 ID `LeanPML.v0.3.5.preliminary`。
- 实际证据：[构建](../logs/v0.3.5/20261013T214810_766115_lake_build.log)／[独立公理审计](../logs/v0.3.5/20261013T214845_382134_axioms_audit.log)，退出码均为 0。当前最终复核还通过 v0.3.5 的完整导入和全部审计。

#### 14 页：(9.2) 的可积性、非负性子结论

- Lean 文件：[GradientControl.lean](../LeanPML/PML/GradientControl.lean)。
- 完整定理：`LeanPML.PML.fieldJ_integrable`、`LeanPML.PML.fieldJ_eq_integral`、`LeanPML.PML.fieldJ_nonneg`、`LeanPML.PML.fieldJDensity_zero_region`。
- 准确范围与条件：实际 L² 与有界 θ 系数下，J 密度可积、内积/积分相等且非负；零区密度为两个梯度表达分量平方和。红勾不表示定义本身是证明。
- 剩余接口：具体矩形 Green、迹、精确 Poincaré 与时间/空间交换；完整原八变量 PDE 对应、提升唯一性与解存在唯一性。
- 本轮新增矢量红勾；稳定标记 ID `LeanPML.v0.3.5.j-analysis`。
- 实际证据：[构建](../logs/v0.3.4/20261013T214336_169080_lake_build.log)／[独立公理审计](../logs/v0.3.4/20261013T214424_960799_axioms_audit.log)，退出码均为 0。当前最终复核还通过 v0.3.5 的完整导入和全部审计。

#### 14 页：(9.3)

- Lean 文件：[GradientControl.lean](../LeanPML/PML/GradientControl.lean)。
- 完整定理：`LeanPML.PML.fieldSpatialDissipation_ge_J`。
- 准确范围与条件：(9.3) 的两个实际积分下界；非负吸收和幅度限制，空间表达 h=Λ−ψ，零区恢复 ψ=0。
- 剩余接口：具体矩形 Green、迹、精确 Poincaré 与时间/空间交换；完整原八变量 PDE 对应、提升唯一性与解存在唯一性。
- 本轮新增矢量红勾；稳定标记 ID `LeanPML.v0.3.5.spatial-j`。
- 实际证据：[构建](../logs/v0.3.4/20261013T214336_169080_lake_build.log)／[独立公理审计](../logs/v0.3.4/20261013T214424_960799_axioms_audit.log)，退出码均为 0。当前最终复核还通过 v0.3.5 的完整导入和全部审计。

#### 14 页：(9.4)

- Lean 文件：[GradientControl.lean](../LeanPML/PML/GradientControl.lean)。
- 完整定理：`LeanPML.PML.gradient_evolution_Conditional`。
- 准确范围与条件：(9.4) 从原层辅助演化和同源真实导数推出；依赖受限梯度域、空间约束及沿路径时间交换接口。
- 剩余接口：具体矩形 Green、迹、精确 Poincaré 与时间/空间交换；完整原八变量 PDE 对应、提升唯一性与解存在唯一性。
- 本轮新增矢量红勾；稳定标记 ID `LeanPML.v0.3.5.gradient-evolution`。
- 实际证据：[构建](../logs/v0.3.4/20261013T214336_169080_lake_build.log)／[独立公理审计](../logs/v0.3.4/20261013T214424_960799_axioms_audit.log)，退出码均为 0。当前最终复核还通过 v0.3.5 的完整导入和全部审计。

#### 14 页：(9.5)

- Lean 文件：[GradientControl.lean](../LeanPML/PML/GradientControl.lean)。
- 完整定理：`LeanPML.PML.field_gradient_control`、`LeanPML.PML.gradient_control_Conditional`。
- 准确范围与条件：(9.5) 从 (9.4)、θ 的两种系数估计和三项平方估计，经合法实际 L² 积分得到；覆盖零区、双边层和角层。
- 剩余接口：具体矩形 Green、迹、精确 Poincaré 与时间/空间交换；完整原八变量 PDE 对应、提升唯一性与解存在唯一性。
- 本轮新增矢量红勾；稳定标记 ID `LeanPML.v0.3.5.gradient-control`。
- 实际证据：[构建](../logs/v0.3.4/20261013T214336_169080_lake_build.log)／[独立公理审计](../logs/v0.3.4/20261013T214424_960799_axioms_audit.log)，退出码均为 0。当前最终复核还通过 v0.3.5 的完整导入和全部审计。

#### 14 页：(9.6)

- Lean 文件：[DissipationClosure.lean](../LeanPML/PML/DissipationClosure.lean)。
- 完整定理：`LeanPML.PML.scale_amplitude_chain`、`LeanPML.PML.spatial_absorption_Conditional`、`LeanPML.PML.spatial_absorption_half_Conditional`。
- 准确范围与条件：(9.6) 由共同迹核的 Poincaré、(9.3)、(9.5) 与原阈值推出；非空空间载体仅用于从0≤p≤S取得S≥0。
- 剩余接口：具体矩形 Green、迹、精确 Poincaré 与时间/空间交换；完整原八变量 PDE 对应、提升唯一性与解存在唯一性。
- 本轮新增矢量红勾；稳定标记 ID `LeanPML.v0.3.5.spatial-absorption`。
- 实际证据：[构建](../logs/v0.3.5/20261013T214810_766115_lake_build.log)／[独立公理审计](../logs/v0.3.5/20261013T214845_382134_axioms_audit.log)，退出码均为 0。当前最终复核还通过 v0.3.5 的完整导入和全部审计。

#### 14 页：(9.7)

- Lean 文件：[DissipationClosure.lean](../LeanPML/PML/DissipationClosure.lean)。
- 完整定理：`LeanPML.PML.debye_relations_Conditional`、`LeanPML.PML.debye_absorption_split`、`LeanPML.PML.debye_absorption_Conditional`。
- 准确范围与条件：(9.7) 由邻域兼容的两次真实求导得到 κ E_t=P_t+τP_tt，再从原阈值的两条材料条件分别吸收。
- 剩余接口：具体矩形 Green、迹、精确 Poincaré 与时间/空间交换；完整原八变量 PDE 对应、提升唯一性与解存在唯一性。
- 本轮新增矢量红勾；稳定标记 ID `LeanPML.v0.3.5.debye-absorption`。
- 实际证据：[构建](../logs/v0.3.5/20261013T214810_766115_lake_build.log)／[独立公理审计](../logs/v0.3.5/20261013T214845_382134_axioms_audit.log)，退出码均为 0。当前最终复核还通过 v0.3.5 的完整导入和全部审计。

#### 14 页：(9.7) 后未编号剩余耗散下界

- Lean 文件：[DissipationClosure.lean](../LeanPML/PML/DissipationClosure.lean)。
- 完整定理：`LeanPML.PML.dissipation7_lower_Conditional`、`LeanPML.PML.dissipation7_nonneg_Conditional`。
- 准确范围与条件：同时扣除不同负项，保留空间耗散1/2与 μτ/(4κ) 的 Debye 平方预算；不是重复使用同一正项。
- 剩余接口：具体矩形 Green、迹、精确 Poincaré 与时间/空间交换；完整原八变量 PDE 对应、提升唯一性与解存在唯一性。
- 本轮新增矢量红勾；稳定标记 ID `LeanPML.v0.3.5.remainder-budget`。
- 实际证据：[构建](../logs/v0.3.5/20261013T214810_766115_lake_build.log)／[独立公理审计](../logs/v0.3.5/20261013T214845_382134_axioms_audit.log)，退出码均为 0。当前最终复核还通过 v0.3.5 的完整导入和全部审计。

### 时间范围及未勾选结论

能量导数、(9.4)–(9.7) 同源估计及精确定量耗散下界作用于开时间区间 (0,T)。闭区间 [0,T] 的静态约束与实际场连续性另行输入，得到静态双边界、能量非负、单调性、初值控制。积分平衡额外需要真实导数层 second.R=P_tt 的 L² 闭区间连续性。允许 T=0、t₁=t₂ 和两个端点，不要求端点普通双侧导数，也不由 T=0 的空内部条件推导端点耗散正性。

本轮没有给具体矩形 Green/Poincaré、实际微分交换、完整 PDE 对应或解存在唯一性加完成勾。定义/假设本身没有完成勾；单调不增不代表严格递减。

### 旧标记与保护

第 10、12、13 页保留旧阶段“耗散/单调性待完成”等文字，新增页首说明其历史属性及当前条件性范围；第 14 页保留旧 θ 性质和 KS² 系数代数红勾，不重复叠加。第 14 页另加“J定义已录入；另证可积非负”及条件性图例。本輪不删除或重写用户批注。

入场 18 页、168 项批注，最终 18 页、183 项批注，新增 10 个红勾和 5 条说明。旧页框、可选正文与旧批注保持；其余 14 页可选文本完全相同。修改页均经 Poppler 150 dpi 渲染并逐页检查：可见、对应准确、无覆盖正文/编号、无缺字及裁切。

- [阶段时间备份](../logs/v0.3.5/pdf/before_v0.3.4-v0.3.5_20261013T214901.pdf)。
- 修改前 SHA-256：`c9d5b114e9de7befb92e001ccc1486227acef27c8c0933fc688722eaf3ca44a3`；修改后：`66c0f5dd32a1a983412a08eea40e3cd5d890f3dd987dbfe7e2bb4c7a5ddce1b3`。
- [备份信息](../logs/v0.3.5/pdf/backup.json)、[证据/定位计划](../logs/v0.3.5/pdf/annotation_plan.json)、[坐标预检](../logs/v0.3.5/pdf/coordinate_preflight.json)。
- [结构与证据验收](../logs/v0.3.5/pdf/verification.json)、[逐页视觉验收](../logs/v0.3.5/pdf/visual_review.json)。
- [标注脚本](../logs/v0.3.5/pdf/annotate_pdf.py)使用独立阶段 ID 和计划哈希，完全相同计划重跑直接跳过；目标发生外部修改时停止，不覆盖新批注。
- [编辑日志](../logs/v0.3.5/20261013T214910_164598_pdf_annotate.log)、[渲染日志](../logs/v0.3.5/20261013T214930_701266_pdf_render.log)、[最终复核日志](../logs/v0.3.5/20261013T215008_802109_pdf_verify.log)。
- [最终目标 PDF](../../results/V7_Maxwell_Debye_PML/V7_global_energy_副本.pdf)。原始 V7 md/tex/pdf、路线图、模型合同和依赖锁文件哈希全部保持。


## v0.4：光滑矩形接口与完整场层映射的增量标注

本轮在最终全工程构建、公理审计与定理类型核验之后，只编辑指定副本。四子阶段分别完成；不是 v0.5 最终具体能量定理的发布。旧批注全部保留，旧“点态/待完成”作为历史范围，新标记明确覆盖本轮的所选光滑类。

- 实际页序与印刷页码均为 3、4、7、8、10、11；总页数保持18。
- 原183个批注/链接完整保留，新增8个矢量红勾及4条无勾说明，总195个批注；无原文文字、页序、MediaBox/CropBox变化。
- 本轮 C_P=2L_x 是已证保守常数，K=32μ(ε+2κ)L_x²，阈值同步该常数；原 (5.1) 的精确 π 常数不打完成勾。
- 技术全空间/全时间光滑延拓、C(K)一致范数和加权成员/路径正则性强于 V7 弱类；原PDE仍仅在(0,T)×Ω。未证明加权传播、弱Green、提升规范唯一性、解存在唯一性。

实际证据：[最终构建](../logs/v0.4.4/20261013T230822_044824_lake_build.log) / [完整公理审计](../logs/v0.4.4/20261013T231144_117778_axioms_audit.log)；另有[定理类型输出](../logs/v0.4.4/20261013T231145_231939_interface_types.log)与[独立语义检查](../logs/v0.4.4/semantic_review_geometry.md)。

| 实际页/印刷页 | 定位 | 类型与本轮标记 | Lean完整声明名和源码 | 已证范围及剩余接口 |
|---|---|---|---|---|
| 3/3 | (2.1) | 真实光滑场方程对应；✓ 光滑 primitive；重构核验；八条方程 | `LeanPML.PML.Concrete.original_reconstruct_at`<br>`LeanPML.PML.Concrete.primitive_to_original_rectangle`<br>[Equivalence.lean](../LeanPML/PML/Equivalence.lean) | 八条方程为原解输入；勾仅表示从光滑 primitive 重构的满足性，非解存在。 |
| 4/4 | (2.3) | 真实历史/时间及L²积分；✓ 历史提升；初值与求导 | `LeanPML.PML.Concrete.integralLift_initial`<br>`LeanPML.PML.Concrete.hasDerivAt_integralLift`<br>`LeanPML.Rectangle.toL2_integralLift_on_Icc`<br>[OriginalSystem.lean](../LeanPML/PML/OriginalSystem.lean) / [HistoryL2.lean](../LeanPML/Rectangle/HistoryL2.lean) | 真实点态时间积分初值、内部求导；C(K) 连续正则性下与 L² Bochner 历史积分相等。定义本身不计证明。 |
| 4/4 | (2.4) | 真实场时间保持；✓ 五个时间；不变量；光滑场版 | `LeanPML.PML.Concrete.five_invariants_on_Icc`<br>`LeanPML.PML.Concrete.five_invariants_toLp_eq_of_continuous`<br>[Equivalence.lean](../LeanPML/PML/Equivalence.lean) | 从原八式、真实历史提升及混合微分推出任意初始不变量场的保持；实际 L² 表示一致。旧三个点态批注保留。 |
| 4/4 | (2.5) | 初始兼容保持/场重构；✓ 初始兼容；保持与重构；光滑场版 | `LeanPML.PML.Concrete.compatible_lift_on_Icc`<br>`LeanPML.PML.Concrete.reconstruct_lift_eqOn`<br>[Equivalence.lean](../LeanPML/PML/Equivalence.lean) | 仅初始五不变量为零作输入，推出全区间兼容及四辅助量重构；不是零解。 |
| 4/4 | (2.6)、命题 2.1 | 光滑场双向对应；✓ 双向八方程；光滑类；固定初始；原函数 | `LeanPML.PML.Concrete.original_to_primitive_rectangle`<br>`LeanPML.PML.Concrete.primitive_to_original_rectangle`<br>`LeanPML.PML.Concrete.lift_reconstruct_eqOn`<br>[Equivalence.lean](../LeanPML/PML/Equivalence.lean) | 所选光滑类，固定初始原函数；包含反向四辅助方程。无解存在唯一性或提升规范唯一性结论。 |
| 7/7 | (5.1) | 具体空间不等式；保守常数说明；无勾：v0.4 保守版；C_P = 2Lx；非原精确值 | `LeanPML.Rectangle.poincare_estimate`<br>`LeanPML.Rectangle.scaleK_rectangle`<br>[Poincare.lean](../LeanPML/Rectangle/Poincare.lean) | 已证明同一迹核上的 CP=2Lx，从而 K=32μ(ε+2κ)Lx²；未证明原文精确 π 常数，无完成勾。 |
| 8/8 | §5.2 五不变量保持段后的零区保持（未编号） | 真实原場时间保持；✓ 原场零区；保持；须初始φ=0 | `LeanPML.PML.Concrete.original_zero_region_preserved`<br>[Equivalence.lean](../LeanPML/PML/Equivalence.lean) | 从原方程、历史提升、五初始兼容及零区 φ₀=0 推出 φ=0；保留一般空间区域，不声称(5.7)/(5.8)传播。 |
| 10/10 | (6.6) | 正则性输入；无勾说明；无勾：v0.4 输入；光滑/加权；正则性；非自动传播 | `LeanPML.Rectangle.hasDerivAt_toL2_of_pointwise`<br>`LeanPML.Rectangle.hasDerivAt_weighted_smooth`<br>[L2Paths.lean](../LeanPML/Rectangle/L2Paths.lean) / [WeightedCalculus.lean](../LeanPML/PML/WeightedCalculus.lean) | 选用 C∞ 空间延拓、C(K) 的统一时间正则性及实际加权路径可微作为强于 V7 弱类的条件；已证明到普通/加权路径导数的连接。假设不打勾。 |
| 11/11 | (7.2) 后加权链式法则说明（未编号） | 真实加权时间求导；✓ 加权路径；真实场恢复；需加权可导 | `LeanPML.Rectangle.weighted_smooth_recovery`<br>`LeanPML.Rectangle.hasDerivAt_weighted_smooth`<br>[WeightedCalculus.lean](../LeanPML/PML/WeightedCalculus.lean) | 实际加权坐标恢复为所选光滑辅助场，普通 L² 导数由真实 C(K) 路径识别；加权范数正则性仍是输入，非自动传播。 |
| 11/11 | (7.5) | 具体光滑空间/边界结论；✓ 矩形光滑；四边 Green；两层 PEC；边界消去 | `LeanPML.Rectangle.green_L2`<br>`LeanPML.Rectangle.greenDomain`<br>`LeanPML.Rectangle.boundary_multiplier_zero`<br>`LeanPML.Rectangle.twoLayer_zeroBoundary`<br>[Green.lean](../LeanPML/Rectangle/Green.lean) / [BoundaryTime.lean](../LeanPML/Rectangle/BoundaryTime.lean) | 真实全矩形四边公式，右−左+上−下；u₀零迹+PEC推出u迹，内部真实求导推出E_t迹。另要求闭端点E_t迹时，T=0须初始导数迹。弱H₀¹–H(div) Green未证明。 |

以上定理均在正式 LeanPML 导入链和最终 Audit 中；可从PDF红字范围区域打开批注，查看完整声明名及证据。仅作为方程/定义输入的 (2.1)、(2.2)、(2.3)、(6.6) 不因此得到无条件证明；(2.1) 勾只表示重构满足八式，(2.3) 勾只表示实际积分初值与求导。

旧范围核对：第4页原 CD/CZ1/CZ2 点态勾保留，由新“五个光滑场版”补全本轮范围；第8页原零区点态标记保留，新增原场保持。第11页旧“Green具体矩形证明待完成”保留，页顶新增“光滑矩形已接通，弱空间未完成”说明。第10页既有 (6.7)–(6.10) 仍为条件性结果；本轮只在(6.6)旁说明强正则性输入。第7页旧CP自由参数的历史系数标记保留，新注明确本轮CP实例化。未给 (5.7)/(5.8)、弱空间、规范唯一性、适定性、严格衰减或完美匹配增加勾。

两层迹的准确时间范围：u的闭区间迹来自u₀迹+真实历史+PEC；E是PEC输入；E_t在内部由真实求导得到。若另要求闭区间E_t迹，T>0通过连续延拓，T=0必须给初始导数迹条件。有限区间主框架仅需内部E_t迹，不能用空内部方程推出端点事实。

原场八槽往返恢复在闭区间；底层 primitive 八槽往返在开区间，历史u/q在闭区间。最高光滑原系统装配另已证明闭区间静态约束。固定初始原函数的历史构造不等于提升规范唯一性。

修改前SHA256：`66c0f5dd32a1a983412a08eea40e3cd5d890f3dd987dbfe7e2bb4c7a5ddce1b3`；最终SHA256：`9021fff043b09278fd918dc4ef0342a0295e3aa7941e52825f59a286fd71a8f3`。

记录：[备份与哈希](../logs/v0.4.4/pdf/backup.json)、[定位/源码/定理计划](../logs/v0.4.4/pdf/annotation_plan.json)、[标注脚本](../logs/v0.4.4/pdf/annotate_pdf.py)、[结构检查](../logs/v0.4.4/pdf/annotation_result.json)、[逐页视觉验收](../logs/v0.4.4/pdf/visual_review.json)。稳定ID确保重跑不叠加；脚本校验输入哈希，不会覆盖别人的后续批注。

## 2026-10-14：v0.4 对齐修复标注追加

本轮只追加；旧195个批注全部保持，原文/页序/版框不变。最终18页，增加5项，其中1个矢量红勾，其余为限定说明。编辑前备份及哈希见 [backup](../logs/v0.4_alignment/pdf/backup.json)，首次版式预检失败的备份信息另存 [attempt01](../logs/v0.4_alignment/pdf/attempt01_backup.json)。

构建证据：[lake build](../logs/v0.4_alignment/20261014T000055_917026_lake_build.log)；公理审计：[Audit](../logs/v0.4_alignment/20261014T000341_178705_axioms_audit.log)；类型/假设复核：[实际类型](../logs/v0.4_alignment/20261014T000341_178709_interface_types.log)、[独立审查](../logs/v0.4_alignment/semantic_review.md)。结构及逐页视觉检查通过：[检查](../logs/v0.4_alignment/pdf/annotation_result.json)、[视觉](../logs/v0.4_alignment/pdf/visual_review.json)。

| 实际/印刷页 | 公式或定位 | 类型/新增标记 | 完整声明与文件 | 准确范围及剩余接口 |
|---|---|---|---|---|
| 3/3 | (2.1)：旧光滑重构核验的接口限定 | 说明，无新勾：v0.4 对齐：古典包装显式给出 E、Hx、Hy 的空间可导证据；八方程输入本身不保证空间光滑。 | `LeanPML.PML.Concrete.originalClassicalOn_of_liftIdentified`<br>`LeanPML.PML.Concrete.primitive_to_original_classical_rectangle`<br>[ClassicalSystem.lean](../LeanPML/PML/ClassicalSystem.lean) | 原式定义不打新勾。旧高层的光滑代表原已成立，本次正式推出空间DifferentiableAt及坐标HasDerivAt，并给带PEC反向古典包装；不是认为底层fderiv等式自动可导。 |
| 4/4 | (2.6)、命题2.1：旧双向光滑标注补充 | 说明，无新勾：对齐补充：古典双向映射已显式携带真实空间可导；仅所选强光滑类，非完整弱解理论。 | `LeanPML.PML.Concrete.original_to_primitive_classical_rectangle`<br>`LeanPML.PML.Concrete.primitive_to_original_classical_rectangle`<br>`LeanPML.Rectangle.RegionalAbsorption.originalRegionalFiniteIntervalProblem`<br>[ClassicalSystem.lean](../LeanPML/PML/ClassicalSystem.lean)<br>[RegionalCoefficients.lean](../LeanPML/Rectangle/RegionalCoefficients.lean) | 现有红勾保留。准确包装同时携带原E/H与primitive u/E/Λ可导；推荐入口由光滑识别及μ非零生成空间证据，域内改写原系数，实际调用古典链。初值、PEC、强正则性仍需声明；未发布v0.5主定理。 |
| 7/7 | (5.2)–(5.3)：物理幅度域范围 | 说明，无新勾：对齐：幅度界 / 仅闭坐标区间 / 域外截回代表 / 积分 a.e. 一致 | `LeanPML.Rectangle.RegionalAbsorption.coefficients_eq_closed`<br>`LeanPML.Rectangle.RegionalAbsorption.coefficients_ae`<br>`LeanPML.Rectangle.RegionalAbsorption.weighted_memLp_iff`<br>`LeanPML.Rectangle.RegionalAbsorption.fieldEnergy_eq_regional_integral`<br>`LeanPML.Rectangle.RegionalAbsorption.fieldDissipation_eq_regional_integral`<br>[RegionalCoefficients.lean](../LeanPML/Rectangle/RegionalCoefficients.lean) | 假设范围说明，不给假设打完成勾。原p/r非负/幅度仅Icc坐标区间；内部截回代表与原场在闭矩形和体积分a.e.一致，权重/成员/能量耗散可积积分正式连接。保留全零、边层、角层，原技术延拓不需域外物理幅度界。 |
| 15/15 | §10参数例旁的本轮替代证书（原文未单列） | ✓ 对齐证书：C_P=4，K=384；c=1/16384，S=1/65536（保守 C_P=2Lx）。 | `LeanPML.Rectangle.ParameterCertificate.unitSquare_parameter_certificate`<br>`LeanPML.Rectangle.ParameterCertificate.unitSquare_explicit_smallness`<br>`LeanPML.Rectangle.ParameterCertificate.unitSquare_le_threshold`<br>[ParameterCertificate.lean](../LeanPML/Rectangle/ParameterCertificate.lean) | 只对本轮实际(-1,1)^2及ε=κ=τ=μ=1参数证书打勾：CP4、A3、K384；三条显式界依次3/2097152、9/16、3/2048≤1，并调用阈值等价。不是原(10.1)/(10.2)配置完成勾，不含二维剖面、初值族或解存在。 |
| 15/15 | (10.1)旧例与保守常数的区别 | 说明，无新勾：原(10.1)未沿用：在 K=384 下，旧 c=1/128 使 8cAK=72>1；这不否定原精确π常数例。 | `LeanPML.Rectangle.ParameterCertificate.oldC_material_condition_value`<br>`LeanPML.Rectangle.ParameterCertificate.oldC_not_le_threshold`<br>[ParameterCertificate.lean](../LeanPML/Rectangle/ParameterCertificate.lean) | 正式反证说明旧c不能迁移至本轮保守CP。保留原论文配置与全部原批注；原(5.1)精确π常数仍未证明。 |

修改前SHA256：`9021fff043b09278fd918dc4ef0342a0295e3aa7941e52825f59a286fd71a8f3`；修改后：`b7cff33c435944c4c24bf5327246015523368c7015e3b6fb6b65348f8fc5819d`。定位与稳定ID见 [annotation_plan](../logs/v0.4_alignment/pdf/annotation_plan.json)，重跑会识别同ID而不叠加。原第3/4页红勾的低层引用范围容易被理解为方程自带空间可导，本轮追加古典包装声明，未删除旧记录。第7页保留“CP=2Lx非原精确值”；第15页新勾明确属于替代证书，不标原数值例完成。第10页既有“光滑/加权输入、非自动传播”说明仍准确，无新结论可勾，故只更新代码/账本说明。

本轮没有给v0.5具体主定理、精确π常数、弱理论、传播、提升唯一性或解存在唯一性增加完成标记。

---

## 2026-10-14：v0.5 光滑具体定理、数据与范围回归

本轮只修改指定副本；18页与200条旧批注保持，新增8条批注（6个矢量红勾、2条范围说明），最终208条。实际页序与印刷页码均一致。每条标记通过当前正式导入、源码哈希、构建及审计核对后添加。

| 页序 / 印刷页 | 公式或定位 / 类别 | Lean文件与完整声明 | 已证准确范围、输入及剩余接口 | 本轮旁注 |
|---|---|---|---|---|
| 5 / 5 | §2.3 命题2.2与H=t∇ψ未编号公式<br>类别：实际古典场、空间积分与范围反例<br>✓ 已证结论（具体光滑范围） | [UnrestrictedData.lean](../LeanPML/PML/Obstructions/UnrestrictedData.lean)<br>`LeanPML.PML.Obstructions.fullProfile_unrestricted_classical`<br>`LeanPML.PML.Obstructions.fullProfile_unrestricted_norm_growth`<br>`LeanPML.PML.Obstructions.fullProfile_unrestricted_not_compatible`<br>`LeanPML.PML.Obstructions.fullProfile_unrestricted_unbounded`<br>`LeanPML.PML.Obstructions.fullProfile_unrestricted_no_coercive_antitone_energy` | 实际完整双向剖面、物理区C∞紧支ψ及正梯度平方积分；同一全未来H=t∇ψ场八式/PEC通过，磁L²=t²G，任意历史初值不能修复Cx。只排除固定正磁控制+有限初值+全未来单调这组能量条件。不是兼容类反例，也不否定所有能量。 | v0.5：完整增长场、八式/PEC及真实L²增长已核验；初始磁辅助不兼容。 |
| 8 / 8 | §5.2数据类的§11.1启动子族<br>类别：初始场证书、真实初始导数与空间成员；非区间解<br>✓ 已证结论（具体光滑范围） | [CompatibleData.lean](../LeanPML/Examples/CompatibleData.lean)<br>[FullDomainProfile.lean](../LeanPML/Examples/FullDomainProfile.lean)<br>`LeanPML.Examples.CompatibleData.physical_data_certificate`<br>`LeanPML.Examples.CompatibleData.physical_initial_traces`<br>`LeanPML.Examples.CompatibleData.initial_derivatives`<br>`LeanPML.Examples.CompatibleData.initialGraphSquare_formula` | 实际f紧支于[-1/4,1/4]²，L²非零；u0=0 E0=P0=f q0=-f H/原aux0，八条原方程只在t=0核验，五初始兼容、三迹、零区、真实加权成员及正有限图平方。时间延拓不是区间PDE解；非一般解存在或加权传播。只覆盖这个启动子族，不替代所有§5.2一般数据。 | v0.5：非零紧支兼容数据子族；初始八式、迹与有限图数据已核验，非存在性。 |
| 10 / 10 | 定理6.1及(6.7)–(6.10)<br>类别：具体光滑原模型先验定理<br>✓ 已证结论（具体光滑范围） | [MainSmoothRectangle.lean](../LeanPML/PML/MainSmoothRectangle.lean)<br>`LeanPML.PML.SmoothRectangle.main_energy_estimate_smoothRectangle`<br>`LeanPML.PML.SmoothRectangle.SmoothCompatibleSolution.energy_graph_bounds`<br>`LeanPML.PML.SmoothRectangle.SmoothCompatibleSolution.energy_law_and_closure`<br>`LeanPML.PML.SmoothRectangle.SmoothCompatibleSolution.energy_antitone`<br>`LeanPML.PML.SmoothRectangle.SmoothCompatibleSolution.energy_integral_balance`<br>`LeanPML.PML.SmoothRectangle.SmoothCompatibleSolution.physical_current_bound`<br>`LeanPML.PML.SmoothRectangle.SmoothCompatibleSolution.energy_eq_original_integrals` | 从原八变量、只在Ioo×整个矩形的真实原方程、PEC、材料/区域界、初始兼容及已列强光滑/普通/加权正则性构造具体问题。原p/r实际积分、graph/4≤E≤graph、准确闭合、antitone、FTC平衡及输入原E/H/P L²控制均通过。CP=2Lx，不是原精确π常数或完整弱V7；不附带存在唯一或严格衰减。T0必要图初始条件明确保留。 | v0.5：(6.7)–(6.10) 矩形光滑兼容类已证；保守 C_P=2Lx，强正则性输入。 |
| 11 / 11 | (7.5)已证矩形Green在原场入口的使用<br>类别：已证具体分析接口的调用说明<br>接口使用范围说明；无新勾 | [Green.lean](../LeanPML/Rectangle/Green.lean)<br>[MainSmoothRectangle.lean](../LeanPML/PML/MainSmoothRectangle.lean)<br>`LeanPML.Rectangle.green_L2`<br>`LeanPML.Rectangle.greenDomain`<br>`LeanPML.PML.SmoothRectangle.SmoothCompatibleSolution.problem`<br>`LeanPML.PML.SmoothRectangle.SmoothCompatibleSolution.energy_law_and_closure` | 说明已存在的真实矩形光滑Green及两层边界消去在具体主定理链内调用；不重复叠加旧完成勾，不把输入PEC或弱Green理论标为证明成果。 | v0.5：原场总装使用已证矩形 Green/两层 PEC；(7.5) 旧光滑勾保留，弱范围未扩展。 |
| 12 / 12 | (7.6)–(7.8)能量律的具体总装<br>类别：实际L²/加权空间值时间求导<br>✓ 已证结论（具体光滑范围） | [MainSmoothRectangle.lean](../LeanPML/PML/MainSmoothRectangle.lean)<br>[BalanceAbstract.lean](../LeanPML/PML/BalanceAbstract.lean)<br>`LeanPML.PML.SmoothRectangle.SmoothCompatibleSolution.energy_law_and_closure`<br>`LeanPML.PML.hasDerivAt_energy7_Conditional` | 同一原场的历史与导数层，通过已经实例化的G/path/regular和原层演化调用两层真实HasDerivAt。κ非零来自正材料；不是把目标能量恒等式当输入。此范围为所选强正则类，CP仍保守；完整弱解传播未完成。 | v0.5：(7.8) 已由原模型光滑兼容路径推出；同源导数层与两层边界已接通。 |
| 14 / 14 | (9.5)–(9.7)既有估计的具体实例化<br>类别：既有空间估计与真实导数的具体接入说明<br>接口使用范围说明；无新勾 | [GradientControl.lean](../LeanPML/PML/GradientControl.lean)<br>[DissipationClosure.lean](../LeanPML/PML/DissipationClosure.lean)<br>[MainSmoothRectangle.lean](../LeanPML/PML/MainSmoothRectangle.lean)<br>`LeanPML.PML.gradient_control_Conditional`<br>`LeanPML.PML.spatial_absorption_Conditional`<br>`LeanPML.PML.debye_absorption_Conditional`<br>`LeanPML.PML.SmoothRectangle.SmoothCompatibleSolution.energy_law_and_closure` | 逐段核对调用链：energy_law_and_closure→dissipation7_lower→spatial_absorption_half→spatial_absorption→gradient_control，并调用debye_absorption。G是真Green，estimate是真保守Poincare，path/regular由历史与混合求导产生，hbase由原八式和初值产生。只追加具体范围说明，不重复批量打勾；弱空间仍未扩展。 | v0.5：(9.5)–(9.7) 的空间/路径接口由具体总装填入；保守 C_P=2Lx，旧勾保留。 |
| 15 / 15 | §10原(10.1)/(10.2)旁的C∞替代实例<br>类别：实际光滑函数、精确参数及系数证明<br>✓ 已证结论（具体光滑范围） | [FullDomainProfile.lean](../LeanPML/Examples/FullDomainProfile.lean)<br>`LeanPML.Examples.FullDomain.profile_contDiff`<br>`LeanPML.Examples.FullDomain.profile_zero_iff`<br>`LeanPML.Examples.FullDomain.profile_bounds`<br>`LeanPML.Examples.FullDomain.regional_threshold`<br>`LeanPML.Examples.FullDomain.four_sides_nonempty`<br>`LeanPML.Examples.FullDomain.four_corners_nonempty` | profile=S*smoothTransition(4x²−1)：物理坐标零、外侧正、幅度≤S、真正C∞；actualRegional使用CP4/A3/K384/c1/16384/S1/65536证书。明确不是原正部幂函数逐字验证，不给原10.1/10.2或精确π常数无限定勾。 | v0.5 替代实例：C∞完整剖面与四边四角已核验；新参数、C_P=4，非原(10.2)。 |
| 16 / 16 | §11.3非零静态模态未编号公式<br>类别：实际非零古典静态解、空间成员与主定理调用<br>✓ 已证结论（具体光滑范围） | [StaticMode.lean](../LeanPML/Examples/StaticMode.lean)<br>`LeanPML.Examples.StaticMode.concreteSolution`<br>`LeanPML.Examples.StaticMode.sideField_weighted`<br>`LeanPML.Examples.StaticMode.concrete_integral_balance`<br>`LeanPML.Examples.StaticMode.nonzero_static_regression` | r0，F(x)真正C∞紧支于p=S平台，λ=φ=(0,F)、Hx=-F、Qx=pF；8式、真实导数、PEC、五初始兼容、零区和加权/普通正则性证明。实际调用主定理得图下界、真实能量律与FTC，E>0恒定/D0，T0也合法。支撑上的p正下界不是一般主定理的全域条件。 | v0.5：§11.3 实际非零静态解已核验；正的常值能量、零耗散，单向吸收。 |

每条均由 [v0.5.3最终完整构建](../logs/v0.5.3/20261014T011533_485975_lake_build.log) 与 [740项审计](../logs/v0.5.3/20261014T011752_801259_axioms_audit.log) 支持，包含前两阶段当前源码。各条源文件哈希和定位矩形见 [annotation_plan.json](../logs/v0.5.3/pdf/annotation_plan.json)。

已有 v0.3 条件性和 v0.4 光滑标记原样保留。本轮在页首补充其具体接入范围，不删除历史“待完成”文字。定义(5.3)/(6.4)/(6.6)、原(5.1)精确π常数、(5.7)/(5.8)传播、弱范围、规范和存在唯一没有新完成勾；第10节只标“替代实例”。v0.5已完成不等于完整弱V7。单层§11.1既有范围勾保留，没有将指定候选扩大为所有单层能量不存在。

修改前新备份及哈希：[backup.json](../logs/v0.5.3/pdf/backup.json)；脚本：[annotate_pdf.py](../logs/v0.5.3/pdf/annotate_pdf.py)；定位准备：[prepare_plan.py](../logs/v0.5.3/pdf/prepare_plan.py)；编辑结构记录：[annotation_result.json](../logs/v0.5.3/pdf/annotation_result.json)；渲染：[render_record.json](../logs/v0.5.3/pdf/render_record.json)；八页实际逐张视觉验收：[visual_review.json](../logs/v0.5.3/pdf/visual_review.json)。

修改前 SHA256 `b7cff33c435944c4c24bf5327246015523368c7015e3b6fb6b65348f8fc5819d`；最终 `730b9d79a305e563791d49cbc5edc0e790895168f171f359af2d4f395eba79ce`。原可选正文、四个页面框、页序和旧批注保持，无正文/批注重叠。标识`LeanPML.v0.5.*`避免再次运行叠加相同标记。


## 2026-10-14：v1.0 弱分析子结论追加（阶段未整体完成）

只修改指定副本。18页及全部208条旧批注保持，新增1个矢量完成勾、2条范围说明，最终211条批注。当前 v1.0.1/v1.0.2 仍部分完成，v1.0.3 弱主定理未合成。旧光滑和条件性勾保持历史范围。

| 实际页 / 印刷页 | 定位 / 类别 | 完整声明及输入范围 | 新标记 / 坐标（左上原点，pt） | 尚缺接口 |
|---|---|---|---|---|
| 7 / 7 | (5.1) 的保守常数子结论；弱空间分析结论 | [WeakPoincare.lean](../LeanPML/Rectangle/WeakPoincare.lean)<br>`LeanPML.Rectangle.weak_poincare`<br>`LeanPML.Rectangle.weakPoincareDomain`<br>在紧支光滑图闭包定义的 H₀¹ 上推广保守常数。一般旧光滑零迹场进入闭包的逼近仍缺；不标原精确公式完成。 | 说明文字，无新勾：v1.0.2：弱 H₀¹ Poincaré 已证，C_P=2Lx；保守常数，非原式精确 π 常数。<br>[67, 518, 301.4833984375, 529.0] | 非零迹理论、一般光滑零迹桥接及弱原系统主定理 |
| 8 / 8 | (5.7) 点上的真实时间积分子结论；真实标量时间积分子结论 | [AuxiliaryMemory.lean](../LeanPML/PML/AuxiliaryMemory.lean)<br>`LeanPML.PML.auxiliary_memory_formula`<br>实际实值时间函数闭区间连续、内部 HasDerivAt，推出变常数公式；梯度输入尚未与弱场识别，不标加权传播完成。 | 说明文字，无新勾：v1.0.2 (5.7)：点上真实 ODE/时间积分版已证；弱场连接及 (5.8) 加权传播未完成。<br>[67, 778, 323.748046875, 789.0] | 弱梯度识别、空间积分与(5.8)加权传播 |
| 11 / 11 | (7.5) 零迹弱 Green；弱空间分析结论 | [WeakGreen.lean](../LeanPML/Rectangle/WeakGreen.lean)<br>`LeanPML.Rectangle.weak_green`<br>`LeanPML.Rectangle.weakGreenDomain`<br>真实弱散度测试配对经线性张成及图范数闭包推广；已填入旧受限空间接口。无一般 Green 输入，无 Λ·n=0；不是最终弱原系统定理。 | ✓ v1.0.2 (7.5)：H₀¹ × H(div) 弱零迹 Green；通量无额外边界条件。<br>H₀¹ 为紧支光滑图闭包；非零迹理论、弱 PML 主定理仍未完成。<br>[67, 488, 284.11181640625, 508.2] | 非零迹理论、一般光滑零迹桥接及弱原系统主定理 |

每项都已核对实际声明类型及独立审计。证据为 [完整构建](../logs/v1.0.3/20261014T104157_124733_lake_build.log) / [796项公理审计](../logs/v1.0.3/20261014T104239_987027_axioms_audit.log)。公理只有标准基础依赖；没有把 Green 或 Poincaré 目标藏进新结构字段。

第7页不对原精确 π 常数打完成勾；第8页不对(5.7)/(5.8)的完整弱场加权传播打完成勾。§5.3及(6.7)–(6.10)、(7.6)–(7.8)、(9.5)–(9.7)没有新增弱主定理完成标记。定义、正则性输入、解存在唯一性均未打勾。

[修改前备份与哈希](../logs/v1.0.3/pdf/backup.json)；[脚本](../logs/v1.0.3/pdf/annotate_pdf.py)；[定位及声明](../logs/v1.0.3/pdf/annotation_plan.json)；[结构核查](../logs/v1.0.3/pdf/annotation_result.json)；[渲染](../logs/v1.0.3/pdf/render_record.json)；[逐页视觉检查](../logs/v1.0.3/pdf/visual_review.json)。稳定ID `LeanPML.v1.0.partial.*` 防止再次叠加。

修改前 SHA256 `730b9d79a305e563791d49cbc5edc0e790895168f171f359af2d4f395eba79ce`；修改后 `4451ed9d022f167b2d66dbb95dd98066cee2c066cb92b935583a6d745d429bf7`。源 md/tex/原PDF不变。


## 2026-10-14 再次数学补齐：第 8 页限定子结论

本轮实际构建 `logs/v1.0.2/20261014T112814_522179_continuation_lake_build.log`、独立审计 `logs/v1.0.2/20261014T112845_938004_continuation_axioms_audit.log` 均退出 0，851 条审计仅标准三公理。当前源码哈希与类型在 `logs/v1.0.2/continuation_20261014T110047/acceptance.json`。下表先建立证据对应，PDF 脚本仅在匹配这些源码哈希与实际审计后添加标记。

### smooth-zero-trace-graph-bridge

- 实际页序 / 印刷页码：8 / 8；定位：§5.2 H₀¹ 初值：光滑零迹进入图闭包的辅助结论（原文未单列）。
- 类型：图范数闭包分析结论。
- 正式文件：`LeanPML/Rectangle/SmoothWeakClosure.lean`。
- 完整声明：`LeanPML.Rectangle.smoothToWeakH1_mem_zeroBoundaryGraph`; `LeanPML.Rectangle.cutoffSequence_toL2_convergence`; `LeanPML.Rectangle.rectangleBubble_weakH01`。
- 已证范围和输入 / 剩余接口：任意现有 SmoothField 四边 ZeroBoundary，经真实内部紧支截断及函数/双偏导 L² 收敛进入现有 H₀¹ 图闭包；非预先紧支多项式泡非零调用。不是一般弱迹核刻画或弱主定理。
- 新增红勾及限定文字：✓ 光滑零迹 / 图逼近已证 / H₀¹ 桥接。左上坐标 (5, 281) pt，字体 6 pt；完整批注内容另含上面的范围和定理。

### actual-weak-field-5-8

- 实际页序 / 印刷页码：8 / 8；定位：(5.8) 实际弱场与加权历史估计。
- 类型：实际弱场/加权空间时间与积分结论。
- 正式文件：`LeanPML/PML/WeightedMemoryBound.lean`, `LeanPML/Analysis/DissipativeMemoryEstimate.lean`。
- 完整声明：`LeanPML.PML.SpatialAbsorption.auxiliary_weak_memory_bound`; `LeanPML.PML.SpatialAbsorption.auxiliary_weighted_integral_bound`。
- 已证范围和输入 / 剩余接口：真实 weakH1Graph/H(div) 路径闭区间连续、初始加权成员、内部普通 L² HasDerivAt 辅助演化及空间兼容下，构造并识别 WeightedL2 历史，证明原常数 2、4cSt。可积性已证；不预设全时段加权成员。未完成原弱八式总装、(5.7) 场指数核原样公式或自动 C²。
- 新增红勾及限定文字：✓ (5.8) 弱场 / 精确加权界 / 需辅助演化 / 非弱主定理。左上坐标 (535, 558) pt，字体 6 pt；完整批注内容另含上面的范围和定理。

### weighted-rate-bound

- 实际页序 / 印刷页码：8 / 8；定位：(5.8) 后未编号 φ_t 加权估计。
- 类型：实际弱场/加权空间时间与积分结论。
- 正式文件：`LeanPML/PML/WeightedForcing.lean`, `LeanPML/PML/AuxiliaryWeightedEvolution.lean`。
- 完整声明：`LeanPML.PML.SpatialAbsorption.auxiliaryRate_weak_norm_sq`; `LeanPML.PML.SpatialAbsorption.auxiliary_derivative_weighted_representative`; `LeanPML.PML.SpatialAbsorption.hasDerivAt_auxiliaryRateX`。
- 已证范围和输入 / 剩余接口：两个真实弱梯度/通量分量的加权右端平方界 2cS(梯度平方和+通量平方和)。普通导数经 HasDerivAt 和原演化识别；下一层需真实输入导数，未称自动 C² 或完整原系统同源层已构造。
- 新增红勾及限定文字：✓ 导数加权界 / 弱梯度分量 / 需真实导数。左上坐标 (535, 613) pt，字体 6 pt；完整批注内容另含上面的范围和定理。

### weighted-membership-propagation

- 实际页序 / 印刷页码：8 / 8；定位：(5.8) 后加权可积性保持子结论。
- 类型：实际弱场/加权空间时间与积分结论。
- 正式文件：`LeanPML/PML/AuxiliaryWeightedEvolution.lean`。
- 完整声明：`LeanPML.PML.SpatialAbsorption.auxiliary_weak_field_membership`; `LeanPML.PML.SpatialAbsorption.physical_auxiliaryWeightedHistory`。
- 已证范围和输入 / 剩余接口：初始 WeightedL2 成员和普通 L² 连续路径/内部真实演化推出全时段加权成员及零区值为零；连续性和内部 C¹ 来自构造历史，非有限范数界直接推出 C²。保留 T=0、两个端点，不要求端点 PDE。
- 新增红勾及限定文字：✓ 成员保持 / 初始加权 / 普通L²演化 / 非自动C²。左上坐标 (5, 640) pt，字体 6 pt；完整批注内容另含上面的范围和定理。

已有页底“(5.8) 未完成”是上一轮状态，保留历史批注，本轮在公式旁新增准确现状；未覆盖或删除。§5.3 不新增规范唯一性勾；方向 Poincaré 仅记录为辅助已证结果，无须借章节号给整体打勾。弱版 (6.7)–(6.10) 不加完成标记。(5.7) 的场指数核尚未单列，本轮实际 Bochner 历史/ODE识别不冒充该原样公式。

PDF 备份、哈希、稳定 ID、坐标、结构与视觉检查保存于 `logs/v1.0.3/pdf/continuation_20261014T110047/`。原版论文、页序、可选正文和全部旧批注保持。


## 2026-10-14 v1.0 数学闭合：弱原系统及规范唯一性

本节为当前追加，前文各阶段“待完成”保留历史语义。仅给本轮实际定理添加4个范围红勾、2条接口接入说明；定义/正则性不打完成勾。旧光滑标记保留。实际页序与印刷页码相同。

证据：[logs/v1.0.3/20261014T121921_205678_lake_build.log](../logs/v1.0.3/20261014T121921_205678_lake_build.log)；[913项公理审计](../logs/v1.0.3/20261014T122038_234964_axioms_audit.log)；[实际输入类型](../logs/v1.0.3/20261014T122040_030951_final_type_review.log)；[源码及隔离验证](../logs/v1.0.3/completion_20261014T122020/verification_before_pdf.json)。

### weak-history-invariants

- 实际第4页，印刷第4页；定位：(2.3)–(2.6) 原→primitive 部分。
- 类型：实际弱空间原系统结论。
- 准确范围：实际Bochner历史、五个L²不变量及初始零兼容保持；不以此宣称任意低正则双向等价。
- 输入/差异：真实 H₀¹/H(div) 图路径、原八式与初始兼容、区域弱系数连续代表、明确时间 jet；保守 C_P=2Lx。
- 剩余范围：最优π常数、最低正则性与一般存在唯一性未证明；旧光滑批注保留。
- 标记：✓ 范围红勾；文字：v1.0 (2.3)–(2.6)：弱原八式的实际历史、五不变量及兼容保持。 / 图空间时间导数；内部 PDE；含 T=0。此勾覆盖原系统 → primitive。
- 位置：左上坐标 x=42，top=758，字体 7.3 pt；最终矩形见 annotation_plan.json。
- 源码：[WeakOriginalSystem.lean](../LeanPML/PML/WeakOriginalSystem.lean), [WeakPrimitiveSystem.lean](../LeanPML/PML/WeakPrimitiveSystem.lean)。
- 完整声明：`LeanPML.PML.Weak.historyU_hasDerivAt`, `LeanPML.PML.Weak.all_invariants_eq_initial`, `LeanPML.PML.Weak.OriginalInterval.reconstruction`, `LeanPML.PML.Weak.OriginalInterval.primitive_main`。

### weak-lift-unique

- 实际第9页，印刷第9页；定位：§5.3 原函数规范唯一性（未编号）。
- 类型：实际弱空间原系统结论。
- 准确范围：两份合法提升对应同一原状态；从重构推出横向差值与零区条件，弱Green/局部性/Poincaré消去；不读取商类任意点值。
- 输入/差异：真实 H₀¹/H(div) 图路径、原八式与初始兼容、区域弱系数连续代表、明确时间 jet；保守 C_P=2Lx。
- 剩余范围：最优π常数、最低正则性与一般存在唯一性未证明；旧光滑批注保留。
- 标记：✓ 范围红勾；文字：v1.0 §5.3：同一原状态的弱提升唯一，能量选择无关。 / 分离区域 W¹,∞ 连续代表；H₀¹ 图闭包；L² 等价类意义。
- 位置：左上坐标 x=42，top=282，字体 7.3 pt；最终矩形见 annotation_plan.json。
- 源码：[LiftUniqueness.lean](../LeanPML/PML/LiftUniqueness.lean), [WeakLiftCompatibility.lean](../LeanPML/PML/WeakLiftCompatibility.lean), [WeakCanonicalEnergy.lean](../LeanPML/PML/WeakCanonicalEnergy.lean)。
- 完整声明：`LeanPML.PML.weak_lift_difference_zero`, `LeanPML.PML.Weak.CompatibleLift.u_unique`, `LeanPML.PML.Weak.CompatibleLift.energy_independent`, `LeanPML.PML.Weak.CompatibleLift.twoLayerEnergy_independent`, `LeanPML.PML.Weak.OriginalInterval.historical_energy_independent`。

### weak-main

- 实际第10页，印刷第10页；定位：定理6.1与(6.7)–(6.10)。
- 类型：实际弱空间原系统结论。
- 准确范围：真实原八式→内部HasDerivAt及精确剩余耗散；闭区间图界、非负、单调、可积性/FTC、原EHP界。不是一般弱解或精确π常数版本。
- 输入/差异：真实 H₀¹/H(div) 图路径、原八式与初始兼容、区域弱系数连续代表、明确时间 jet；保守 C_P=2Lx。
- 剩余范围：最优π常数、最低正则性与一般存在唯一性未证明；旧光滑批注保留。
- 标记：✓ 范围红勾；文字：v1.0 (6.7)–(6.10)：弱原八式 → 图范数界、耗散闭合、单调与积分平衡。 / 保守 C_P=2Lx；区域连续代表及时间 jet 正则性；非适定性或最低正则性。
- 位置：左上坐标 x=42，top=502，字体 7.3 pt；最终矩形见 annotation_plan.json。
- 源码：[MainWeakRectangle.lean](../LeanPML/PML/MainWeakRectangle.lean), [WeakFiniteProblem.lean](../LeanPML/PML/WeakFiniteProblem.lean), [WeakCanonicalEnergy.lean](../LeanPML/PML/WeakCanonicalEnergy.lean)。
- 完整声明：`LeanPML.PML.Weak.OriginalInterval.main_energy_estimate_WeakOriginal`, `LeanPML.PML.Weak.main_energy_estimate_RegionalWeak`, `LeanPML.PML.Weak.OriginalInterval.magnetic_reconstruction`, `LeanPML.PML.Weak.RegionalIntegrals.energy_integrable_and_eq`, `LeanPML.PML.Weak.RegionalIntegrals.dissipation_integrable_and_eq`。

### weak-balance-connection

- 实际第11页，印刷第11页；定位：(7.5)–(7.8) 弱接口接入说明。
- 类型：接口接入范围说明。
- 准确范围：旧弱Green已证明；本轮同源路径和原层演化填入实际空间能量链。无额外弱法向迹构造声明。
- 输入/差异：真实 H₀¹/H(div) 图路径、原八式与初始兼容、区域弱系数连续代表、明确时间 jet；保守 C_P=2Lx。
- 剩余范围：最优π常数、最低正则性与一般存在唯一性未证明；旧光滑批注保留。
- 标记：说明文字，无完成勾；文字：v1.0：弱 Green 与同源图路径已接入 (7.6)–(7.8)，见第10页范围。 / 旧“弱主定理未完成”为历史；新红勾仅指旁注所列的已证版本。
- 位置：左上坐标 x=42，top=202，字体 7.3 pt；最终矩形见 annotation_plan.json。
- 源码：[WeakPathAssembly.lean](../LeanPML/PML/WeakPathAssembly.lean), [WeakFiniteProblem.lean](../LeanPML/PML/WeakFiniteProblem.lean)。
- 完整声明：`LeanPML.PML.Weak.OriginalInterval.base_evolution`, `LeanPML.PML.Weak.OriginalInterval.first_evolution`, `LeanPML.PML.Weak.OriginalInterval.main_energy_estimate_WeakOriginal`。

### weak-gradient-closure-connection

- 实际第14页，印刷第14页；定位：(9.5)–(9.7) 原系统实例化说明。
- 类型：接口接入范围说明。
- 准确范围：通过具体弱图有限问题调用既有梯度与两类吸收预算；不是新增未证接口或一般弱解结论。
- 输入/差异：真实 H₀¹/H(div) 图路径、原八式与初始兼容、区域弱系数连续代表、明确时间 jet；保守 C_P=2Lx。
- 剩余范围：最优π常数、最低正则性与一般存在唯一性未证明；旧光滑批注保留。
- 标记：说明文字，无完成勾；文字：v1.0：(9.5)–(9.7) 已由弱原系统同源路径调用，未外加 Green/Poincaré。 / 常数仍用 C_P=2Lx；时间正则性为明确输入，旧接口说明保留为历史。
- 位置：左上坐标 x=42，top=486，字体 7.3 pt；最终矩形见 annotation_plan.json。
- 源码：[WeakFiniteProblem.lean](../LeanPML/PML/WeakFiniteProblem.lean), [MainWeakRectangle.lean](../LeanPML/PML/MainWeakRectangle.lean)。
- 完整声明：`LeanPML.PML.Weak.OriginalInterval.main_energy_estimate_WeakOriginal`, `LeanPML.PML.Weak.OriginalInterval.first_evolution`。

### weak-static-main-call

- 实际第16页，印刷第16页；定位：§11.3 静态状态：本轮允许变体。
- 类型：实际弱空间原系统结论。
- 准确范围：实际单位矩形非零八变量原解与真实时间导数/加权成员；CP4 K384；不是只有初值可容许性。
- 输入/差异：真实 H₀¹/H(div) 图路径、原八式与初始兼容、区域弱系数连续代表、明确时间 jet；保守 C_P=2Lx。
- 剩余范围：最优π常数、最低正则性与一般存在唯一性未证明；旧光滑批注保留。
- 标记：✓ 范围红勾；文字：v1.0：非零静态解实际调用弱主定理；能量正且恒定，内部耗散为零。 / 本轮为 p=S、r=0、F=1 的允许变体；不是原紧支 F 配置原样核验。
- 位置：左上坐标 x=42，top=558，字体 7.3 pt；最终矩形见 annotation_plan.json。
- 源码：[WeakStaticMode.lean](../LeanPML/Examples/WeakStaticMode.lean)。
- 完整声明：`LeanPML.Examples.WeakStaticMode.originalAt`, `LeanPML.Examples.WeakStaticMode.main_call`, `LeanPML.Examples.WeakStaticMode.nonzero_static_regression`。

保护、备份、坐标、渲染和视觉验收见 [本轮 PDF 记录](../logs/v1.0.3/pdf/completion_20261014/annotation_result.json)。不修改原 md/tex/pdf、路线图和模型合同；未给精确 (5.1)、一般适定性或最低正则性打勾。


## 2026-10-14 v1.0 closeout：追加标注证据

当前原稿与历史批注保留。以下标记在本轮源码构建、公理审计及类型审查通过后执行，最终位置和验收以 `logs/v1.0_closeout/pdf/annotation_result.json`、`visual_review.json` 为准。实际页序与印刷页码相同。完整证据为 `logs/v1.0_closeout/verification_before_pdf.json`，930 条审计无 sorryAx。

- 页序/印刷 **4/4**，命题2.1、(2.5)–(2.6)反向；红勾，坐标（左上制）(55,11)。旁注：v1.0收尾：弱图路径反向重构；八个真实导数、八式及兼容已核验。 / H₀¹ 电场 / H(div) 通量；内部时间方程，不代表一般分布解等价或存在性。。
  范围：弱图路径 primitive_to_original_WeakOn；保留前向与光滑历史标注。
  文件：LeanPML/PML/WeakReverse.lean；声明：`LeanPML.PML.Weak.primitive_to_original_WeakOn`; `LeanPML.PML.Weak.reverse_compatible`; `LeanPML.Examples.WeakStaticMode.reverse_static_call`。
- 页序/印刷 **8/8**，(5.7) 空间值算子指数子结论；红勾，坐标（左上制）(55,11)。旁注：v1.0收尾 (5.7)：加权商类算子指数记忆式；与原辅助场及旧历史连接。 / 两个方向含零吸收；逐点标量指数核的代表元识别仍待完成。。
  范围：B为有界吸收乘子，证明Bochner核exp((s-t)B)公式；不声称已识别点值exp(-p(x)(t-s))。
  文件：LeanPML/Analysis/OperatorMemory.lean, LeanPML/PML/AuxiliaryOperatorMemory.lean；声明：`LeanPML.Analysis.operator_memory_formula`; `LeanPML.PML.SpatialAbsorption.auxiliary_operator_memory`; `LeanPML.PML.Weak.OriginalInterval.operator_memory_both`。
- 页序/印刷 **10/10**，(6.6) 正则性连接说明；仅说明、不打勾，坐标（左上制）(55,433)。旁注：v1.0收尾 (6.6)连接：λ_tt由图导数及辅助演化推出；T=0初始兼容仍单列。。
  范围：不是给正则性假设打完成勾；λ_tt不再作为独立输入。未声明与整套C^k正则性定义等价。
  文件：LeanPML/PML/WeakV7Regularity.lean；声明：`LeanPML.PML.Weak.V7TimeRegularity.flux_second`; `LeanPML.PML.Weak.V7TimeRegularity.main_energy_and_auxiliary`。
- 页序/印刷 **13/13**，(8.4)–(8.8)输入原变量控制；红勾，坐标（左上制）(55,764)。旁注：v1.0收尾 (8.4)–(8.8)：输入原 Z1/Z2/Qx/Qy 的 L² 控制及初值能量界。 / 含 u、q、φ；保守 C_P=2Lx，仍采用列明的弱图路径与初始兼容。。
  范围：实际O.fields原变量由兼容保持识别后接PhysicalControl，常数未放宽；不是任意裸八变量范数等价。
  文件：LeanPML/PML/WeakPhysicalControl.lean；声明：`LeanPML.PML.Weak.OriginalInterval.original_auxiliary_control`; `LeanPML.PML.Weak.OriginalInterval.original_auxiliary_initial_control`。

第8页旧“场连接/5.8未完成”仅作为历史保留；本轮追加算子核范围，既有5.8证据不被旧文字否定。第4页旧前向限定保留，新勾只说明反向已补齐。原(5.1)精确常数及一般W¹,∞连续代表没有新增完成标记，也没有追加任何存在唯一性、严格衰减主张。


本轮最终证据：`logs/v1.0_closeout/acceptance.json`。主工程完整构建与930条审计、隔离目录从零构建本工程及完整审计均通过；隔离复用精确依赖缓存。PDF第4、8、13页新增范围红勾，第10页增加正则性连接说明；旧221条批注全部保留。最终仍为部分收尾，未登记V7原文逐项对齐完成。


## 2026-10-14 v1.0_completion 追加证据（保留全部历史标记）

本轮源码构建及997项审计通过；精确常数、标量核和真实 C^k 桥接分别核验。一般 W¹,∞ 连续代表仍未构造，不能登记 ROADMAP v1.0 全部完成。旧“精确常数/标量核待完成”是历史状态，本轮仅追加更新，不删除旧批注。

构建：`logs/v1.0_completion/20261014T170041_585017_lake_build.log`；审计：`logs/v1.0_completion/20261014T170212_199650_axioms_audit.log`；实际类型：`logs/v1.0_completion/20261014T170234_873529_type_review.log`。

|实际页序/印刷页码|公式与类别|完整声明/代码|准确范围、剩余接口|本轮旁注与定位|
|---|---|---|---|---|
|7 / 7|(5.1)；已证分析子结论|`LeanPML.Rectangle.weak_sharp_poincare`<br>`LeanPML.Rectangle.sharpPoincareConstant_sq`<br>`LeanPML.Rectangle.sharpWeakPoincareDomain`<br>`LeanPML/Rectangle/SharpPoincare.lean`|一维 Dirichlet–Wirtinger → 切片 → Fubini → H¹ 图闭包；CP²=(π²/Lx²+π²/Ly²)⁻¹。|✓ v1.0本轮：(5.1) 原 π 常数已证；真实矩形 H₀¹ 图闭包，含两方向 Fubini。 / 已接入精确阈值及新弱原系统能量入口；不要求常数最优性另证。；x=55, top=11 pt|
|8 / 8|(5.7)；已证分析子结论|`LeanPML.Analysis.dampingKernel_eq_scalarExpMultiplier`<br>`LeanPML.PML.Weak.OriginalInterval.scalar_memory_both`<br>`LeanPML.PML.Weak.OriginalInterval.scalar_memory_physical_x`<br>`LeanPML.PML.Weak.OriginalInterval.scalar_memory_physical_y`<br>`LeanPML/Analysis/MultiplierExponential.lean`<br>`LeanPML/PML/AuxiliaryScalarMemory.lean`|追加更新旧算子核待识别说明：有界吸收乘子指数已等于 exp(tp) 乘子，并识别原辅助场。无共同零测集全时间结论；固定差值系数在积分内。|✓ 本轮 (5.7)：标量指数乘子/Bochner 公式已证；双方向、逐时刻商类，含零吸收。；x=55, top=269 pt|
|10 / 10|(6.6) 正则性充分性连接；正则性连接说明|`LeanPML.PML.Weak.V7ClosedCkCore.regularity`<br>`LeanPML.PML.Weak.V7ClosedCkCore.canonical_fields`<br>`LeanPML.PML.Weak.V7ClosedCkCore.main_energy`<br>`LeanPML/PML/WeakCanonicalTime.lean`|不是正则性自动传播完成勾。正长度 canonicalInterval 规范 E/P 端点导数槽；原场不变，不增加端点 PDE。|本轮 (6.6) 连接已证：T>0 的真实 C^k 构造路径；T=0 初始导数层兼容另列。；x=55, top=547 pt|
|10 / 10|(6.7)–(6.10) 精确常数版；已证分析子结论|`LeanPML.PML.Weak.OriginalInterval.main_energy_estimate_SharpWeakOriginal`<br>`LeanPML.PML.Weak.main_energy_RegionalSharpCk`<br>`LeanPML.Examples.WeakStaticMode.canonical_main_call`<br>`LeanPML/PML/MainSharpWeakRectangle.lean`<br>`LeanPML/PML/WeakCanonicalTime.lean`|(6.7)图界、(6.8)定量耗散与真实求导、(6.9)单调/Bochner时间平衡、(6.10)原场控制。T≥0 jet入口保留退化兼容；Ck规范入口T>0。代表选择仍未证。|✓ 本轮 (6.7)–(6.10)：原 π 常数；弱图/C^k 类；区域连续代表仍输入，非完整 W¹,∞ 对齐。；x=55, top=609 pt|
|13 / 13|(8.4)–(8.8)；已证分析子结论|`LeanPML.PML.Weak.OriginalInterval.sharp_original_auxiliary_control`<br>`LeanPML.PML.Weak.OriginalInterval.sharp_original_auxiliary_initial_control`<br>`LeanPML/PML/MainSharpWeakRectangle.lean`|通过同一原解的闭区间兼容保持识别 O.fields 中 Z1/Z2/Qx/Qy；常数保持原式。|✓ 本轮 (8.4)–(8.8)：精确 C_P 下输入原 Z/Q 与 u/q/φ 的控制及初值界。 / 所选弱图路径、初始兼容；不表示任意八变量裸 L² 范数等价。；x=55, top=497 pt|
|15 / 15|(10.1) 及后续小量不等式；已证分析子结论|`LeanPML.Rectangle.ParameterCertificate.original_parameters_threshold`<br>`LeanPML.Rectangle.ParameterCertificate.original_amplitude_certificate`<br>`LeanPML.Rectangle.ParameterCertificate.original_parameters_explicit`<br>`LeanPML/Rectangle/SharpParameterCertificate.lean`|三条显式小量与KS²严格界，接回min阈值；未单独证明显示的min最小分支等式。|✓ 本轮 (10.1)：原数值阈值已证；C_P²=2/π²，K=48/π²，c=1/128，S=1/512。 / 严格使用 π>3；不附带宣称 (10.2) 全族连续代表构造或解存在性完成。；x=55, top=11 pt|

本轮定位、输入哈希、带时间备份、标注脚本及渲染验收放在 `logs/v1.0_completion/pdf/`。最终执行结果以 `annotation_result.json`、`visual_review.json` 为准。只改指定副本；不对未完成代表选择、适定性、任意单点正则性或完整弱 V7 范围添加完成勾。


## 2026-10-14 v1.0_finalization：一般弱系数与原剖面最终连接

本节追加更新旧旁注的历史范围，不删除旧勾或用户批注。副本修改前为18页、231条批注，SHA256 `ac8430fa24c936013550a0c71e480b72c4d6801067a1afcee8398de42c8d941e`。本轮新增范围如下；只给已证结论打勾，(6.6) 的假设本身不打完成勾。精确 (5.1) 与实际标量核 (5.7) 的上一轮标记已复核，无需重复叠加。

正式构建：[20261014T181951_587380_lake_build.log](../logs/v1.0_finalization/20261014T181951_587380_lake_build.log)；完整审计：[20261014T182113_565033_axioms_audit.log](../logs/v1.0_finalization/20261014T182113_565033_axioms_audit.log)；类型输出：[当前完整类型](../logs/v1.0_finalization/20261014T182149_492115_type_review.log)。均退出0；1058次审计输出（1050个不同声明），仅标准基础公理。

|实际页序/印刷页码|公式或定位|类别及范围|文件与完整声明|旁注/坐标|
|---|---|---|---|---|
|3/3|§1 一般分离 W¹,∞ 系数的代表（辅助结论，原文未单列）|真实二维弱测试→一维分布原函数→闭区间Lipschitz代表；构造原区域系数入口，原8式及加权空间按a.e.识别。|`LeanPML.Analysis.exists_regional_lipschitz_representative`<br>`LeanPML.PML.RawWeakRegionalAbsorption.representatives`<br>`LeanPML.PML.RawWeakRegionalAbsorption.weighted_spaces_eq`<br>`LeanPML.PML.Weak.OriginalInterval.changeCoefficients`<br>[WeakIntervalRepresentative.lean](../LeanPML/Analysis/WeakIntervalRepresentative.lean)<br>[WeakAbsorptionRepresentative.lean](../LeanPML/PML/WeakAbsorptionRepresentative.lean)<br>[WeakCoefficientTransport.lean](../LeanPML/PML/WeakCoefficientTransport.lean)<br>[MainRepresentedWeak.lean](../LeanPML/PML/MainRepresentedWeak.lean)|✓ v1.0最终：区域分离 W¹,∞ 已构造 Lipschitz 代表；原乘子、权重及积分 a.e. 不变。<br>连续性不再独立输入；幅度仅要求计算域，保留全零、单向及角层。<br>x=55，top=11，字号=6.3|
|9/9|§5.3 / (6.4) 合法提升选择无关|复用弱乘积零迹保持、方向Poincare及弱梯度局部性；新代表构造消去旧规范唯一性调用的独立连续性输入。|`LeanPML.PML.Weak.OriginalInterval.historical_energy_independent_GeneralWeak`<br>`LeanPML.PML.Weak.twoLayerEnergy_independent_GeneralWeak`<br>[MainGeneralWeak.lean](../LeanPML/PML/MainGeneralWeak.lean)|✓ v1.0最终 §5.3：一般分离弱系数的合法提升及两层能量选择无关；商类意义。<br>连续代表在证明内构造；不把两个任意状态当成同源时间层。<br>x=55，top=11，字号=6.3|
|10/10|(6.6)接口及 (6.7)–(6.10) 原系统先验定理|当前原八式主入口；不再独立输入p/r连续性。Ck正长度，零长度使用明确初始jet兼容，闭区间输出及内部导数分开。勾是能量结论，不给(6.6)假设本身打勾。|`LeanPML.PML.Weak.OriginalInterval.main_energy_GeneralWeakCk`<br>`LeanPML.PML.Weak.OriginalInterval.main_energy_GeneralWeakJet`<br>`LeanPML.Examples.GeneralWeak.static_ck_call`<br>[MainGeneralWeak.lean](../LeanPML/PML/MainGeneralWeak.lean)<br>[GeneralWeakRegression.lean](../LeanPML/Examples/GeneralWeakRegression.lean)|✓ v1.0最终：(6.7)–(6.10) 一般分离弱系数；原 π 常数；连续代表已由弱导数构造。<br>真实 C^k/初始加权成员；T>0 规范入口，T=0 合法初始 jet。不是适定性。<br>x=55，top=813，字号=6.3|
|15/15|第10节未编号 c_* 最小分支等式|真实sharpPoincareConstant/threshold定义，严格π界；保留c=1/128,S=1/512及三条已证小量证书。|`LeanPML.Rectangle.ParameterCertificate.original_threshold_min`<br>`LeanPML.Rectangle.ParameterCertificate.original_threshold_exact`<br>[OriginalParameterThreshold.lean](../LeanPML/Rectangle/OriginalParameterThreshold.lean)|✓ v1.0最终：原 c*=min{π/√48,π²/1152,1/24}=π²/1152 已严格核验。<br>x=55，top=90，字号=6.3|
|15/15|(10.2) 原幂次剖面全族|物理区、四边四角分支，技术Lipschitz截断在域内等于原式；非恒定代表经构造接入新主定理。并非C∞替代剖面。|`LeanPML.Examples.OriginalPower.extension_eq_profile`<br>`LeanPML.Examples.OriginalPower.absorption_branches`<br>`LeanPML.Examples.OriginalPower.representative_nonconstant`<br>`LeanPML.Examples.GeneralWeak.original_profile_main`<br>[OriginalPowerProfile.lean](../LeanPML/Examples/OriginalPowerProfile.lean)<br>[GeneralWeakRegression.lean](../LeanPML/Examples/GeneralWeakRegression.lean)|✓ v1.0最终 (10.2)：m≥2、0<ηx,ηy≤1/512 的原剖面全族，真实区域弱导数/幅度已证。<br>x=55，top=576，字号=6.3|
|15/15|(10.2) 本轮范围说明|更新本页旧“全族待证/C∞替代”旁注的历史范围；不删除旧批注。|`LeanPML.Examples.GeneralWeak.original_profile_main`<br>[GeneralWeakRegression.lean](../LeanPML/Examples/GeneralWeakRegression.lean)|说明：本轮已接入一般弱系数主入口；原参数有效。剖面/数据证书不表示一般演化解存在。<br>x=55，top=781，字号=6.3|

备份、前后哈希、稳定标记ID、碰撞检查、源码哈希、标注脚本及逐页视觉检查位于 [logs/v1.0_finalization/pdf](../logs/v1.0_finalization/pdf)。最新总验收见 [acceptance.json](../logs/v1.0_finalization/acceptance.json)。

本轮主定理采用一般区域分离弱系数，不再独立输入连续代表；正长度 Cᵏ 与零长度合法初始 jet 分支分别说明。没有标为一般适定性、严格/指数衰减。原 (10.2) 全族是合法系数证书，主入口零解调用不表示相应非零初值产生一般演化解。§11.3 的非零静态原解调用在代码/日志中保留；不为增加数量重复给旧静态勾叠加标记。


### v1.0_finalization 最终工程与 PDF 验收（2026-10-14）

当前119个正式 Lean 文件全部可达，默认构建3131 jobs通过；1058次审计输出覆盖1050个不同声明，本轮新增61个不同审计声明，无 sorryAx，仅标准 propext/Classical.choice/Quot.sound。当前源码隔离重编和完整审计通过，复用精确依赖缓存、不复制项目编译产物。源文件在最终验证后未改变。

PDF 实际/印刷第3、9、10、15页新增5勾及1条限定说明，18页和231条旧批注全部保留；最终237条批注。逐页渲染和碰撞检查通过，详见本轮 `pdf/annotation_result.json`、`pdf/visual_review.json`。旧第一次隔离结果保留为 `isolated_intermediate_*`：它之后曾补充当前辅助变量控制，因此不作为最终源码证据；最终隔离使用新目录重新从零构建。

最终依据为 [acceptance.json](../logs/v1.0_finalization/acceptance.json) 与 [source_snapshot.json](../logs/v1.0_finalization/source_snapshot.json)。主线没有尚未兑现的分析接口；T=0初始图状态条件及先验解正则性保留为明示的数学输入，不宣称适定性、严格衰减或任意分布解理论。
