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
