# v0.4.1–v0.4.4：所选光滑矩形类分别验收完成

用途：记录实际几何、空间分析、时间路径和原模型映射。下方保留全部旧历史；旧“未实现”仅表示当时状态。本轮停在具体接口构造，未创建 v0.5 的主定理或报告，没有依赖更新、提交或推送。

| 阶段 | 状态 | 真实构建 / 独立审计 | 审计声明数（含历史） |
|---|---|---|---|
| v0.4.1 | 已验收 | [构建](logs/v0.4.1/20261013T224101_375806_lake_build.log) / [审计](logs/v0.4.1/20261013T224142_908894_axioms_audit.log) | 410 |
| v0.4.2 | 已验收 | [构建](logs/v0.4.2/20261013T224801_700595_lake_build.log) / [审计](logs/v0.4.2/20261013T225034_426223_axioms_audit.log) | 429 |
| v0.4.3 | 已验收 | [构建](logs/v0.4.3/20261013T230513_776030_lake_build.log) / [审计](logs/v0.4.3/20261013T230651_423759_axioms_audit.log) | 484 |
| v0.4.4 | 已验收 | [构建](logs/v0.4.4/20261013T230822_044824_lake_build.log) / [审计](logs/v0.4.4/20261013T231144_117778_axioms_audit.log) | 537 |

- **v0.4.1**：`Domain/Fields/Boundary` 给出全开矩形与闭矩形测度对应、Fubini、真实 fderiv、光滑场的 L² 表示；由 a.e. 相等推导连续代表在闭矩形相等，保证梯度与四边迹良定义、线性，并接到原受限空间域。
- **v0.4.2**：`Green/Poincare` 证明右−左+上−下的实际四边公式、迹消去，并直接构造 Green 与同迹核的 Poincaré 接口。保守常数为 $C_P=2L_x$，故 $K=32\mu(\varepsilon+2\kappa)L_x^2$；阈值使用这一常数。原精确 π 常数未证，未沿用其数值证书。非零多项式泡函数的 Green/Poincaré 和时间路径调用已编译。
- **v0.4.3**：`TimeSpace/L2Paths/SmoothPaths/WeightedCalculus/StatePaths/BoundaryTime` 从联合光滑性证明混合导数交换，用 C(K) 统一路径的实际可导性识别 L² 导数，并识别加权路径恢复的 φ_t/φ_tt。构造同源路径、梯度/散度交换及两层迹；成员资格、统一/加权范数连续可微仍为明确强正则性输入。
- **v0.4.4**：`OriginalSystem/PrimitiveSystem/Equivalence/HistoryL2/InterfaceAssembly/OriginalAssembly` 完成真正历史积分、L² Bochner 对应、五个不变量的实际场保持、初始兼容和原场零区保持、双向八式及 PEC；最终从原方程与初始数据构造 `originalFiniteIntervalProblem_separated`，并给出 P_tt 连续性。没有把任一目标分析公式或全时段兼容藏入正则性。

## 输入范围、差异与未完成事项

选用整个矩形上的全空间 C∞ 技术延拓、联合时间光滑性、C(K) 一致范数正则性及实际加权路径成员/可微性，强于原文 (6.6)/W¹,∞ 弱范围；域外不要求 PDE。原演化只在 (0,T)×Ω，PEC/连续性/历史覆盖 [0,T]。无吸收正下界，无 w 上界，无磁场法向约束，无额外子区边界。

T=0 的初始导数层极化和零区 φ_t 条件单列；不能由空内部推导。E_t 的闭端点零迹若另行需要，采用 BoundaryTime 中带退化初始迹条件的结论。一般非零初始不变量已保持，但额外源项 primitive 版本未纳入无源总装。

未完成：原精确 Poincaré 常数；一般弱 H₀¹–H(div)/W¹,∞ 实现；(5.7)/(5.8) 加权传播；提升规范唯一性；解存在唯一性、严格衰减、Laplace/完美匹配。v0.5.1 才调用现有抽象主定理发布具体光滑先验结论，不以本轮构造替代最终声明。

## 证据与阅读

每阶段 `logs/<stage>/acceptance.json` 保存成功日志及源码哈希；真实失败与修复日志未覆盖。最终 v0.4.4 全工程构建包含所有先前阶段。独立假设检查见 [semantic_review_geometry.md](logs/v0.4.4/semantic_review_geometry.md)，受保护文件见 [source_verification.json](logs/v0.4.4/source_verification.json)。论文与路线图状态差异保留为历史；没有改源文件和旧日志。

先读 `greenDomain`、`hasDerivAt_jet_gradientX`、`original_to_primitive_rectangle`，再看 `originalFiniteIntervalProblem_separated`。InfoView、F12、重建/审计及刷新导入见 [README](README.md)。PDF 新范围见 [标注账本](docs/pdf_formalization_marks.md)，只有实际已证子结论加勾。

---

# 2026-10-13：v0.3.4–v0.3.5 分别验收完成

用途：登记第 9 节空间估计、耗散闭合及有限区间条件性主定理。下方全部历史原样保留，旧“当前/下一阶段”指记录当时。本轮止于 v0.3.5，未实施 v0.4，没有提交、推送、依赖更新或新增 reading_guide。

## v0.3.4：已完成

新增 [GradientControl.lean](LeanPML/PML/GradientControl.lean)，18 条正式定理。

- (9.2)：实际 L² 的有界 θ 乘子及 J 内积定义，密度可积、积分对应与非负性；空间约束把 Λ−ψ 接到梯度。
- 零区 θ=1/2、ψ=0 a.e. 给 J 密度为梯度平方和，保留空间耗散，不删除物理区。
- (9.3)：实际 fieldSpatialDissipation 同时控制 (c−S)J 和 3cJ/4。
- (9.4)：真实原层辅助演化、SameSourcePath 与时间/梯度接口推出两方向关系。
- (9.5)：系数分配、三项平方估计、a.e. 场等式、可积性和积分序关系得到准确常数 3、3S²；全零吸收、两个不对称边层与不对称角层均有正式调用。

- [实际默认构建](logs/v0.3.4/20261013T214336_169080_lake_build.log)／[独立公理审计](logs/v0.3.4/20261013T214424_960799_axioms_audit.log)：退出码均为 0，审计 334 条。
- [命令、哈希与阶段验收](logs/v0.3.4/acceptance.json)／[新增定理索引](logs/v0.3.4/new_theorems.json)。每个日志旁同名 `.json` 记录真实命令、目录与退出码。

## v0.3.5：已完成

新增 [DissipationClosure.lean](LeanPML/PML/DissipationClosure.lean)（14 条定理）和 [MainAbstract.lean](LeanPML/PML/MainAbstract.lean)（21 条定理）。本轮合计 53 条新定理。

1. 实际单层积分下界和 (9.1)，其中 Debye 关系从邻域兼容及真实导数得到，未新增教学子系统方程。
2. (9.6) 使用同一迹核的 Poincaré、(9.3)、(9.5) 与原阈值；正式证明 KS²≤Kc²/16≤1/16≤1。非空空间载体仅用于从0≤p≤S取得S≥0，矩形载体ℝ×ℝ自动满足，不排除零吸收或零测度。
3. (9.7) 从真实 κE_t=P_t+τP_tt 得到平方分项界，再分别使用两条材料阈值。
4. (6.8) 精确定量闭合：空间耗散支付 E 负项后剩一半；Debye 耗散支付 E_t 负项后剩 μτ/(4κ) 平方项；由剩余项证明非负，随后结合原条件性能量律给真实导数非正。
5. 有限闭区间单调性、0≤E₇(t)≤E₇(0)，保留 (6.7) 及七类原/辅助变量重构控制并接到初始能量。
6. 实际时间积分平衡单独用固定 mathlib FTC 证明，能量连续与耗散可积都从实际普通/加权场路径推出。

- [实际默认构建](logs/v0.3.5/20261013T214810_766115_lake_build.log)／[独立公理审计](logs/v0.3.5/20261013T214845_382134_axioms_audit.log)：退出码均为 0，审计 369 条。
- [命令、哈希与阶段验收](logs/v0.3.5/acceptance.json)／[新增定理索引](logs/v0.3.5/new_theorems.json)。每个日志旁同名 `.json` 记录真实命令、目录与退出码。

两个阶段完整审计仅出现标准 `propext`、`Classical.choice`、`Quot.sound`，没有 sorryAx。源码、默认导入与每条新定理的审计覆盖已经核对。v0.3.5 最终构建包含 v0.3.4 全模块，没有修改旧数学模块。

## 最终定理假设与时间范围

`FiniteIntervalProblemConditional` 的输入只包括：T≥0；Ioo 0 T 上同源真实普通/加权导数；原层 primitive 演化；受限梯度/散度、Green、迹和时间交换接口；两层 Icc 0 T 上分量连续；闭区间静态极化、空间和同一迹核约束。一般 Poincaré 单独列明，参数包只有原阈值及正性。没有目标梯度界、耗散符号、单调性或积分平衡字段。`PhysicalInitialControlBounds` 是结论包，不是输入条件。

- 真实能量导数、同源梯度估计、定量耗散下界在 (0,T) 使用内部演化。
- 静态双边界、能量非负、单调性及初值控制在 [0,T] 成立。
- 积分平衡额外要求 second.R（内部实际为 P_tt）在闭区间 L² 连续；由此证明 D₇ 连续和 IntervalIntegrable。单调性无需这项附加条件。
- T=0、t₁=t₂、t₁=0、t₂=T 都保留，没有端点双侧导数；不能用 T=0 的空内部条件推出端点兼容或耗散正性。

以上输入另经人工语义审查；仅通过 #print axioms 不足以发现普通结构字段中的循环假设。逐项内容追加于 [定理清单](docs/theorem_inventory.md)、[结论账本](docs/claim_ledger.md)。学习内容集中在 [README](README.md) 和代码中文注释。

## 失败、修复与来源记录

实际日志保留固定 FTC 模块缺少编译产物后的补编译、系数/积分/序关系 API 修复、一次并行期间短暂缺失 GradientControl.olean，以及审计覆盖检查拦截的一条前缀重名漏项。后者修改注册工具为完整行精确匹配，补列 debye_absorption 后重新构建与审计。没有修改锁文件、降低常数或通过占位证明填补缺口。

[来源复核](logs/v0.3.4/source_review.md)、[入场快照](logs/v0.3.4/source_snapshot.json)、[前阶段证据复核](logs/v0.3.4/previous_review.json)确认原 V7、模型合同和固定配置未变。路线图部分复选框已勾选而状态文字仍旧，本轮保持路线图原样，以源码和真实验证为准。

## PDF 标注及最终保护检查

通过全部构建/审计后，才编辑指定副本。18 页、168 项旧批注及可选正文全部保留；实际/印刷第 10、12、13、14 页新增 10 个带范围矢量红勾和 5 条说明，最终 183 项批注。

- 第 10 页：(6.8) 条件性精确耗散闭合，(6.9) 条件性单调性及积分平衡；定理 6.1 只说明抽象接口下核心闭合。
- 第 12 页：只更新历史状态说明，不重复叠加旧红勾。
- 第 13 页：(9.1) 条件性耗散下界。
- 第 14 页：J 的可积非负子结论，(9.3)、(9.4)、(9.5)、(9.6)、(9.7) 以及未编号剩余耗散下界；J 定义只标说明。
- 具体矩形分析、原 PDE 对应和解存在唯一性没有完成勾；既有旧待完成标记保留，旁边/页首说明其历史范围。

[PDF 账本](docs/pdf_formalization_marks.md)、[新备份与哈希](logs/v0.3.5/pdf/backup.json)、[证明及定位计划](logs/v0.3.5/pdf/annotation_plan.json)、[结构验收](logs/v0.3.5/pdf/verification.json)、[逐页视觉验收](logs/v0.3.5/pdf/visual_review.json)均保留。四个修改页用 Poppler 150 dpi 重新渲染、逐页查看，无遮挡、裁切或缺字。最终保护、导入、审计、历史与链接检查见 [final_checks.json](logs/v0.3.5/final_checks.json)。

## 下一阶段（未实施）

v0.4.1：具体矩形 Domain、Fields、Boundary，建立全矩形上的光滑场、坐标导数、四边迹及 PEC/零迹表示。之后再兑现 Green/Poincaré、时间微分交换、完整原模型映射及提升唯一性。本轮已经闭合的是条件性先验能量定理；没有证明具体原 PDE 全形式化、解存在唯一性或严格衰减。

---

# 2026-10-13：v0.3.2–v0.3.3 分阶段验收完成

用途：记录本轮真实条件性能量律、图范数与重构控制的实现和验证；下方全部历史原样保留。当前止于 v0.3.3，未进入 v0.3.4，没有提交、推送、依赖更新或新增 reading_guide。

## v0.3.2：已完成

新增五个正式模块：[BalanceInterfaces](LeanPML/PML/BalanceInterfaces.lean)、[PrimitiveEvolution](LeanPML/PML/PrimitiveEvolution.lean)、[SpatialBalance](LeanPML/PML/SpatialBalance.lean)、[BalanceBlocks](LeanPML/PML/BalanceBlocks.lean)、[BalanceAbstract](LeanPML/PML/BalanceAbstract.lean)，新增 25 条公开定理。

实际完成：从原层 primitive 演化和真实普通/加权 L² 导数出发，组合既有三个块；一般 Green 下得到 (7.6) 含边界真实求导，零迹下消去边界。对邻域内原方程真实求导，推出同源导数层同系统，并逐层使用 u/E/E_t 零迹，最终证明 (7.8) 的 `HasDerivAt energy7 (-dissipation7 …) t`。只输入原层系统，不把 first 层 PDE 或目标能量律作为独立假设。

条件接口为受限梯度/散度域、迹与独立边界配对、一般 Green、梯度/散度时间交换以及两层域成员与零迹。具体矩形实现待 v0.4.1–3。未证明 D₇≥0 或单调性。

- [默认构建](logs/v0.3.2/20261013T095839_225389_lake_build.log)／[命令与退出码](logs/v0.3.2/20261013T095839_225389_lake_build.json)：退出 0，2877 个任务。
- [独立公理审计](logs/v0.3.2/20261013T100104_046897_axioms_audit.log)／[元数据](logs/v0.3.2/20261013T100104_046897_axioms_audit.json)：退出 0，共 288 条结果（原 263 + 新 25）。
- [新增定理索引](logs/v0.3.2/new_theorems.json)、[阶段验收](logs/v0.3.2/acceptance.json)。
- 编译修复包括有界系数的 bc 展开、自伴内积方向、空间块配对展开及导入产物缺失；实际失败与修复日志均保留。未放宽数学结论。

## v0.3.3：已完成

新增 [Coercivity](LeanPML/PML/Coercivity.lean)、[PhysicalControl](LeanPML/PML/PhysicalControl.lean)，新增 28 条公开定理；两个阶段共新增 53 条。实际完成：

1. (8.3)：空间约束与已有零延拓嵌入推出梯度控制；明确零迹 Poincaré 下推出位移控制。
2. (8.1) 消元、(8.2) 原阈值系数界、Young 与实际积分序关系，得到单层精确 $N^2/4\le F_c\le N^2$。
3. 同一参数、同源两层得到 (6.7)；图平方或能量为零时全部受约束坐标为零。不安装未经证明的 Norm 实例。
4. 实际 L² 重构得到 (6.10)、(8.4)–(8.8)，保持所有原常数、Q 方向及 μ/ε/κ 缩放。低层中间图界在正式入口中从原参数与约束推出。
5. `ConditionalPoincare.ofGreenTrace` 用迹算子之核统一两个阶段的零迹接口；未声称由 Green 已证 Poincaré。

- [默认构建](logs/v0.3.3/20261013T100156_159842_lake_build.log)／[命令与退出码](logs/v0.3.3/20261013T100156_159842_lake_build.json)：退出 0，2879 个任务，包含全部 v0.3.2 模块。
- [独立公理审计](logs/v0.3.3/20261013T100321_602582_axioms_audit.log)／[元数据](logs/v0.3.3/20261013T100321_602582_axioms_audit.json)：退出 0，共 316 条结果。
- [新增定理索引](logs/v0.3.3/new_theorems.json)、[阶段验收](logs/v0.3.3/acceptance.json)。
- 两次审计只出现标准 propext、Classical.choice、Quot.sound，没有 sorryAx 或自定义占位公理。
- 真实失败保存在各阶段目录，包括一次并行开发中短暂缺失 .olean，随后转为串行整体验证；锁文件与数学条件未改。

原文 §8.2 末尾严格 $<B_{\rm sp}$ 在零状态下不成立。本轮使用目标所需非严格估计，保留零状态和原 1/4、1 常数。V7 md/tex/原 PDF 与上阶段一致；入场路线图仅有用户已有 v0.3.1 五个复选框变动，本轮没有改路线图。见 [入场哈希](logs/v0.3.2/source_snapshot.json) 和 [来源复核](logs/v0.3.3/pdf/source_review.md)。

## PDF 与最终保护检查

在两阶段实际构建/审计通过后才编辑指定副本。18 页与原 150 项批注完整保留，在实际/印刷第 10–13 页新增 12 个范围红勾和 6 条说明，共 168 项批注。原始 md/tex/pdf 未动。旧“待完成”标记原样保留，并增加当前范围说明。

- 第 10 页：(6.7) 条件性图范数界、(6.10) 兼容重构 L² 控制。
- 第 11 页：(7.6) 条件性空间能量恒等式；(7.5) 只标 Green 接口说明。
- 第 12 页：(7.8) 条件性两层恒等式、(8.3) 空间约束/Poincaré 控制、§8.1 条件性下界。
- 第 13 页：§8.2 条件性上界、(8.4)–(8.8) 逐项重构控制及严格号的零状态说明。
- 未给 (6.8)–(6.9)、(9.5)–(9.7)、耗散非负或最终单调性添加整体完成勾。

[PDF 账本](docs/pdf_formalization_marks.md)逐项给公式、完整 Lean 名称、实际假设、剩余接口和证据。
[备份及哈希](logs/v0.3.3/pdf/backup.json)、[标注计划](logs/v0.3.3/pdf/annotation_plan.json)、[结构/证据验证](logs/v0.3.3/pdf/verification.json)、[四页视觉验收](logs/v0.3.3/pdf/visual_review.json)均已保存；定位检查无原文遮挡，150 dpi 图逐页检查无裁切或字体缺失。

[最终一致性检查](logs/v0.3.3/final_checks.json)核对正式导入、全部审计、保护文件、历史保留与链接。说明集中在 [README](README.md)；实际接口在 [theorem_inventory](docs/theorem_inventory.md)、[claim_ledger](docs/claim_ledger.md)追加登记。

## 下一阶段（本轮未开始）

v0.3.4：从辅助演化和同源梯度关系构造 J 的实际积分，使用 θ 分配权重推导 (9.5)，包括零吸收分支及 S≥3cJ/4。两类耗散预算闭合、单调性和积分平衡留到 v0.3.5。具体矩形 Green/Poincaré/迹与微分交换、完整原 PDE 对应和提升唯一性仍待后续。

---

# 2026-10-13：v0.3.1 实际内积、加权状态与能量定义

用途：记录本阶段真实函数空间、合法积分、时间求导、构建/审计及 PDF 范围标注。下方旧阶段记录完整保留，“当前/下一阶段”均指记录当时。

**v0.3.1 已完成。** 新增六个正式模块，109 条定理；保留旧 154 条审计，共 263 条实际公理输出。本轮未进入 v0.3.2，没有更新 Lean/mathlib、修改路线图、提交或推送，也没有新建 reading_guide。

## 实际实现与假设

- [EnergyCalculus](LeanPML/Analysis/EnergyCalculus.lean)：实际 `Lp ℝ 2 ν`，有界可测系数的连续乘法、L² 乘积可积、积分/内积对应和真实内积路径求导。
- [WeightedL2](LeanPML/Analysis/WeightedL2.lean)：V7 (5.6) 的平方根坐标闭子空间；a.e. 零区条件、完备性、代表元独立、双向恢复、连续单射嵌入和平方范数控制、加权积分及时间求导。只需可测权重与零区/正区下界，不假设权重有界或吸收正下界。
- [SpatialCoefficients](LeanPML/PML/SpatialCoefficients.lean)：实际可测 p/r，原非负与幅度条件推出权重间隙及四耗散系数；`ofAE` 选择满足全点界的 a.e. 等价代表；分离变量构造和整个开矩形二维 Lebesgue 测度入口。
- [State](LeanPML/PML/State.lean)：瞬时场坐标、极化代数约束、真实普通/加权空间分量导数、同源两层。内部时间点使用邻域等式证明导数层坐标对应。条件性空间域未冒称已实现 Sobolev/零迹。
- [Energy](LeanPML/PML/Energy.lean)：(6.2) F_c、(6.4) E₇、(6.5) 图范数平方候选、逐项内积真实求导、单位矩形非零非恒定加权路径实例。`energy7` 固定使用论文 `scaleK` 和同源路径。
- [EnergyIntegrals](LeanPML/PML/EnergyIntegrals.lean)：旧三块密度实际可积、F_c 的积分/内积精确对应；(7.2) L² 分量耗散积分非负、全零吸收仍有 c(‖hₓ‖²+‖hᵧ‖²)；(7.7)/(7.8) D_c/D₇ 合法积分及同源定义；真实积分形式的能量求导。

完整假设、定义对应、阅读顺序和 InfoView/F12 方法集中于 [README](README.md)。现有 [定理/接口清单](docs/theorem_inventory.md)逐项追加 T10、T11、T12、T15、T17、T18 的完成范围；这些整条 PDE 条目没有整体标成完成。

本轮真正证明
$\|\psi\|_2^2\le\|X\|_2^2=\int w\psi^2$，其中 $X=\sqrt w\psi$；
以及 $F_c$ 等于旧局部密度积分，沿实际空间路径可导。导数仍是明确内积表达式 `fieldEnergyRate`，**不是** $-D_c$。$D_c,D_7$ 没有非负承诺；图范数平方候选没有未经证明的零分离或双边估计。

实例：单位开矩形上的加权平方根 seed=1，$p=1,r=0,c=4$；加权坐标路径 $X_x(t)=(t+1)\mathrm{seed}$ 对应物理 $\psi_x(t)=(t+1)/2$。实际证明成员资格、非零、真实导数及能量非恒定，并调用通用单层求导。它不声称满足空间约束或完整 PDE。

## 实际验证与保留记录

- [最终默认 lake build](logs/v0.3.1/20261013T002136_137117_lake_build.log)／[完整命令、目录、退出码](logs/v0.3.1/20261013T002136_137117_lake_build.json)：退出 0，2872 个构建任务。18 个项目模块、根入口和 Audit 均在正式导入/默认构建范围。
- [独立公理审计](logs/v0.3.1/20261013T002105_759533_axioms_audit.log)／[元数据](logs/v0.3.1/20261013T002105_759533_axioms_audit.json)：退出 0，263 条实际结果；仅标准 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx` 或自设占位公理。
- [新增定理完整索引](logs/v0.3.1/new_theorems.json)：109 个完整名、所属文件和行号，全部出现在审计结果中。Audit 顶部注释也含“#print axioms”字样，因此不能把文本行数直接当作定理数。
- [首次整体成功](logs/v0.3.1/20261013T002043_718503_lake_build.log) 后，只更新根入口的阶段说明，再得到上述最终默认构建；数学源码没有再变动。
- 真实失败包括首次导入未有 .olean、L² a.e. 函数加法需展开、当前 API 名称与类型推断、代表函数/子空间范数化简；已修复且未放宽命题。初次过量 import 拉入无关 tactic 模块，主动中断后收窄到所需固定模块；中断、后续依赖成功及所有失败日志都保留，没有升级依赖。
- PDF 首次定位预检发现页底说明与页码相交，在编辑前调整；失败与修复日志同样保留。初始 PDF 检查的运行环境问题也有原始日志，不把失败写成成功。

复现：

~~~sh
cd '/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML'
python3 scripts/run_logged.py --stage v0.3.1 lake_build lake build
python3 scripts/run_logged.py --stage v0.3.1 axioms_audit lake env lean Audit.lean
~~~

[最终交付核对](logs/v0.3.1/20261013T002703_882103_final_checks.log)退出 0；[结果 JSON](logs/v0.3.1/final_checks.json)记录导入/审计覆盖、源文件哈希、保护文件与历史保留。

## PDF、来源与视觉验收

只修改 [指定 PDF 副本](../results/V7_Maxwell_Debye_PML/V7_global_energy_副本.pdf)，实际页序与印刷页码均为 **8、9、11、12**。新增 4 个有范围的矢量红勾：

| 页 | 定位 | 本轮限定 |
|---|---|---|
| 8 | (5.6) 后嵌入结论 | 加权空间嵌入；含零区处理 |
| 9 | (6.2) | 积分/内积表示；非 PDE 能量律 |
| 11 | 加权空间时间链式法则说明 | 加权空间求导；需该空间路径可导 |
| 11 | (7.2) 的子结论 | 分量积分非负；真实梯度接口待完成 |

另有 5 处定义/历史范围说明，不加完成勾；第 12 页 (7.8) 明确区分左半实际定义与右半待完成能量律。原 18 页、可选正文、页面框与 141 项旧批注保留，当前共 150 项批注。四个修改页均重新渲染，并逐页检查新勾、字体、裁切与遮挡。没有给 (6.7)–(6.10)、(7.5)–(7.8) 的完整能量律或 (9.5)–(9.7) 打完成勾。

[新备份](logs/v0.3.1/pdf/before_v0.3.1_20261013T002329.pdf)未覆盖历史备份，修改前 SHA-256 为 `f318a9a0e4ac0721f61fffc601388e16be4e568b4efcbb3b2de3e9ad19a2b757`；最终为 `9b55183d444b9efa91e873dbbef1d7e73756962106f9c51d0de108f78b49c2ac`。

[PDF 编辑日志](logs/v0.3.1/20261013T002336_826429_pdf_annotate.log)、[重新打开/渲染日志](logs/v0.3.1/20261013T002342_329628_pdf_verify_render.log)、[机器验证](logs/v0.3.1/pdf/verification.json)和[视觉验收](logs/v0.3.1/pdf/visual_review.json)均已留档。逐项定理、输入范围与未完成接口见 [既有 PDF 标注账本](docs/pdf_formalization_marks.md)，脚本和坐标放在 [PDF 日志目录](logs/v0.3.1/pdf)。

[来源核对](logs/v0.3.1/pdf/source_review.md)：原 V7 md/tex/pdf、模型合同和固定配置与 v0.2.4 相同。路线图在本轮前仅勾选 v0.2.4 四项，已保存差异；本轮没有改路线图。§11.1 关于 (7.6)/(7.7) 的旧交叉引用疑点保留。没有静默修改数学假设。

## 未完成接口与交接

尚未构造具体矩形弱梯度、零迹、H(div)、Green/PEC、时间/空间微分交换，也未证明论文完整正则性可推出本轮所有空间路径证据。尚无两层同 primitive 方程证明、图范数零分离与双边估计、Poincaré、完整 D₇ 非负、最终能量单调性，或原八变量 PDE 解存在唯一性。

下一阶段 **v0.3.2** 的入口为本轮实际空间、`StateHasDerivAt`、`SameSourcePath`、`hasDerivAt_integral_fieldEnergy` 及 v0.2 局部块。在明确的 primitive/Green/零迹接口下，目标是推出单层和两层能量律；目标能量恒等式仍必须作为结论。本轮交接于此。

---

# 2026-10-11：v0.2.4 单层能量不是终点

用途：记录本阶段实际证明、构建/审计和带范围 PDF 标注。下方原进度完整保留，其中“当前”“下一阶段”均指历史记录当时。

**v0.2.4 已完成。** 仅实现本阶段，未进入 v0.3.1。新增 [SingleLayer.lean](LeanPML/PML/Obstructions/SingleLayer.lean) 与 [single_layer_failure.md](docs/single_layer_failure.md)，没有新增 reading_guide。已接入 [正式入口](LeanPML.lean) 与 [审计入口](Audit.lean)，更新 [README](README.md) 与 [结论登记](docs/theorem_inventory.md)。

## 数学产物和范围

命名空间 `LeanPML.PML.Obstructions`，5 个定义、20 条定理，按块组合、初值、兼容、导数、负耗散、积分和第二层排列。全部声明与输入条件见 [学习说明的索引](docs/single_layer_failure.md#9-声明索引与阅读方法)。

- (6.2)/(7.7)：直接复用电、极化和空间块组合密度，核对 μ、ε、κ 分母与 1/2。
- (2.4)/§11.1：五个初始不变量的数值为零；这是初始代数，不是完整五不变量的时间保持或全场兼容资格。
- (2.1)/§11.1：初始原方程给 dP=dE=0；另有 HasDerivAt 绑定实际函数的版本。原方程只在本组初值处化为 εE′=−P′。
- §11.1：三块初始耗散分别为 −μεcξ²、−μκcξ²、0，总计 −μc(ε+κ)ξ²；分开恒等式、非正性和 ξ≠0 时的严格负性。
- 实际积分：一般测度及整个开矩形 Ω=(x₀,x₁)×(y₀,y₁)，a.e. 支撑与平方可积给初始密度可积及精确积分；严格负还需 ∫f²>0。未用普通 f≠0 替代正积分。
- 真实局部时间：调用三块的 HasDerivAt 定理，证明初始密度导数 μc(ε+κ)ξ²；直接求二次型导数，不对单点兼容关系求导。
- 第二层：真实辅助演化初值给 l′(0)=V；独立分量支撑下 S₁=c(gₓ²+gᵧ²)，并给可积分量的实际积分式。未把 gₓ,gᵧ 命名为梯度便宣称空间接口已完成。

## 实际验证

- [最终 lake build](logs/v0.2.4/20261011T231924_138774_lake_build.log)，[命令元数据](logs/v0.2.4/20261011T231924_138774_lake_build.json)：退出 0，无编译错误/警告，2609 个构建任务。
- [独立 lake env lean Audit.lean](logs/v0.2.4/20261011T231954_467990_axioms_audit.log)，[命令元数据](logs/v0.2.4/20261011T231954_467990_axioms_audit.json)：退出 0。
- 12 个正式证明模块、根入口及 Audit 进入默认构建。原 134 条审计保留，新增 20 条，共 154 条；仅 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx` 或自设占位公理。
- 第一次检查缺少积分模块 .olean；按锁定版本 [补编译依赖](logs/v0.2.4/20261011T231148_079128_integral_dependencies.log) 成功。没有更新 Lean/mathlib/依赖锁或全局环境。
- [首轮构建](logs/v0.2.4/20261011T231659_623087_lake_build.log) 暴露两处把 a=b=0 化简误当作定义相等；[第二轮](logs/v0.2.4/20261011T231755_020287_lake_build.log) 保留函数整体改写失败。通过显式化简与逐时刻函数相等证据修复，命题未放宽。[首次成功](logs/v0.2.4/20261011T231854_493352_lake_build.log) 后清除一处无害 tactic 警告，得到上述最终成功版本。
- 原始材料、模型合同、scope、路线图及锁定配置的入场哈希见 [快照](logs/v0.2.4/before_hashes.json)；正式验收核对见 [final_checks.json](logs/v0.2.4/final_checks.json)。

## PDF 和来源核对

[目标副本](../results/V7_Maxwell_Debye_PML/V7_global_energy_副本.pdf) 只修改实际/印刷第 15 页 §11.1，增加 4 个矢量红勾与 2 处限定/交叉引用说明：初始兼容（仅点态数值）、点态初值代数、初值积分计算（平方可积；严格负须正积分）、第二层分量（梯度接口待完成）。完整 PDE 初始增长仅有条件性说明，没有完成勾。

原 18 页与 135 项旧批注/链接全部保留，当前 141 项。已重新打开、渲染并检查第 15 页，无遮挡裁切。备份为 [before_v0.2.4_20261011T232305.pdf](logs/v0.2.4/pdf/before_v0.2.4_20261011T232305.pdf)，未覆盖任何旧备份；副本最终 SHA-256 为 `f318a9a0e4ac0721f61fffc601388e16be4e568b4efcbb3b2de3e9ad19a2b757`。

[编辑日志](logs/v0.2.4/20261011T232336_537816_pdf_annotate.log)和[重新打开/渲染核验](logs/v0.2.4/20261011T232342_713491_pdf_verify_render.log)均退出 0；证据与逐项范围见 [PDF 账本](docs/pdf_formalization_marks.md)，脚本、坐标、备份哈希及视觉记录均在 [PDF 日志目录](logs/v0.2.4/pdf)。

[来源核对](logs/v0.2.4/pdf/source_review.md)：原 V7 MD/TEX/PDF 版本未变。§11.1 误将导数式引用为 (7.7)，应为 (7.6)，只记录不改原文。负耗散式没有编号，不是 §11.2 的 (11.1)。路线图在本轮前已有 v0.2.3 复选框变化但数学要求不变；本轮保持其入场版本。

## 尚缺接口与下一阶段

T34 只完成初始代数、真实局部时间和条件明确的实际积分部分；没有证明经过这组数据的完整 PDE 解存在。真实梯度/支撑、磁场/提升对应、初始端点、一般积分求导、Green/PEC、正平方积分的具体光滑数据实例、Poincaré、加权空间与两层闭合仍未完成。(6.7)–(6.10)、(7.5)–(7.8)、(9.5)–(9.7) 没有被登记为完整实现。

下一阶段 **v0.3.1**：实际内积、加权状态与能量定义，入口为计划中的 `Analysis/EnergyCalculus.lean`、`PML/State.lean`、`PML/Energy.lean`。本轮到此交接，不提前建设这些模块，不提交或推送。

---

2026-10-11 再次调整阅读注释：保留公式、出处和符号对应，在关键 `have` 旁补充求导、导数值改写、零区常值及二维合并的理由；简单实例仍保持简短。只修改注释及一处换行，没有改变定义、假设或证明内容。[变更核对](logs/v0.2.3/comments_readable_20261011T214656/comment_only_check.json)；[实际构建及默认审计](logs/v0.2.3/20261011T214957_195523_readable_comments_build.log)退出 0，134 条审计无 sorryAx。以下保留前两次注释调整的历史记录。

2026-10-11 后续调整：按用户偏好，将 LocalSpatial 主要注释压至 1–4 行，保留公式、出处和必要条件；文件由 787 行缩至 484 行，证明代码逐字不变。[构建及默认审计通过](logs/v0.2.3/20261011T214335_015307_shortened_comments_build.log)，[变更核对](logs/v0.2.3/comments_short_20261011T214308/check.json)。

# 2026-10-11：v0.2.3 注释阅读改进

按用户要求，在 [LocalSpatial.lean](LeanPML/PML/LocalSpatial.lean) 全部 31 个定义/定理的注释中补充对应 PDF 的直接数学公式、实际页码、纸面符号与 Lean 参数的映射，区分原式、局部密度、推论和教学实例。重点展开 (7.1) 完整求导链、零区公式及 (7.2) 积分式与点态密度的差别。

本次没有新增数学结果。去掉注释后，定义、假设和证明代码与修改前逐字一致，见 [仅注释变更检查](logs/v0.2.3/20261011T212242_049381_comments_only_check.log)；[修改前源码](logs/v0.2.3/comments_20261011T211945/before_LocalSpatial.lean)保留。PDF、原始材料、工具链和依赖未改。

实际 [默认构建](logs/v0.2.3/20261011T212242_143462_comments_lake_build.log) 和 [独立审计](logs/v0.2.3/20261011T212322_994625_comments_axioms_audit.log) 都退出 0，全部 134 条审计通过，无 sorryAx，仅有原来的标准基础公理。历史日志及历史文件哈希保留，不用新注释覆盖旧快照；当前源码新哈希见 [注释检查记录](logs/v0.2.3/comments_20261011T211945/comment_only_check.json)。

---

# LeanPML 当前进度：v0.2.3

用途：记录“空间块与退化区”的实际证明、中文学习材料、真实构建审计以及 PDF 标注证据。日期：2026-10-10（Asia/Shanghai）。下方完整保留旧 PROGRESS，历史中的“当前”和“下一阶段”只指当时的状态。

**v0.2.3 已完成：数学任务、正式构建、公理审计、中文说明、PDF 标注、视觉验收和末次文件核对均通过。** 本轮没有实现 v0.2.4。

## 新产物与数学结论

- [LocalSpatial.lean](LeanPML/PML/LocalSpatial.lean)：6 个定义、25 条定理，全部进入正式导入和审计。其中 4 个密度定义、15 条核心定理；2 个路径定义、10 条实例定理。
- [阅读指南](docs/v0.2.3_reading_guide.md)：论文到 Lean 对应、假设、正/零分支、方向次序、真实求导、InfoView 及准确 mathlib 源码位置。
- [LeanPML.lean](LeanPML.lean) 接入模块；[Audit.lean](Audit.lean) 完整保留旧 109 条，再增加全部 25 条，共 134 条。
- [README](README.md) 更新本阶段入口；旧 README、PROGRESS、入口、审计与路线图快照存于 [阶段日志](logs/v0.2.3)。
- [PDF 标注账本](docs/pdf_formalization_marks.md)：逐项登记当前源码、完整定理名、页码、旧勾保留、新增范围、未完成接口和本次证据。

本文件所有新定理均位于 `LeanPML.PML`。$h,l$ 是实际时间函数，$V$ 是由 `HasDerivAt h V t` 绑定的真实导数值，$f$ 直接取 $l-h$。吸收是固定空间点的值，时间不变，不要求全空间为常数。

| 声明 | 来源、假设及结论 |
|---|---|
| `spatialEnergy`、`spatialEnergy2D` | (5.5)、(6.2)、(7.1)；含 $1/2$，空间部分不额外乘 $\mu$，未作积分 |
| `spatialDissipation`、`spatialDissipation2D` | (7.2) 的点态分支密度；零区独立为 $ch_i^2$ |
| `spatial_weight_balance` | $a>0$ → $\sigma_j+aw_i=c$；先给出 $a\ne0$ 再消分母 |
| `spatial_rate_identity` | (7.1) 实数代数；调用平衡式，继而由真实求导调用 |
| `hasDerivAt_spatialAuxiliary` | 原始 $h'=V,l'=V+\sigma_jh-\sigma_i l$ → $(l-h)'=\sigma_jh-\sigma_i l$ |
| `hasDerivAt_spatialEnergy_pos` | 上述真实导数、$a>0$ → 正区能量真实导数；不假设目标公式 |
| `hasDerivAt_zeroSpatialComponent`、`hasDerivAt_zeroSpatial2D` | (7.1) 后未编号公式；真实 $h_i'=V_i$ → 一/两个时间分量的平方能量导数 |
| `zeroSpatial_compatibility_preserved` | §5.2 零区保持句；非负吸收、$a=0$、$T\ge0$、$h,l$ 闭区间连续、内部真实辅助演化、仅初始 $l(0)=h(0)$ → 整段 $l=h$ |
| `hasDerivAt_spatialEnergy_zero` | 非负吸收、$a=0$、$l$ 的真实演化和当前 $l(t)=h(t)$ → 分支能量导数；没有对单点兼容求导 |
| `hasDerivAt_spatialEnergy` | 非负吸收、两份真实导数、仅当 $a=0$ 要求兼容 → 两分支统一结论 |
| `spatialDissipation_nonneg`、`spatialDissipation2D_nonneg` | $c>0$、$0\le p,r\le S\le c/4$ → 点态非负；实际调用 v0.2.1 系数界 |
| `spatialDissipation2D_of_sum_zero` | $a=0$ → 零区密度等于 $c(h_x^2+h_y^2)$ |
| `energyWeightX_swap`、`spatialEnergy2D_eq_sum` | (5.5)、(6.2) 推出的方向映射与能量分解；由二维求导调用 |
| `hasDerivAt_spatialEnergy2D` | 两方向的四份真实导数、非负吸收及条件化零区兼容 → 二维时间结论，保留全部耦合项 |

最高局部时间结论为

$$
F_{\mathrm{sp}}'
=(V_x+ch_x)l_x+(V_y+ch_y)l_y-D_{\mathrm{sp}}.
$$

点态非负不等于单独空间块单调，耦合项仍需后续主方程和 Green 公式处理。原材料不一致处没有通过增加假设掩盖；本轮没有对 $w_i,p,r$ 作空间求导，没有吸收正下界。

## 零区、方向和实例

$x$ 方向 $(\sigma_i,\sigma_j)=(p,r)$，$y$ 方向 $(r,p)$；$l_i^2$ 系数使用本方向吸收，$h_i^2$ 使用另一方向吸收。正式代码显式复用 `energyWeightY` 并证明交换映射，避免仅以名称暗示方向。

$p=r=0$ 只推出辅助量导数为零。零初值兼容及闭区间连续/内部演化才推出整段 $f=0$。复用 `Time.eq_initial_of_hasDerivAt_zero` 处理端点和 $T=0$，没有额外要求端点双侧导数或全实轴 ODE。局部零区求导只在导数数值中使用当前 $l=h$，没有把单点关系拿去求导。

四条正式密度实例：

| 定理 | 参数 $c=4,S=1$ | 精确结果 |
|---|---|---|
| `spatial_zero_absorption_example` | $p=r=0$ | $4h_x^2+4h_y^2$ |
| `spatial_x_layer_example` | $p=1,r=0$ | $5l_x^2+3h_y^2$ |
| `spatial_y_layer_example` | $p=0,r=1$ | $3h_x^2+5l_y^2$ |
| `spatial_corner_example` | $p=r=1$ | $\frac52(l_x^2+l_y^2)+\frac32(h_x^2+h_y^2)$ |

它们验证局部幅度条件并调用一般非负定理，不宣称这些数值对任意材料满足全部阈值。

两条非零光滑时间路径各包含定义、真实导数、一般定理调用和非零初值：

- `spatialDecayPath`、`hasDerivAt_spatialDecayPath`、`hasDerivAt_spatial_positive_path`、`spatial_positive_path_initial`：$h=0,l=e^{-t}$，正区导数为 $-5e^{-2t}$，初始 $l=1,F=5/2$。
- `spatialLinearPath`、`hasDerivAt_spatialLinearPath`、`hasDerivAt_spatial_zero_path`、`spatial_zero_path_initial`：两方向 $h_i=l_i=t+1$，零区导数 $2(t+1)$，初始分量和二维能量为 1。

这些是局部时间路径，未验证完整 PDE 解或解的存在唯一性。

## 真实构建、公理审计和失败保留

Lean `v4.31.0`（`68218e876d2a38b1985b8590fff244a83c321783`）、Lake `5.0.0-src+68218e8`、mathlib `v4.31.0`（`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`）保持固定。本阶段未安装/更新依赖，未改其他工程、全局工具链或 Lake 包元数据。

所有下表命令都由原 `scripts/run_logged.py --stage v0.2.3` 在工程根目录执行；LOG 是完整 stdout/stderr，同名 JSON 含命令、实际工作目录、退出码、起止时间。表中的短标签不是用来替代元数据里的真实命令。

| 实际记录 / 命令标签 | 退出码 | 完整输出与元数据 |
|---|---:|---|
| input_snapshot | 0 | [LOG](logs/v0.2.3/20261010T232231_591743_input_snapshot.log)／[JSON](logs/v0.2.3/20261010T232231_591743_input_snapshot.json) |
| pdf_inspect | 0 | [LOG](logs/v0.2.3/20261010T232231_714148_pdf_inspect.log)／[JSON](logs/v0.2.3/20261010T232231_714148_pdf_inspect.json) |
| lake env lean --version | 0 | [LOG](logs/v0.2.3/20261010T232330_615307_lean_version.log)／[JSON](logs/v0.2.3/20261010T232330_615307_lean_version.json) |
| lake_version | 0 | [LOG](logs/v0.2.3/20261010T232330_615308_lake_version.log)／[JSON](logs/v0.2.3/20261010T232330_615308_lake_version.json) |
| lake env lean LeanPML/PML/LocalSpatial.lean | 1 | [LOG](logs/v0.2.3/20261010T232350_473950_spatial_core_check.log)／[JSON](logs/v0.2.3/20261010T232350_473950_spatial_core_check.json) |
| lake env lean logs/v0.2.3/spatial_path_derivatives_check.lean | 0 | [LOG](logs/v0.2.3/20261010T232351_036683_path_derivatives_check.log)／[JSON](logs/v0.2.3/20261010T232351_036683_path_derivatives_check.json) |
| lake build LeanPML.PML.LocalSpatial | 1 | [LOG](logs/v0.2.3/20261010T232505_118419_spatial_core_check.log)／[JSON](logs/v0.2.3/20261010T232505_118419_spatial_core_check.json) |
| lake build LeanPML.PML.LocalSpatial | 0 | [LOG](logs/v0.2.3/20261010T232537_821679_spatial_core_check.log)／[JSON](logs/v0.2.3/20261010T232537_821679_spatial_core_check.json) |
| lake env lean logs/v0.2.3/spatial_examples_check.lean | 1 | [LOG](logs/v0.2.3/20261010T232603_895787_spatial_examples_check.log)／[JSON](logs/v0.2.3/20261010T232603_895787_spatial_examples_check.json) |
| lake env lean logs/v0.2.3/spatial_examples_check.lean | 0 | [LOG](logs/v0.2.3/20261010T232630_563186_spatial_examples_check.log)／[JSON](logs/v0.2.3/20261010T232630_563186_spatial_examples_check.json) |
| lake build | 1 | [LOG](logs/v0.2.3/20261010T232847_164311_lake_build.log)／[JSON](logs/v0.2.3/20261010T232847_164311_lake_build.json) |
| lake env lean Audit.lean | 1 | [LOG](logs/v0.2.3/20261010T232859_298331_axioms_audit.log)／[JSON](logs/v0.2.3/20261010T232859_298331_axioms_audit.json) |
| lake build | 0 | [LOG](logs/v0.2.3/20261010T232910_472603_lake_build_retry.log)／[JSON](logs/v0.2.3/20261010T232910_472603_lake_build_retry.json) |
| lake env lean Audit.lean | 0 | [LOG](logs/v0.2.3/20261010T232931_121820_axioms_audit_retry.log)／[JSON](logs/v0.2.3/20261010T232931_121820_axioms_audit_retry.json) |
| pdf_evidence_plan | 0 | [LOG](logs/v0.2.3/20261010T233059_003288_pdf_evidence_plan.log)／[JSON](logs/v0.2.3/20261010T233059_003288_pdf_evidence_plan.json) |
| pdf_ledger | 0 | [LOG](logs/v0.2.3/20261010T233318_014924_pdf_ledger.log)／[JSON](logs/v0.2.3/20261010T233318_014924_pdf_ledger.json) |
| pdf_operation_marker | 0 | [LOG](logs/v0.2.3/20261010T233326_737482_pdf_operation_marker.log)／[JSON](logs/v0.2.3/20261010T233326_737482_pdf_operation_marker.json) |
| pdf_annotate | 1 | [LOG](logs/v0.2.3/20261010T233326_922813_pdf_annotate.log)／[JSON](logs/v0.2.3/20261010T233326_922813_pdf_annotate.json) |
| pdf_annotate_retry | 0 | [LOG](logs/v0.2.3/20261010T233406_456228_pdf_annotate_retry.log)／[JSON](logs/v0.2.3/20261010T233406_456228_pdf_annotate_retry.json) |
| pdf_verify_render | 0 | [LOG](logs/v0.2.3/20261010T233406_716661_pdf_verify_render.log)／[JSON](logs/v0.2.3/20261010T233406_716661_pdf_verify_render.json) |
| pdf_visual_qa | 0 | [LOG](logs/v0.2.3/20261010T233454_140775_pdf_visual_qa.log)／[JSON](logs/v0.2.3/20261010T233454_140775_pdf_visual_qa.json) |

真实失败及修复：

1. 核心初稿中的函数和表达式与 lambda 目标形状不一致，且中间版本用了不存在的 `mul_eq_mul_right`。最终先给出显式函数类型，用合法的 `eq_div_iff` 与分母非零证据处理代数；没有放宽恒等式或增加目标假设。
2. 实例首轮在 `norm_num` 已结束目标后多写了一条 `ring`，删除多余步骤后通过。
3. 根入口整合时把新 `import` 放在模块说明之后，Lean 报“import 必须位于文件开头”；那次独立审计也因根模块产物缺失而失败。移入顶部导入区域后，默认构建与独立审计都重跑通过。旧审计没有删减。
4. PDF 首次编辑已经完成文字/批注核对并写入目标，但在随后统计旧批注数量时遇到 pypdf 的间接对象 `len` 错误。修复统计取值；重试识别到同一计划已写入，直接跳过，未重复画勾。随后独立重新打开目标、核对全部页面、渲染和视觉验收均通过。首次失败输出未覆盖。

最终默认构建输出 `Build completed successfully (2122 jobs).`，覆盖 11 个正式模块和两个入口。全部 134 条定理的独立公理输出均只含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx` 或自定义占位公理。标准基础依赖不等于未完成证明。

## PDF 标注与验收

只修改指定的 `V7_global_energy_副本.pdf`。原 PDF、MD、TEX、旧“标注前备份”和用户原有 126 个批注/链接全部保留。新备份为 [before_v0.2.3_20261010T232231.pdf](logs/v0.2.3/pdf/before_v0.2.3_20261010T232231.pdf)，哈希在 [backup.json](logs/v0.2.3/pdf/backup.json)。

[账本](docs/pdf_formalization_marks.md)逐项重新核对已有 16 处标记，并登记 4 个新红勾：第 8 页未编号零区时间保持，第 10 页 (7.1) 正区和后续零区公式，第 11 页 (7.2) 点态子表达式。实际页序号与印刷页码一致。第 1 页加图例，第 7/8 页限定旧 (5.3)/(5.5) 勾只指阈值等价/零分支计算，第 11 页给旧 (7.3)/(7.4) 旁注补“积分待完成”。

红勾以矢量线条绘制，中文字体嵌入；没有重排文档。修改页 1、7、8、10、11 均重新渲染并逐页检查，标记可见、没有裁切或覆盖。机器辅助核验也确认：标记矩形之外像素完全不变，其余 13 页内容流未变，全部 18 页原可选文本保留。[完整视觉与内容核验](logs/v0.2.3/pdf/verification.json)保存最终哈希和每页记录。

[定位计划](logs/v0.2.3/pdf/annotation_plan.json)、[编辑脚本](logs/v0.2.3/pdf/annotate_pdf.py)及稳定标记 ID 保留，重跑同一计划不会重复叠加。PDF 图例和账本明确：定义/假设不是证明，局部时间不等于空间/PDE。

## 来源版本和历史清单增量

V7 MD 哈希仍为 `0a7f73a25cb119eeb75b3e7b3c3f2fbb3b319250f3354ed4dcad0ecff8eff4fb`，与清单和上一阶段相同。本次对照 (5.5)、(6.1)–(6.2)、(7.1)–(7.2) 及零区未编号公式，未发现需要调整已接受假设的差异。

路线图当前哈希 `5b19f2895a88184b71ffa9da4a49d0c1888d99906f9bd5bd64e3450ba3b78f06`，上一阶段输入为 `77364bd8edd1c12feef48b8f6688faa379f62a7caa742baba0cbe41032d51f90`。[已有差异](logs/v0.2.3/roadmap_preexisting_diff.patch)仅为 v0.2.2 第 545–548 行四个勾选框变为完成，文字“待实现”仍保留；数学任务未变。本轮不改路线图，阶段状态以当前 PROGRESS 为准。

[输入快照](logs/v0.2.3/input_hashes.json)登记 194 项保护文件：既有正式模块、历史清单/合同/范围、旧日志、原材料、配置和既有 PDF 备份。旧源码未作无关重构，历史账本不覆盖。

| 清单条目 | 本轮增量 | 仍未完成 |
|---|---|---|
| T15，(7.1) | 权重平衡、代数恒等式、真实时间平方求导、两方向合成 | 真正梯度/通量场、混合导数交换、可测可积及积分求导 |
| T15，零区 | 独立一/二维公式、兼容初值的时间保持、保留 $c|\nabla v|^2$ 的时间分量密度 | 原 PDE 兼容解类到这些路径的接口 |
| T15，(7.2) | 分支点态耗散、零区值和非负性，复用系数界 | 完整空间积分、加权路径规则、Green/PEC；**整个 T15 未标完成** |
| T13、T14、T19 | 未扩大 v0.2.2 范围；本次重新构建与审计旧结果以支持 PDF 旧勾 | 空间能量与范数接口仍待完成 |
| T02–T04 | 不因零区兼容保持而宣称磁不变量或完整等价完成 | 两个磁辅助不变量、提升构造和原八变量对应 |

未给 (6.7)–(6.10)、(7.5)–(7.8)、(9.5)–(9.7) 添加整体完成红勾。模型合同和历史 theorem_inventory 保持原样，本表只登记精确增量。

## 学习、复现和下一阶段

建议先读指南，再读 `hasDerivAt_spatialEnergy_pos`、`zeroSpatial_compatibility_preserved`、`hasDerivAt_spatialEnergy2D`。在 VS Code 用 `Lean 4: InfoView: Display Goal`，把光标放到具名 `have` 和 `calc` 前后看目标；F12 查看 mathlib。导入刷新使用保存、构建、`Lean 4: Server: Restart File`。

~~~sh
cd '/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML'
python3 scripts/run_logged.py --stage v0.2.3 lake_build lake build
python3 scripts/run_logged.py --stage v0.2.3 axioms_audit lake env lean Audit.lean
~~~

下一阶段仅为 **v0.2.4：单层能量不是终点**，入口计划是 `PML/Obstructions/SingleLayer.lean` 与 `docs/single_layer_failure.md`。对照 (6.2)、(7.7)、§11.1，核验特殊初始数据的单层耗散计算，并把初始导数计算与解存在性分开，再说明第二层通过 $\lambda_t(0)=\nabla f$ 提供的控制。本轮未创建这些产物，未提交或推送远端。

## 最终验收

**v0.2.3 已达到验收标准。** 本阶段全部数学任务、非零真实路径、可读性说明、默认构建、公理审计、PDF 逐项证据与视觉验收均已完成；交接于此，不进入 v0.2.4。

[末次检查成功输出](logs/v0.2.3/20261010T233915_169415_final_checks_retry.log)／[命令、目录与退出码](logs/v0.2.3/20261010T233915_169415_final_checks_retry.json)，退出 0。检查覆盖 194 项保护文件、旧历史全文、11 个模块与两个入口、134 条定理和审计逐项对应、9 个锁定依赖、文档链接与数学分隔、12 项 mathlib 源码位置以及最终 PDF/账本/源码证据一致性。

[首次末次检查日志](logs/v0.2.3/20261010T233856_282495_final_checks.log)退出 1：检查脚本将数学记号 $\mathcal D_c[U_0](0)$ 误识别为 Markdown 链接，找不到名为 `0` 的文件。修复为先排除数学区再扫描链接，重试通过；没有修改数学证明或放宽验收条件。

[检查脚本](logs/v0.2.3/final_checks.py)与[交付哈希](logs/v0.2.3/verified_artifact_hashes.json)保留。哈希覆盖代码、README、阅读指南、PDF 账本、固定配置、最终 PDF 与标注证据；本段最后完成登记不纳入其自身哈希。

---

以下完整保留此前进度记录。

# LeanPML 当前进度：v0.2.2

用途：记录“电块与极化块：代数层和求导层分开”的数学范围、正式实现、学习说明和真实验证。日期：2026-10-10（Asia/Shanghai）。下方保留此前 PROGRESS 全文；历史中的“当前”“下一阶段”仅指当时的阶段。

**v0.2.2 已完成：全部本阶段数学任务、中文学习说明、默认构建、公理审计及末次文件核对均已通过。** 本轮没有进入 v0.2.3。

## 新文件与实际结论

- [LocalElectric.lean](LeanPML/PML/LocalElectric.lean)：3 个定义、6 条定理；V7 (7.3) 的数值恒等式、真实二阶时间路径求导及非零实例。
- [LocalDebye.lean](LeanPML/PML/LocalDebye.lean)：6 个定义、12 条定理；(6.1) 兼容关系求导、(7.4) 真实求导、(8.1) 消元、(8.2) 全部四组系数界及非零实例。
- [v0.2.2 阅读指南](docs/v0.2.2_reading_guide.md)：纸面公式、Lean 声明、假设用途、关键证明及 mathlib 源码位置。
- [LeanPML.lean](LeanPML.lean) 新增两个导入；[Audit.lean](Audit.lean) 保留旧 91 条审计，新增全部 18 条，合计 109 条。
- [README.md](README.md) 更新工程入口、阅读顺序和命令。旧 README、PROGRESS、两个入口与路线图快照保存在 [本阶段日志目录](logs/v0.2.2)。

固定空间点的系数可以随空间变化，但在当前时间求导中不依赖时间。没有吸收正下界，没有除以 $a$ 或 $b$。纯恒等式不强加物理正性；系数估计则明确输入正性和小量条件。$C_P$ 仍是给定正参数，不是本阶段新证明的空间不等式。

## 定义、定理、输入及调用关系

所有新增声明均在 `LeanPML.PML` 命名空间。

| 正式声明 | 数学含义、假设及依赖 |
|---|---|
| `electricEnergy`、`electricRemainder`、`electricEnergyAlong` | (7.3) 的 $F_e,D_e$ 及沿真实函数的定义；$F_e$ 带 $\epsilon/2$，速度槽明确使用 `deriv v` |
| `electric_rate_identity` | 任意实数下的形式求导数值恒等式；由下一条调用，没有独立宣称可导 |
| `hasDerivAt_electricEnergyAlong` | 一阶 `HasDerivAt v vDot t`、二阶 `HasDerivAt (deriv v) vDDot t` → $F_e'=\epsilon(v_{tt}+av_t+bv)(v_t+cv)-D_e$；逐项调用 mathlib 求导规则，再调用代数引理 |
| `deriv_exampleU`、`hasDerivAt_deriv_exampleU` | 先由已有真实导数证据证明整个导数函数等于指数函数，再对该函数求导；单点速度等式没有被用来冒充二阶导数 |
| `hasDerivAt_electricEnergyAlong_exampleU`、`deriv_exampleU_zero` | 一般电块定理的非零实际路径调用；初始真实速度为 1 |
| `polarQuadratic`、`polarEnergy`、`polarRemainder`、`polarEnergyAlong` | (6.2)/(7.4) 的 $Q,F_D=Q/(2\kappa),D_D$ 及真实路径；不是 v0.1.2 教学 Debye 能量 |
| `polarCoeffAR`、`polarCoeffG` | (8.1) 的 $A_R,G$；$A_R$ 不是材料 $A=\epsilon+2\kappa$ |
| `polar_constraint_derivative` | $v',R',z'=R$ 的真实证据，加邻域兼容 → $\kappa v_t=R+\tau R_t$；用邻域换函数与导数唯一性，不需要参数正性 |
| `polar_shifted_constraint` | 调用上一条并取邻域兼容在点上的值 → $\kappa(v_t+cv)=\tau R_t+(1+c\tau)R+cz$ |
| `polar_rate_algebra` | $\kappa\ne0$ 和已求导约束的数值形式 → 代数率恒等式；供上层求导调用，先提供非零证据再消分母 |
| `hasDerivAt_polarQuadratic` | $R',z'=R$ → $Q$ 的平方、交叉项逐项真实求导；不需要兼容或材料正性 |
| `hasDerivAt_polarEnergy` | 三份导数证据、邻域兼容、$\kappa\ne0$ → $F_D'=(R_t+aR+bz)(v_t+cv)-D_D$；调用约束和代数层 |
| `hasDerivAt_polarEnergy_on_Ioo` | $t\in(0,T)$，兼容只在 $(0,T)$ 内成立 → 上述局部求导；开集给出邻域，不增加端点或全实轴条件 |
| `polarQuadratic_eq_reduced` | 单点 $z+\tau R=\kappa v$ → (8.1) 的精确 $Q$ 消元；这里没有求导，所以不需要邻域 |
| `polarEnergy_eq_reduced` | 调用 $Q$ 消元、除以 $2\kappa$ 得 $F_D$ 表达式；等式两边使用 Lean 实数除法，恒等式本身不需 $\kappa\ne0$；物理解释仍为 $\kappa>0$ |
| `polar_coefficients_bounds_of_local_conditions` | 明确列出 $a,b\ge0,c,\tau>0,a\le c/2,b\le c^2/16,ac-b\ge0,c\tau\le1/4$ → 全部 (8.2) |
| `polar_coefficients_bounds_of_threshold` | 原材料正性、$0<c\le c_*$、$0\le p,r\le S\le c/4$ → 调用旧吸收界、`c_mul_tau_bounds` 和前一条；后者内部使用 `le_threshold_iff_explicit` |
| `example_polar_path_compatible`、`hasDerivAt_example_polarEnergy` | 非零指数路径的真实兼容及一般极化块求导定理的实际调用 |

(8.1) 准确重写的是 $Q$：

$$
Q=A_RR^2+2\kappa c(1-a\tau-b\tau^2)vR+\kappa^2Gv^2.
$$

(8.2) 的结论保留为

$$
\frac34\le A_R\le\frac54,\quad
0\le1-a\tau-b\tau^2\le1,\quad
0\le G\le\frac{37}{64}c^2,\quad
0\le b+ac\le\frac9{16}c^2.
$$

证明将关键中间量显式命名：$a\tau\le1/8$、$b\tau^2\le1/256$、$ac\tau^2\le1/32$、$bc\tau^3\le1/1024$。最高入口未把这些中间结果当作独立原始假设；没有放宽论文常数。

余项 $D_e,D_D$ 可能为负。完整 (6.2) 中这两块分别贡献 $\int_\Omega\mu F_e$、$\int_\Omega\mu F_D$；本轮没有进行该空间积分，也没有由局部等式推出能量正定或单调。

## 非零路径与旧工作的衔接

取 $\kappa=\tau=1$，

$$
v(t)=\frac{1-e^{-2t}}2,\quad R(t)=-e^{-2t},\quad z(t)=\frac{1+e^{-2t}}2.
$$

旧 v0.1.2–v0.1.3 提供实际函数及 $v_t=e^{-2t},R_t=2e^{-2t},z_t=R$ 的真实证据。本轮补充整个 `deriv exampleU` 的等式，再得到真实二阶导数；两块实例各自调用一般求导定理。兼容关系先按实际函数验证，随后提升为邻域相等，未跳过一般定理。

已有 `example_nonzero_initial` 给 $R(0)=-1$；本轮另证 $v_t(0)=1$。该指数路径具有所需真实导数，故不是零函数的代数代入。它是局部时间路径实例，未验证完整二维 PDE、边界或空间正则性。

对 $U_0$，本轮的 $v,R,z$ 对应 $u,P,q$，兼容关系对应 v0.1.3 的时间保持结论。本轮开区间入口可以接收其限制到内部的关系；一般函数空间版本、原八变量到 primitive 的连接仍未实现。本轮没有输入教学方程 $\epsilon E'=-P'$。

## 实际构建与公理审计

工具链固定：Lean `v4.31.0`，提交 `68218e876d2a38b1985b8590fff244a83c321783`；Lake `5.0.0-src+68218e8`；mathlib `v4.31.0`，提交 `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`。未更新依赖、全局默认工具链或包元数据。

所有命令通过原 `scripts/run_logged.py --stage v0.2.2 标签 命令…` 从工程根目录运行：

~~~text
/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML
~~~

LOG 保留实际 stdout/stderr；同名 JSON 保留完整命令、工作目录、实际程序路径、退出码和执行时间。

| 实际命令 | 退出码 | 完整输出／元数据 |
|---|---:|---|
| 输入哈希及快照脚本 | 0 | [LOG](logs/v0.2.2/20261010T185337_475327_input_snapshot.log)／[JSON](logs/v0.2.2/20261010T185337_475327_input_snapshot.json) |
| `lake env lean --version` | 0 | [LOG](logs/v0.2.2/20261010T185519_661138_lean_version.log)／[JSON](logs/v0.2.2/20261010T185519_661138_lean_version.json) |
| `lake --version` | 0 | [LOG](logs/v0.2.2/20261010T185519_661137_lake_version.log)／[JSON](logs/v0.2.2/20261010T185519_661137_lake_version.json) |
| `lake env lean LeanPML/PML/LocalElectric.lean`，首轮 | 1 | [LOG](logs/v0.2.2/20261010T185417_628876_electric_check.log)／[JSON](logs/v0.2.2/20261010T185417_628876_electric_check.json) |
| 同上，修复重试 | 0 | [LOG](logs/v0.2.2/20261010T185446_670197_electric_check_retry.log)／[JSON](logs/v0.2.2/20261010T185446_670197_electric_check_retry.json) |
| `lake build LeanPML.PML.LocalElectric` | 0 | [LOG](logs/v0.2.2/20261010T185455_983903_electric_build.log)／[JSON](logs/v0.2.2/20261010T185455_983903_electric_build.json) |
| `lake env lean logs/v0.2.2/coeff_bounds_check.lean` | 0 | [LOG](logs/v0.2.2/20261010T185441_222604_coeff_bounds_check.log)／[JSON](logs/v0.2.2/20261010T185441_222604_coeff_bounds_check.json) |
| `lake env lean LeanPML/PML/LocalDebye.lean`，首轮 | 1 | [LOG](logs/v0.2.2/20261010T185507_232464_debye_check.log)／[JSON](logs/v0.2.2/20261010T185507_232464_debye_check.json) |
| 同上，修复重试 | 0 | [LOG](logs/v0.2.2/20261010T185532_505132_debye_check_retry.log)／[JSON](logs/v0.2.2/20261010T185532_505132_debye_check_retry.json) |
| `lake build LeanPML.PML.LocalDebye`，核心初版 | 0 | [LOG](logs/v0.2.2/20261010T185551_496522_debye_module_build.log)／[JSON](logs/v0.2.2/20261010T185551_496522_debye_module_build.json) |
| `lake build`，整合最终正式模块 | 0 | [LOG](logs/v0.2.2/20261010T185648_883655_lake_build.log)／[JSON](logs/v0.2.2/20261010T185648_883655_lake_build.json) |
| `lake env lean Audit.lean` | 0 | [LOG](logs/v0.2.2/20261010T185707_307274_axioms_audit.log)／[JSON](logs/v0.2.2/20261010T185707_307274_axioms_audit.json) |

真实失败与修复：

- 电块首轮的 `pow` 搭配 `simpa` 遇到函数幂、lambda 与目标表达式匹配问题；改为从求导证据用 `congr_deriv` 整理导数值后通过，没有改动数学结论。
- 极化块首轮需显式调用 `Filter.EventuallyEq.symm`、`Filter.EventuallyEq.eq_of_nhds`，并区分函数括号的逐点改写和导数值的代数整理；修复后通过；同时将一次多余的 `<;>` 改为顺序 tactic，消除风格警告，没有关闭 linter。初始错误与警告全文未覆盖。
- 系数界先在日志目录独立检查，再将同一证明合入正式 LocalDebye；草稿只保留为过程证据，正式入口不导入日志目录。
- 整合时为极化二次型四个关键 `have`、函数改写 `hQ`、能量求导 `henergy` 添加明确命题类型，便于逐步查看 InfoView；随后实际运行默认构建。
- 默认构建输出 `Build completed successfully (2121 jobs).`，重新构建两个新模块、根入口和 Audit，覆盖全部 10 个正式模块。
- 独立审计全部 109 条输出均只有 `propext`、`Classical.choice`、`Quot.sound`；无 `sorryAx` 或自定义占位公理。三者为标准基础依赖，不是待填证明的借口，也不宣称“没有任何公理”。

## 来源、历史与清单增量

V7 正文哈希仍为 `0a7f73a25cb119eeb75b3e7b3c3f2fbb3b319250f3354ed4dcad0ecff8eff4fb`，与来源清单及 v0.2.1 快照一致。本轮重新对照 (6.1)、(6.2)、(7.3)、(7.4)、(8.1)、(8.2)，未发现这些公式的确定符号或常数冲突；此判断不是完整 V7 独立审稿结论。

路线图本轮开始时哈希为 `77364bd8edd1c12feef48b8f6688faa379f62a7caa742baba0cbe41032d51f90`，此前 v0.2.1 快照为 `521bbb4fcad5d64159726f47ac2a694d282dbd0fc637ff025eaa0718fdffd63d`。[已保存的原有差异](logs/v0.2.2/roadmap_preexisting_diff.patch)仅是第 531–534 行 v0.2.1 四项复选框从未完成改为完成；第 508 行的“待实现”仍保留。v0.2.2 数学任务没有变化。本轮不改路线图，阶段完成状态以本进度为准。

[输入快照](logs/v0.2.2/input_hashes.json)登记 149 项保护文件，包括 V7、合同、历史清单、旧代码、日志和配置。旧源码没有重构；修改前入口、README、PROGRESS 保留为本阶段快照。原 theorem_inventory 保留其历史“计划”文字，增量状态逐项登记如下：

| 条目 | 本轮实际完成 | 尚未完成 |
|---|---|---|
| T13，(7.3) | 数值恒等式、实际时间路径与真实二阶导数的局部求导 | 空间函数路径、可积性、积分求导及 PDE 接入 |
| T14，(7.4) | 邻域兼容的真实求导、极化块实际求导、开区间入口 | 场层兼容与时间导数接口、空间积分；不等于完成全部条目 |
| T19，(8.1)–(8.2) | 固定点约束消元、原阈值入口及全部系数上下界 | 将点态结果用于空间能量估计的后续接口；未证明 T20 正定性 |

关于“单点兼容不能直接求导”的语义要求已落实为邻域/开区间输入；关于 $Q,F_D,\mu$ 的因子区别已落实为独立定义。未新增磁场约束，未删除零吸收，未将余项非负或目标能量恒等式塞入假设。

## 阅读、复现与下一阶段

建议先读 [学习指南](docs/v0.2.2_reading_guide.md)，再读 `hasDerivAt_electricEnergyAlong`、`polar_constraint_derivative`、`polar_coefficients_bounds_of_threshold`，然后顺着调用读 Debye 求导、约束消元、实例与审计。

在 VS Code 打开工程根目录，通过 `Lean 4: InfoView: Display Goal` 查看每一步；光标逐行经过 `have`/`calc`/`apply`/`rw`，悬停看类型、F12 看来源。新增导入后先构建，再用 `Lean 4: Server: Restart File` 刷新文件。

~~~sh
cd '/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML'
python3 scripts/run_logged.py --stage v0.2.2 lake_build lake build
python3 scripts/run_logged.py --stage v0.2.2 axioms_audit lake env lean Audit.lean
~~~

下一阶段 **v0.2.3：空间块与退化区**，计划建立 `PML/LocalSpatial.lean`，核验 V7 (7.1)–(7.2)。取 $h=\partial_i v,l=\Lambda_i,f=l-h$，分别处理正吸收与零吸收；零区须保留 $c|\nabla v|^2$，局部通量不能直接设为零。实际梯度与时间微分交换仍由后续空间分析兑现。本轮没有建立该模块。

完整二维主定理还需要空间块、真实场空间和加权积分、Green/PEC、Poincaré、图范数控制、两层耗散闭合以及原系统与 primitive 的对应。本阶段也没有证明一般解存在唯一性或严格递减。

## 最终验收

**v0.2.2 已达到验收标准。** 两块真实求导、(8.1) 消元、(8.2) 四组界、原阈值入口、非零实际路径、中文说明均完成，并通过真实默认构建和独立公理审计。

末次文件与记录检查：[成功输出](logs/v0.2.2/20261010T190231_231494_final_checks_retry.log)／[完整命令、目录及退出码](logs/v0.2.2/20261010T190231_231494_final_checks_retry.json)，退出码 0。核验了 149 项保护文件字节、旧进度/审计全文、10 个模块及两个入口的构建产物、109 条定理与审计输出逐项对应、9 个依赖检出提交、新文档链接和数学分隔、19 项 mathlib 源码行，以及本机 VS Code 的两条操作命令。

检查脚本首次运行因本机 Python 没有 `tomllib` 而退出 1，见 [失败输出](logs/v0.2.2/20261010T190218_077261_final_checks.log)／[元数据](logs/v0.2.2/20261010T190218_077261_final_checks.json)。随后只用既有标准库读取所需的默认目标字段，未安装依赖；修复后重试通过。这不涉及 Lean 数学证明的改动。

[交付文件哈希](logs/v0.2.2/verified_artifact_hashes.json)覆盖正式源码、README、阅读指南和固定配置；本 PROGRESS 的最后验收登记不在该哈希表中。[检查脚本](logs/v0.2.2/final_checks.py)保留以便复核。失败日志和中间模块检查全部保留，没有将未执行的命令标为通过。

下一任务为 v0.2.3；本轮交接到此，未创建 `LocalSpatial.lean`，未提交或推送远端。


---

以下完整保留此前进度记录。

# LeanPML 当前进度：v0.2.1

用途：记录“系数条件、零吸收分支和精确小量条件”的实现、学习说明及实际验证证据。更新日期：2026-10-10（Asia/Shanghai）。下方完整保留 v0.1.3 及此前进度原文，其中“本轮”“下一阶段”仅指相应历史阶段。

**v0.2.1 已完成。** 数学任务、中文代码与阅读说明、默认构建、独立公理审计及文档交叉核对均已完成。本轮没有进入 v0.2.2。

## 交付文件及实际范围

- [PML/Coefficients.lean](LeanPML/PML/Coefficients.lean)：5 个定义、17 条定理，覆盖 V7 (5.2)–(5.4) 的点态参数代数。
- [PML/Weights.lean](LeanPML/PML/Weights.lean)：7 个定义、15 条定理，覆盖 (5.5) 的能量权重、(7.2) 的耗散分式、(9.2) 的分配权重以及四分支/无界族实例。
- [中文阅读指南](docs/v0.2.1_reading_guide.md)：论文到 Lean 的对应、假设用途、三段关键证明、mathlib 源码位置和 InfoView 操作。
- [LeanPML.lean](LeanPML.lean) 导入两个新模块；[Audit.lean](Audit.lean) 审计全部新增 32 条定理，保留旧 59 条，合计 91 条。
- [README.md](README.md) 更新当前入口；本进度保留全部旧记录；[logs/v0.2.1](logs/v0.2.1) 保存命令、输出、元数据及修改前快照。

所有代数对象都在固定空间点取值。$p,r$ 可以来自空间变系数场，不假设全域常吸收。$C_P>0$ 在本阶段仅是给定参数，不宣称证明了矩形 Poincaré 不等式。没有引入隐藏参数结构、全局吸收正下界或 PDE 能量结论作为假设。

## 定义、假设、结论和依赖

命名空间为 `LeanPML.PML`。具体输入与逐步说明以源码及阅读指南为准。

| 来源与声明 | 输入／用途 → 结论 |
|---|---|
| `absorptionSum`、`absorptionProduct` | V7 第 1 节的 $a=p+r,b=pr$；用于 (5.4) 和权重分母 |
| `materialA`、`scaleK`、`threshold` | (5.2) 的 $A,K,c_*$，定义不预设正性 |
| `materialA_pos`、`scaleK_pos`、`threshold_pos` | 对应材料/域参数正性 → $A,K,c_*>0$；$\tau$ 不参与 $K$ 的正性引理 |
| `le_inv_sqrt_iff` | $c\ge0,K>0$ → $c\le1/\sqrt K\iff c^2K\le1$，由 (5.2) 推出 |
| `le_threshold_iff_explicit` | $\epsilon,\kappa,\tau,\mu,C_P,c>0$ → 论文阈值与三条显式小量不等式的双向等价 |
| `absorptionSum_nonneg`、`absorptionProduct_nonneg`、`absorptionSum_eq_zero_iff` | $p,r\ge0$ → $a,b\ge0$，且 $a=0\iff p=r=0$ |
| `absorptionSum_le_half` | $p,r\le S\le c/4$ → $a\le c/2$，不额外要求正吸收 |
| `absorptionProduct_le_sum_sq_quarter` | 任意实数 $p,r$，由 $(p-r)^2\ge0$ → $b\le a^2/4$ |
| `absorptionProduct_le_c_sq_sixteenth` | 非负吸收及幅度条件 → $b\le c^2/16$ |
| `absorptionSum_mul_sub_product_nonneg` | 非负吸收、已推导的 $a\le c/2$ → $ac-b\ge0$；实际依赖前两项代数估计 |
| `c_mul_tau_le_material_bound`、`material_bound_lt_sixteenth`、`c_mul_tau_bounds` | 显式条件及正材料，连接阈值等价 → $c\tau\le\kappa/(8A)<1/16<1/4$；严格界使用 $\epsilon>0$ |
| `scale_mul_amplitude_sq_le_sixteenth` | $K,S\ge0,S\le c/4,c^2K\le1$ → $KS^2\le1/16$，合同 §4 的直接推论 |
| `unit_material_smallness_example` | 全部材料及 $C_P$ 取 1、$c=1/576$ → 调用等价定理验证可行小量条件 |
| `energyWeightX/Y`、`thetaX/Y` | (5.5)、(9.2) 前的分支定义，分别在零区取 0 和 $1/2$ |
| `weights_of_sum_zero` | $a=0$ → 上述四个零区值；不除以 $a$ |
| `energyWeights_lower_bound` | $a>0$、幅度条件 → $w_x,w_y\ge3/2$，仅正吸收分支 |
| `theta_partition` | $p,r\ge0$ → $0\le\theta_x,\theta_y\le1$ 且和为 1，包含零区 |
| `dissipationPlus/Minus` 及三条界定理 | 对应非负吸收、幅度与 $a>0$ → (7.2) 分式非负、上界 $c+S\le5c/4$ 或 $c$ |
| 四个 `*_example`（zero_absorption、x_layer、y_layer、corner） | $c=4,S=1$、吸收为 0/1 → 调用一般分支定理并精确计算 $w,\theta$ |
| `vanishingAbsorption`、`family_denominator_pos`、`vanishingAbsorption_bounds` | 固定 $c>0$，$p_n=c/(n+4)$ → 分母正、$0<p_n\le c/4$ |
| `vanishingAbsorption_eventually_small` | $c,\delta>0$ → 存在 $N$ 使所有 $n\ge N$ 满足 $0<p_n<\delta$ |
| `energyWeights_on_family`、`energyWeights_unbounded` | 参数族真实计算 → $w_x=n+4,w_y=n+3$，任意有限 $M$ 都被某项同时超过 |

全部定理的假设都显式列出。$ac-b$ 引理中的 `ha_le_half` 是前一个引理从原幅度条件推出的中间接口，不是新增的模型假设。一般保持/能量时间引理本轮无需参与，因为本阶段不涉及时间路径求导；旧 v0.1.* 源码未重构。

## 四分支、无界性与零区耗散

四个权重实例取 $(p,r)=(0,0),(1,0),(0,1),(1,1)$，对应

$$
(w_x,w_y)=(0,0),(4,3),(3,4),(3/2,3/2),
$$

$$
(\theta_x,\theta_y)=(1/2,1/2),(1,0),(0,1),(1/2,1/2).
$$

它们调用一般定理，且用精确数值验证所用幅度/分支假设；$c=4$ 的四点例子不宣称满足任意材料的完整小量条件。完整材料可行性由另一个 `unit_material_smallness_example` 验证：$A=3,K=24,c=1/576$。该例仍没有把 $C_P=1$ 解释成已证空间常数。

在正分支，令 $s=\sigma_i,t=\sigma_j$ 或交换二者，分式界为

$$
0\le\frac{s(c+s)}{s+t}\le c+S\le5c/4,\qquad
0\le\frac{s(c-s)}{s+t}\le c.
$$

这里分别使用 $c,s,t\ge0,s\le S$，或 $0\le s\le c,t\ge0$；始终先提供 $s+t>0$ 才用除法保序。没有要求吸收远离零。无界族固定 $c>0,S=c/4,r=0$，同时证明了趋零和任意 $M$ 的无界量词，而非仅做数值采样。

V7 (7.2) 在 $Z=\{a=0\}$ 上保留独立的 $c|\nabla v|^2$。分式定义的总函数值不是完整耗散；没有通过零延拓删除这部分。此阶段只核验系数性质，完整空间局部恒等式与积分留待以后。

## 固定环境与实际命令

Lean `v4.31.0`（提交 `68218e876d2a38b1985b8590fff244a83c321783`），Lake `5.0.0-src+68218e8`，mathlib `v4.31.0`（提交 `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`）。依赖锁定及 Lake 包元数据 `0.0.3` 未变，本轮无安装、依赖更新或全局默认工具链修改。

以下命令均通过原 [run_logged.py](scripts/run_logged.py) 在工程根目录执行：

~~~text
/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML
~~~

每次使用 `python3 scripts/run_logged.py --stage v0.2.1 标签 命令...`；完整命令、工作目录、实际程序路径、退出码及时间保存在同名 JSON，原始 stdout/stderr 合并输出保存在 LOG。

| 实际命令 | 退出码 | 完整输出／元数据 |
|---|---:|---|
| `python3 -c …（输入快照）` | 0 | [LOG](logs/v0.2.1/20261010T163514_352590_input_snapshot.log)／[JSON](logs/v0.2.1/20261010T163514_352590_input_snapshot.json) |
| `lake --version` | 0 | [LOG](logs/v0.2.1/20261010T163514_482563_lake_version.log)／[JSON](logs/v0.2.1/20261010T163514_482563_lake_version.json) |
| `lake env lean --version` | 0 | [LOG](logs/v0.2.1/20261010T163514_482593_lean_version.log)／[JSON](logs/v0.2.1/20261010T163514_482593_lean_version.json) |
| `lake env lean LeanPML/PML/Coefficients.lean` | 0 | [LOG](logs/v0.2.1/20261010T163711_696784_coefficients_check.log)／[JSON](logs/v0.2.1/20261010T163711_696784_coefficients_check.json) |
| `lake build LeanPML.PML.Coefficients` | 0 | [LOG](logs/v0.2.1/20261010T163735_193113_coefficients_build.log)／[JSON](logs/v0.2.1/20261010T163735_193113_coefficients_build.json) |
| `lake env lean LeanPML/PML/Weights.lean` | 1 | [LOG](logs/v0.2.1/20261010T164047_677105_weights_check.log)／[JSON](logs/v0.2.1/20261010T164047_677105_weights_check.json) |
| `lake env lean LeanPML/PML/Weights.lean` | 0 | [LOG](logs/v0.2.1/20261010T164113_945466_weights_check_retry.log)／[JSON](logs/v0.2.1/20261010T164113_945466_weights_check_retry.json) |
| `lake build` | 0 | [LOG](logs/v0.2.1/20261010T164149_807197_lake_build.log)／[JSON](logs/v0.2.1/20261010T164149_807197_lake_build.json) |
| `lake build` | 0 | [LOG](logs/v0.2.1/20261010T164214_705177_lake_build_final.log)／[JSON](logs/v0.2.1/20261010T164214_705177_lake_build_final.json) |
| `lake env lean Audit.lean` | 0 | [LOG](logs/v0.2.1/20261010T164229_853015_axioms_audit.log)／[JSON](logs/v0.2.1/20261010T164229_853015_axioms_audit.json) |

真实修复记录：

- 权重首轮检查退出 1：`energyWeights_on_family` 的 x 分支在 `field_simp` 后剩下 `c - 0 = c + 0 * (↑n + 4)`，尚未闭合。添加 `ring` 完成机械代数，未改变假设或结论。
- 下一次检查和第一次默认构建已退出 0，但报告两处多余 `<;>` 的风格警告。改为普通顺序 `ring` 后再次实际构建，最终无这些警告；未关闭 linter。
- 最终默认构建输出 `Build completed successfully (2119 jobs).`。Coefficients 已在本阶段单独实际构建，随后默认构建沿导入链检查新 Weights、根入口和 Audit，覆盖全部 8 个模块。
- 独立公理审计包含全部 91 条定理，只有 `propext`、`Classical.choice`、`Quot.sound` 标准基础依赖，没有 `sorryAx` 或自定义占位公理。失败日志、带警告日志和最终成功结果均保留。

最终文件与证据检查也已实际退出 0：[完整输出](logs/v0.2.1/20261010T164631_262704_final_checks.log)／[完整命令及元数据](logs/v0.2.1/20261010T164631_262704_final_checks.json)。它确认 116 项受保护文件字节未变、旧进度全文保留、8 个模块和两个入口的构建产物存在、91 条定理与审计逐项对应、9 个依赖检出提交与锁定配置一致，以及新文档链接和数学分隔有效。阅读指南引用的 11 个 mathlib 引理均核对了准确源码行。已保存 [已验证交付文件哈希](logs/v0.2.1/verified_artifact_hashes.json)，覆盖正式源码、README、阅读指南及配置；本 PROGRESS 的最终验收登记不纳入该哈希表。

## 来源版本与历史记录

- V7 正文 SHA-256 仍为 `0a7f73a25cb119eeb75b3e7b3c3f2fbb3b319250f3354ed4dcad0ecff8eff4fb`，与 [source_inventory 的 S2](docs/source_inventory.md) 一致。本轮重新阅读 §5.1、§7.1、§9.2，未把历史审查当成当前 Lean 证据。
- 模型合同、theorem_inventory 和 scope 与 v0.1.3 输入快照一致，未修改其内容和历史状态。
- 路线图本轮开始时的 SHA-256 为 `521bbb4fcad5d64159726f47ac2a694d282dbd0fc637ff025eaa0718fdffd63d`，v0.1.3 记录及当前 Git HEAD 为 `ea0598a824d40ed1678b3b36e61a3329b9086625cc957839ca947b0acd6fb39e`。已核对 [原有差异](logs/v0.2.1/roadmap_preexisting_diff.patch)：仅第 490–493 行 v0.1.3 四项勾选由空改成完成，第 488 行仍写“待实现”。这是原有状态文字差异，v0.2.1 数学任务没有改动；本轮保留原文件。
- [输入哈希快照](logs/v0.2.1/input_hashes.json) 保护 116 项文件，包括原文、合同、路线图、旧代码/日志、配置、记录脚本及相关外部工程设置。修改前 README、PROGRESS、入口、Audit 和路线图正文也保存在本阶段目录。
- 本节之后保留此前 PROGRESS 全文；[上一阶段 README](logs/v0.2.1/before_README.md) 也完整保留。未回写历史清单或覆盖旧验证日志。

## 已完成部分与未完成接口

本阶段完成 T09 的一般参数代数和 T10 的点态分支/系数部分。**没有整体标记 T10 完成**：加权空间、可测性、等价类、完备性和嵌入不在本轮范围。T08 的精确矩形 Poincaré、空间参数到 $L^\infty$ 幅度语义的连接仍待兑现。

没有实现 PDE 能量恒等式、Green/PEC、原八变量与 primitive 等价、完整五不变量、一般解的存在唯一性或完整 PML 主定理。系数界是这些后续分析的可调用组成部分，不是完整二维 PML 证明。

## 阅读、复现与下一任务

建议先读 [阅读指南](docs/v0.2.1_reading_guide.md)，再依次打开 `absorptionSum_eq_zero_iff`、`energyWeights_lower_bound`、`le_threshold_iff_explicit`。指南区分 mathlib 的基础引理、既有工程与本轮新结果，并列出当前固定依赖的准确源码位置。InfoView 查看方法和每个关键 tactic 的作用均已说明。

~~~sh
cd '/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML'
python3 scripts/run_logged.py --stage v0.2.1 lake_build lake build
python3 scripts/run_logged.py --stage v0.2.1 axioms_audit lake env lean Audit.lean
~~~

**下一阶段 v0.2.2 尚未开始。** 入口为 `PML/LocalElectric.lean` 与 `PML/LocalDebye.lean`：对应 V7 (7.3)、(7.4)、(8.1)–(8.2)，完成电块、Debye 块、约束消元以及实际时间路径上的求导，并保持代数引理和真实分析层的区分。本轮未创建这两个模块。

---

以下为此前进度原文，完整保留。

# LeanPML 当前进度：v0.1.3

用途：登记“真实时间不变量与模型接口练习”的实际实现、验证和边界，便于对照中文代码学习。更新日期：2026-10-10（Asia/Shanghai）。本节之后完整保留 v0.1.2 及更早进度原文，历史章节中的“本轮”“下一阶段”仅指其当时状态。

**v0.1.3 已完成。** 默认构建、独立公理审计及非零正式实例均已实际通过；本轮没有进入 v0.2.1。

## 交付与依赖

- 新增 [Time/Constancy.lean](LeanPML/Time/Constancy.lean)：2 条真实时间常值定理，复用既有 `LeanPML.Time.antitoneOn_Icc_of_hasDerivAt_nonpos`；明确处理 $T=0$。
- 新增 [PML/TimeInvariants.lean](LeanPML/PML/TimeInvariants.lean)：7 个定义、25 条定理。中文批注覆盖对象、真实求导、方程代入、区间常值、兼容保持、零吸收与非零实例。
- [LeanPML.lean](LeanPML.lean) 增加两个正式导入；[Audit.lean](Audit.lean) 保留旧 32 条审计，增加全部 27 条新定理的审计，共 59 条。
- [README.md](README.md) 提供假设表、公式推导、声明索引、阅读顺序、InfoView 操作、复现命令及 PML 对应范围。
- 固定配置、既有 4 个证明模块、日志脚本、合同、清单与旧阶段日志保留；修改前 README、PROGRESS、入口和 Audit 原文保存在 [本阶段日志目录](logs/v0.1.3)。

固定环境仍为 Lean `v4.31.0`（提交 `68218e876d2a38b1985b8590fff244a83c321783`）、Lake `5.0.0-src+68218e8`、mathlib `v4.31.0`（提交 `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`）。Lake 包版本 `0.0.3` 是原有工程元数据，不是研究阶段号。本轮未运行 `lake update`、安装工具或改变全局默认工具链。

## 实际命题、假设和用途

固定一个空间点，令 $u,q,E,P,Z_1,Z_2:\mathbb R\to\mathbb R$，$\epsilon,\kappa,\tau,b$ 是实常参数。恒等式无需符号条件，故覆盖物理范围 $\epsilon,\kappa,\tau>0,b\ge0$；未改变模型合同，也未要求 $b$ 在空间为常数。

三个定义为

$$
C_D=q+\tau P-\kappa u,\qquad C_{z1}=Z_1+\epsilon bu,\qquad C_{z2}=Z_2+bq.
$$

| 保持定理（前缀 LeanPML.PML） | 连续性输入 | 内部真实方程输入 |
|---|---|---|
| `CD_eq_initial` | $u,q,P$ 在 $[0,T]$ 连续 | $u'=E,\ q'=P,\ \tau P'+P=\kappa E$ |
| `CZ1_eq_initial` | $u,Z_1$ 在 $[0,T]$ 连续 | $u'=E,\ Z_1'=-\epsilon bE$ |
| `CZ2_eq_initial` | $q,Z_2$ 在 $[0,T]$ 连续 | $q'=P,\ Z_2'=-bP$ |

上述方程只要求 $t\in(0,T)$；全部以 `HasDerivAt` 输入，极化导数值通过 `∃ dP, HasDerivAt P dP t ∧ ...` 绑定到实际函数。另输入 $T\ge0,t\in[0,T]$，输出对应的 $C(t)=C(0)$。不输入目标零导数或全时段兼容，不增加 $E'$、$E$ 连续性、$\epsilon E'=-P'$ 或磁场条件。

证明依赖依次为：

1. `hasDerivAt_CD_zero`、`hasDerivAt_CZ1_zero`、`hasDerivAt_CZ2_zero`：用真实线性求导规则和原方程得到零导数；`ring` 仅负责代数。
2. 三条 `continuousOn_*`：由参与该不变量的函数连续性得到不变量连续性，适用于任意集合。
3. `Time.eq_initial_of_hasDerivAt_zero`：一般连续性及内部零导数 → $F,-F$ 单调不增 → $F(t)=F(0)$。单点分支调用 `eq_initial_on_Icc_zero`，不需要任何导数证据。
4. 三条 `*_eq_initial`：把上述实际推导交给一般时间接口。
5. 三条 `*_compatibility`：仅追加初值 $C(0)=0$，得到 $q+\tau P=\kappa u$、$Z_1=-\epsilon bu$、$Z_2=-bq$。
6. 两条 `*_eq_initial_of_zero_absorption` 及两条 `*_zero_of_zero_absorption`：实例化 $b=0$，得到 $Z_i$ 保持初值及零初值保持。没有除以 $b$；只要求对应 $Z_i$ 的连续性与内部真实零导数。

没有要求端点的普通双侧导数。函数的类型定义于实轴，不等于在实轴全域假设原方程。

## 非零实例的验证内容

复用 `LeanPML.Debye.exampleE`、`exampleP`，取 $\epsilon=\kappa=\tau=b=1$：

$$
E=e^{-2t},\quad P=-e^{-2t},\quad
u=(1-e^{-2t})/2,\quad q=(1+e^{-2t})/2,\quad Z_1=-u,\quad Z_2=-q.
$$

4 条新 `hasDerivAt_example*` 证明 $u,q,Z_1,Z_2$ 的真实导数；`example_continuous` 给出四函数连续性；旧 Debye 模块提供 $E,P$ 的导数和连续性。`example_polarization` 从真实 $P'$ 证明本阶段所需极化方程，不输入另一条教学子系统方程。

`example_initial_compatibility` 证明三个不变量的初值为零。`example_nonzero_initial` 精确证明 $P(0)=-1,q(0)=1,Z_2(0)=-1,q(0)\ne0$。原变量 $P,Z_2$ 非零，因此“零不变量”不等于“所有变量为零”。

`example_compatibility_on_Icc` 的三个分支分别调用三个一般兼容保持定理，交付任意 $T\ge0$、$t\in[0,T]$ 的兼容关系。不是只做数值检查，也没有用定义的全时段代数化简替代主定理。实例已随默认构建和独立审计通过。

## 命令与真实验证证据

所有下列命令的工作目录均为：

~~~text
/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML
~~~

记录器是原有 [scripts/run_logged.py](scripts/run_logged.py)，调用形式为 `python3 scripts/run_logged.py --stage v0.1.3 标签 命令...`。每份 `.log` 是完整合并输出，同名 `.json` 保存命令、工作目录、执行时间、实际程序路径及退出码。

| 实际动作／命令 | 退出码 | 完整输出与元数据 |
|---|---:|---|
| 输入快照 `python3 -c ...` | 0 | [输出](logs/v0.1.3/20261010T105711_227998_input_snapshot.log)／[完整命令和元数据](logs/v0.1.3/20261010T105711_227998_input_snapshot.json) |
| `lake env lean --version` | 0 | [输出](logs/v0.1.3/20261010T105904_141610_lean_version.log)／[元数据](logs/v0.1.3/20261010T105904_141610_lean_version.json) |
| `lake --version` | 0 | [输出](logs/v0.1.3/20261010T105904_141608_lake_version.log)／[元数据](logs/v0.1.3/20261010T105904_141608_lake_version.json) |
| 首轮 `lake build` | 1 | [失败输出](logs/v0.1.3/20261010T110106_690944_lake_build.log)／[元数据](logs/v0.1.3/20261010T110106_690944_lake_build.json) |
| 修复后 `lake build` | 0 | [成功输出](logs/v0.1.3/20261010T110154_522300_lake_build_retry.log)／[元数据](logs/v0.1.3/20261010T110154_522300_lake_build_retry.json) |
| `lake env lean Audit.lean` | 0 | [完整公理输出](logs/v0.1.3/20261010T110440_468487_axioms_audit.log)／[元数据](logs/v0.1.3/20261010T110440_468487_axioms_audit.json) |

首轮失败发生在 `Time/Constancy.lean:54`：对取负求导结果使用 `simpa only [neg_zero]` 后，Lean 报 `HasDerivAt (-F) 0 s` 与目标显式函数的类型匹配错误。改为 `(hderiv s hs).neg.congr_deriv (neg_zero : -(0 : ℝ) = 0)`，直接替换导数值，重建通过。数学假设、时间范围和结论均未改变。真实失败日志保留。

最终默认构建输出 `Build completed successfully (2117 jobs).`，并明确列出新常值模块、新 PML 模块、`LeanPML` 与 `Audit`。正式导入链共 6 个模块，两个根入口都属于默认目标。

独立审计共 59 条记录，包括新增 27 条；全部依赖仅为 `[propext, Classical.choice, Quot.sound]`。它们是标准基础公理，不是证明占位。没有 `sorryAx` 或自行引入的占位公理。

补充文件与证据检查：首次检查器把 Audit 注释中的示意 `#print axioms` 也计入声明，导致计数断言失败；这是检查器的注释过滤问题，并非 Lean 构建或公理审计失败。修正为先去掉注释后计数，再次检查通过。保留 [检查器失败输出](logs/v0.1.3/20261010T111133_795594_final_checks.log)／[完整命令](logs/v0.1.3/20261010T111133_795594_final_checks.json)，以及 [最终检查输出](logs/v0.1.3/20261010T111152_959705_final_checks_retry.log)／[完整命令与退出码 0](logs/v0.1.3/20261010T111152_959705_final_checks_retry.json)。

最终检查确认：91 项受保护文件字节未变，旧 PROGRESS 全文保留；6 个模块和两个入口的构建产物存在，59 条定理与审计逐项对应；全部 9 个依赖检出提交与锁定文件一致；正式代码无证明占位及自定义公理，新增文档链接有效、显示数学与代码分隔成对，v0.2.1 模块未创建。已保存 [交付文件哈希](logs/v0.1.3/verified_artifact_hashes.json)，覆盖已编译源码、README、配置及日志脚本；本 PROGRESS 的最后证据登记不计入该哈希表。

## 来源核对、差异和阶段边界

- 对照 [合同 §5.1–5.2](docs/model_contract.md)、[T02–T04](docs/theorem_inventory.md) 及 [scope](docs/scope.md) 核对符号和初值意义；这些文档与 v0.1.2 输入快照一致，未修改。
- V7 正文 `results/V7_Maxwell_Debye_PML/V7_global_energy.md`（工程父目录下）的 SHA-256 仍为 `0a7f73a25cb119eeb75b3e7b3c3f2fbb3b319250f3354ed4dcad0ecff8eff4fb`，与来源清单一致。本阶段核对其 (2.4) 和兼容关系，不把此前纸面审查当成已完成的 Lean 证明。
- 路线图当前 SHA-256 为 `ea0598a824d40ed1678b3b36e61a3329b9086625cc957839ca947b0acd6fb39e`，与 v0.1.2 快照中的 `f43c6bc2524262cd97ac4ee9a6768199c8fb5f3da39b732fe89b0b6c3a09d6c5` 不同。本轮按当前 v0.1.3 条目和用户指令实现，未直接沿用旧版本状态结论。
- 具体状态差异：路线图第 474 行仍写 v0.1.2“待实现”，第 476–479 行任务已勾选；v0.1.3 第 488 行仍写“待实现”。[scope.md 第 124–126 行](docs/scope.md) 是 v0.0.2 的历史状态。它们的静态状态文字与后来构建进展不同，不影响本阶段数学假设；原文按要求保留，以本 PROGRESS 的实际证据登记当前完成情况。
- T02 的时间积分提升未实现；T03 仅完成 V7 (2.4) 的三个固定空间点标量不变量，**没有整体标记五不变量条目完成**；T04 的八变量/primitive 双向等价仍未实现。
- 两个磁辅助不变量 $C_x=Q_x-p\phi_y,C_y=Q_y+r\phi_x$、时间/空间导数交换、真实场空间、几乎处处意义和正则性、积分提升与原 PDE 对接均留待后续。
- 当前允许任意初始常数的时间保持结论，没有扩展完整无源 PML 合同的兼容初值范围；也不包含一般解的存在唯一性或完整 PML 能量定理。

## 复现、阅读与下一任务

~~~sh
cd '/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML'
python3 scripts/run_logged.py --stage v0.1.3 lake_build lake build
python3 scripts/run_logged.py --stage v0.1.3 axioms_audit lake env lean Audit.lean
~~~

先读 README 假设表，再读 Monotonicity → Constancy → TimeInvariants，最后看 Audit 和本记录。VS Code 打开整个工程，在 InfoView 中逐步看 `apply`、`rcases`、`congr_deriv`、`.trans hinit` 前后的目标，具体操作见 README。

与 v0.1.2 的联系是实际极化方程、真实导数和闭区间分析接口；区别是 v0.1.2 得到能量非正导数与单调不增，本阶段得到线性不变量的零导数和兼容约束保持。本阶段不会新增能量严格递减结论。

**下一阶段 v0.2.1 尚未开始。** 入口为 `PML/Coefficients.lean` 和 `PML/Weights.lean`：证明 $a=p+r,b=pr$ 的符号和精确小量估计，在零/单向/双向吸收分支定义权重，核验 $w_i$ 与 $\theta_i$ 的不同退化定义及界限。零吸收不能通过除以 $a$ 或 $b$ 跳过，也不能增加吸收正下界。本轮未创建这两个模块。

---

以下为此前进度原文，完整保留。

# LeanPML 当前进度：v0.1.2

用途：记录 Debye 时间子系统本阶段实际实现、验证和交接的范围。更新日期：2026-10-10（Asia/Shanghai）。下方 v0.1.1/v0.0.3 原文完整保留，其中“本轮”“下一阶段”等仅指历史日期。

**v0.1.2 已完成。** 最终默认构建、独立公理审计和非零显式实例均实际通过；本轮没有进入 v0.1.3。

## 交付文件与数学范围

- 新建 [LeanPML/Debye/ScalarEnergy.lean](LeanPML/Debye/ScalarEnergy.lean)，命名空间 `LeanPML.Debye`，含 4 个定义和 20 条新定理，均有中文批注。
- [LeanPML.lean](LeanPML.lean) 增加正式导入；[Audit.lean](Audit.lean) 增加全部 20 条审计，与旧定理合计 32 条。
- [README.md](README.md) 更新命题/假设表、推导、显式实例、InfoView、复现命令和 PML 范围说明。
- 本 PROGRESS 登记真实证据并保留完整历史；[logs/v0.1.2](logs/v0.1.2) 保存完整输出、元数据和修改前快照。
- 重用 `LeanPML.Time.antitoneOn_Icc_of_hasDerivAt_nonpos` 与单点时间引理，未改动旧证明、固定配置或日志脚本。

真实函数 $E,P:\mathbb R\to\mathbb R$，正材料 $\epsilon,\kappa,\tau$ 和 $T\ge0$。主定理只要求 $E,P$ 在 $[0,T]$ 连续，并在 $(0,T)$ 输入以下证据：

```lean
∀ t ∈ Set.Ioo 0 T, ∃ dE dP : ℝ,
  HasDerivAt E dE t ∧ HasDerivAt P dP t ∧
  ε * dE = -dP ∧ τ * dP + P t = κ * E t
```

能量和耗散具体定义为

$$
\mathcal E(t)=\frac{\epsilon E(t)^2+P(t)^2/\kappa}{2},
\qquad
\mathcal D(t)=\frac{(\kappa E(t)-P(t))^2}{\kappa\tau}.
$$

已经从上述真实方程证明内部的

$$
\mathcal E'(t)=-\frac\tau\kappa dP^2=-\mathcal D(t)\le0,
$$

以及 $[0,T]$ 上单调不增和 $0\le\mathcal E(t)\le\mathcal E(0)$。没有把这些结论放进主定理输入或“解”的定义。

| 新声明（省略前缀 LeanPML.Debye） | 假设与依赖 → 结论 |
|---|---|
| `energy`、`dissipation` | 具体时间函数定义，无附带符号/能量律假设 |
| `energy_nonneg` | $\epsilon,\kappa>0$ 和平方非负 → 能量非负，无 ODE 要求 |
| `continuousOn_energy` | $E,P$ 在任意集合连续 → 能量在同集合连续 |
| `hasDerivAt_energy_of_hasDerivAt` | 两个真实点导数 → 未代入方程的能量求导公式 |
| `hasDerivAt_energy_rate` | 两个点导数、两方程、$\kappa\ne0$ → $-(\tau/\kappa)dP^2$ 的 HasDerivAt |
| `dissipation_eq_rate` | 第二方程、$\kappa,\tau\ne0$ → $\mathcal D=(\tau/\kappa)dP^2$ |
| `hasDerivAt_energy_dissipation` | 上述真实点导数与方程 → 导数为 $-\mathcal D$ |
| `dissipation_nonneg` | $\kappa,\tau>0$，无 ODE 要求 → 耗散非负 |
| `energy_deriv_nonpos` | 点导数、两方程、$\kappa,\tau>0$ → 实际能量导数非正 |
| `hasDerivAt_energy_on_Ioo` | 内部 hODE、非零 $\kappa,\tau$ → 内部逐点真实能量导数 |
| `antitoneOn_energy_zero` | 任意参数和函数，无连续/导数假设 → 单点区间单调性 |
| `antitoneOn_energy` | 三正材料、$T\ge0$、原函数连续性与内部 hODE → 闭区间 AntitoneOn |
| `energy_bounds` | 主定理输入及 $t\in[0,T]$ → 非负与初值上界 |
| `exampleE`、`exampleP` | 非零显式函数定义 |
| `hasDerivAt_exampleE`、`hasDerivAt_exampleP` | 链式法则及取负求导 → 全轴真实导数 |
| `continuous_exampleE`、`continuous_exampleP` | 真实可导性 → 全轴连续性 |
| `example_ode` | 已证明的导数证据及代数整理 → 实例两方程 |
| `example_initial` | exp(0)=1 → E(0)=1、P(0)=-1、初能量=1 |
| `example_energy_antitone` | $T\ge0$ → 将实例证据传给一般主定理 |
| `example_energy_bounds` | $T\ge0,t\in[0,T]$ → 调用一般初值界并改写上界为 1 |

$\epsilon>0$ 用于能量非负；主单调性定理中 `_hε` 保留物理范围，但不参与导数符号估计。$\kappa>0$ 用于能量中的 $P^2/\kappa$，与 $\tau>0$ 一起保证耗散分母为正。非零条件显式传给 `eq_div_iff` 和 `field_simp`。没有除以 $\epsilon$，局部求导恒等式无需假设 $\epsilon>0$。

$T=0$ 独立使用单点时间引理；主证明零分支不读取连续性或内部导数。非退化区间调用 v0.1.1 的中值定理接口，未增加端点双侧导数或区间外方程。

## 显式实例的实际验证范围

对 $\epsilon=\kappa=\tau=1$、$E(t)=e^{-2t},P(t)=-e^{-2t}$，已经形式化：

1. `HasDerivAt exampleE (-2 * exampleE t) t` 与 `HasDerivAt exampleP (2 * exampleE t) t`。
2. 带这两条证据的存在量词形式原方程，及两个函数的连续性。
3. 初始场值 $1,-1$ 和初能量 $1$，因此确为非零实例。
4. 对任意 $T\ge0$，通过一般 `antitoneOn_energy` 和 `energy_bounds` 得到 $[0,T]$ 上单调性及 $0\le\mathcal E(t)\le1$。

这些有名定理都在同一正式模块构建、在 Audit 中逐项审计。不是数值采样、普通代数变量检查或仅零解验证。实例为一个非零真实解提供见证，但没有证明一般初值问题的存在唯一性。

## 环境、来源与保留范围

本次重新实际读取版本：Lean `4.31.0`（提交 `68218e876d2a38b1985b8590fff244a83c321783`），Lake `5.0.0-src+68218e8`。mathlib 固定为 `v4.31.0`，提交 `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`。

`lean-toolchain`、`lakefile.toml`、`lake-manifest.json` 均不改动；包元数据仍为 0.0.3，研究阶段为 v0.1.2。没有执行 `lake update`，没有改动 elan 全局设置或其他工程。缓存命令报告 2086 个文件已解压，无需新下载。

未发现适用的 AGENTS.md。开始时 [input_hashes.json](logs/v0.1.2/input_hashes.json) 记录 68 个受保护文件；包括旧源码、固定配置、路线图、模型文档、日志脚本、旧日志和相关工程/全局设置。四个拟修改文件另外保存 `before_*` 快照。已有历史日志和旧 PROGRESS 原文继续保留。

具体材料差异及处理：

- 当前路线图 SHA-256 为 `f43c6bc2524262cd97ac4ee9a6768199c8fb5f3da39b732fe89b0b6c3a09d6c5`，不同于 v0.1.1 记录的 `7514ec9e…`。已重新读取 §3.1、v0.1.2 及相邻阶段；不根据旧哈希猜测全部文本改动。
- 路线图第 460 行仍写 v0.1.1“待在新工程验收”，而第 462–465 行任务已勾选；v0.1.2 第 474 行仍为待实现。本轮保留路线图原文，以本进度和实际日志更新完成状态。
- `docs/scope.md` 第 124–126 行属于 v0.0.2 交接；原 README 末尾和原 PROGRESS 的“v0.1.2 尚未开始”属于上一阶段。当前 README 已更新，旧 PROGRESS 作为历史保留。
- `docs/scope.md` 第 74 行 Q01 区分点态 $EP_t$ 与空间积分/范数。当前只建立实值时间函数的平方能量推导，没有声称兑现空间积分版本。Q02–Q13 的 PML 接口不因本例通过而自动完成。

本阶段未发现需要修改已接受数学合同的冲突；没有改动合同中的材料、吸收、边界或兼容初值条件。

## 实际命令与完整日志

全部命令工作目录为：

```text
/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML
```

使用 `python3 scripts/run_logged.py --stage v0.1.2 标签 命令...`。每条命令的参数列表、工作目录、退出码、开始/结束时间在 JSON 中，完整合并输出在同名 LOG 中。下表 Python 快照命令为简述，实际完整代码在其 JSON 参数中。

| 实际操作/命令 | 退出码 | 完整输出 / 元数据 |
|---|---|---|
| `Python：受保护文件哈希、修改前快照` | 0 | [输出](logs/v0.1.2/20261010T005810_726205_input_snapshot.log) · [元数据](logs/v0.1.2/20261010T005810_726205_input_snapshot.json) |
| `lake env lake --version` | 0 | [输出](logs/v0.1.2/20261010T005810_831764_lake_version.log) · [元数据](logs/v0.1.2/20261010T005810_831764_lake_version.json) |
| `lake env lean --version` | 0 | [输出](logs/v0.1.2/20261010T005810_831842_lean_version.log) · [元数据](logs/v0.1.2/20261010T005810_831842_lean_version.json) |
| `lake exe cache get Mathlib.Analysis.Calculus.Deriv.Pow Mathlib.Analysis.Calculus.Deriv.Mul Mathlib.Analysis.Calculus.Deriv.Add Mathlib.Analysis.SpecialFunctions.ExpDeriv Mathlib.Tactic.FieldSimp Mathlib.Tactic.Ring Mathlib.Tactic.NormNum` | 0 | [输出](logs/v0.1.2/20261010T005909_539572_mathlib_cache.log) · [元数据](logs/v0.1.2/20261010T005909_539572_mathlib_cache.json) |
| `lake build` | 1 | [输出](logs/v0.1.2/20261010T010036_323185_lake_build.log) · [元数据](logs/v0.1.2/20261010T010036_323185_lake_build.json) |
| `lake build` | 0 | [输出](logs/v0.1.2/20261010T010100_916130_lake_build_retry.log) · [元数据](logs/v0.1.2/20261010T010100_916130_lake_build_retry.json) |
| `lake env lean Audit.lean` | 0 | [输出](logs/v0.1.2/20261010T010129_718599_axioms_audit.log) · [元数据](logs/v0.1.2/20261010T010129_718599_axioms_audit.json) |

首轮 `lake build` 实际退出 1：`hasDerivAt_exampleE`、`hasDerivAt_exampleP` 中，`simpa` 未把目标里部分应用的显式函数定义展开到预期形式。修复为 `change` 显式给出函数，再用 `congr_deriv (by ring)` 对齐导数值；没有改函数、方程或假设。同时移除了 `field_simp` 已解决目标后的多余 `ring`，没有关闭检查器。失败输出与修复后成功输出均保留。

缓存工具重放了 `ld64.lld: warning: directory not found for option -L/usr/local/lib`，命令本身退出 0。没有为该缓存链接警告改变全局目录或配置。最终正式构建无上述证明警告。

最终构建明确记录 `Built LeanPML.Debye.ScalarEnergy`、`Built LeanPML`、`Built Audit`；旧模块作为未改动依赖参与默认构建。输出 `2115 jobs` 包含依赖任务，不是项目定理数。

## 公理审计与验收

末次检查实际退出 0：[完整输出](logs/v0.1.2/20261010T010604_033726_final_checks.log) · [命令、目录与退出码](logs/v0.1.2/20261010T010604_033726_final_checks.json)。确认 68 个受保护文件未变、旧 PROGRESS 原文完整保留、6 个正式模块有构建产物、全部 32 条定理进入审计、9 个依赖实际提交与 manifest 一致、当前文档链接有效。正式源码、README、固定配置和日志脚本的 [交付哈希](logs/v0.1.2/verified_artifact_hashes.json) 已保存；PROGRESS 因追加本段而不包含在该哈希表中。

独立 `lake env lean Audit.lean` 实际输出全部 32 条定理的依赖，均为

```text
[propext, Classical.choice, Quot.sound]
```

这三项分别是命题外延性、经典选择和商类型基础原则；无 `sorryAx` 或自定义证明占位公理。不能把标准基础原则误报为“未完成证明”；也不能只看依赖列表而跳过实际命题语义。

| v0.1.2 验收项 | 结果 |
|---|---|
| 真实 E、P、常参数、具体能量 | 4 个定义，命名空间与教学例分离 |
| 两种真实耗散公式 | 从 HasDerivAt 与原方程推导，非零分母有显式证据 |
| 能量非负、连续、耗散非负、实际导数非正 | 均实际形式化，符号不是输入的能量结论 |
| 有限区间主定理与初值界 | 输入仅材料条件、T≥0、原函数连续性与内部 ODE |
| T=0 与端点 | 单点分支无导数；不加端点普通双侧导数 |
| 非零实际函数实例 | 真求导、真方程、连续性、初值及一般定理调用全部编译 |
| 构建/审计 | 最终均退出 0，新模块与全部新定理实际进入检查 |
| 中文说明与复现 | README、源码注释、InfoView 指南和日志齐全 |
| 阶段边界 | 未建立时间不变量模块，未进入 v0.1.3 |

## 距离完整 PML 及下一任务

当前是给定解的时间先验能量估计与一个显式解的验证，允许等号；没有证明一般初值问题的存在唯一性、严格递减或完整二维 PML。此处的极化平方抵消是后续局部能量计算的基础，完整 PML 还需原八变量/提升等价、五不变量、空间 Green 与 PEC、时间空间导数交换、加权图范数与 Poincaré、两层耗散闭合及积分平衡。没有因此将旧 theorem_inventory 的完整 PDE 条目标为实现。

**下一阶段 v0.1.3 尚未开始。** 计划入口 `LeanPML/PML/TimeInvariants.lean`，从真实 $u'=E,q'=P,\tau P'+P=\kappa E$ 推出 $q+\tau P-\kappa u$ 为时间常数；从 $Z_1'=-\epsilon bE,Z_2'=-bP$ 推出 $Z_1+\epsilon bu$、$Z_2+bq$ 为常数，并证明零初值保持。先处理固定空间点的时间函数，磁辅助与场空间对应留到后续阶段。本轮未创建此模块。

---

# v0.1.1 及更早历史记录（以下保留原文）

# LeanPML 当前进度：v0.1.1

用途：记录本阶段已经由 Lean 实际检查的命题、命令证据和范围，便于复现及继续学习。更新日期：2026-10-06（Asia/Shanghai）。下方 v0.0.3 原文作为历史保留；其中“本轮”和“尚未开始”仅指当时阶段。

**v0.1.1 已完成。** 最终 `lake build` 与独立 `lake env lean Audit.lean` 均实际退出 0。没有进入 v0.1.2，没有改变已接受的 PML 数学合同。

## 本阶段交付与范围

| 文件 | 变更 |
|---|---|
| [Time/Monotonicity.lean](LeanPML/Time/Monotonicity.lean) | 新增一般闭区间单调性接口、无分析假设的单点区间引理 |
| [Tutorial/ScalarEnergy.lean](LeanPML/Tutorial/ScalarEnergy.lean) | 新增标量能量性质、有限区间主定理、初值界及负耗散对照例 |
| [LeanPML.lean](LeanPML.lean) | 将两个新模块接入正式默认构建 |
| [Audit.lean](Audit.lean) | 对全部 12 条项目定理逐项执行 `#print axioms` |
| [scripts/run_logged.py](scripts/run_logged.py) | 增加可选 `--stage v0.1.1`，旧用法保持兼容 |
| [README.md](README.md) | 中文命题说明、逐步阅读顺序、VS Code InfoView、复现与下一阶段入口 |
| [logs/v0.1.1](logs/v0.1.1) | 命令完整输出、参数/目录/退出码元数据、修改前快照 |

复用 [LocalEnergy.lean](LeanPML/Tutorial/LocalEnergy.lean) 中的 `energy` 与 `LeanPML.Tutorial.hasDerivAt_energy`，未改动该文件。新增 11 条定理，连同旧求导定理共审计 12 条；构建输出中的 `2114 jobs` 包含依赖任务，不是新增定理数量。

| 命名空间与定理 | 假设 → 已证结论 |
|---|---|
| `Time.antitoneOn_Icc_of_hasDerivAt_nonpos` | 一般函数在 $[a,b]$ 连续，内部有真实导数证据且导数值非正 → $[a,b]$ 上单调不增 |
| `Time.antitoneOn_Icc_self` | 任意函数 → $[a,a]$ 上单调不增，无连续性或导数假设 |
| `Tutorial.energy_nonneg` | 任意 $u,t$ → 平方能量非负 |
| `Tutorial.continuousOn_energy` | 原函数在任意集合连续 → 能量在同一集合连续 |
| `Tutorial.hasDerivAt_energy_on_Ioo` | $(0,T)$ 内原方程 → 内部能量真实导数及公式，不要求耗散符号 |
| `Tutorial.energy_deriv_nonpos` | 某点原方程与 $\sigma\ge0$ → 该点实际能量导数非正 |
| `Tutorial.antitoneOn_energy_zero` | 任意 $u$ → 能量在 $[0,0]$ 单调不增，无参数/连续/导数假设 |
| `Tutorial.antitoneOn_energy` | $\sigma,T\ge0$，原函数闭区间连续、内部原方程 → 能量在 $[0,T]$ 单调不增 |
| `Tutorial.energy_bounds` | 主定理输入及 $t\in[0,T]$ → $0\le\mathcal E(t)\le\mathcal E(0)$ |
| `Tutorial.exp_solves_negative_damping` | 任意时刻 → $e^t$ 满足 $\sigma=-1$ 的真实方程 |
| `Tutorial.negative_damping_counterexample` | 无假设的显式例子 → exp 连续、上述真实方程成立、能量在 $0$ 可导且导数为 $1>0$ |

上表名称均省略共同前缀 `LeanPML.`。主定理输入里没有能量导数、导数符号、单调性或初值界。对给定函数，已经证明

$$
\left.
\begin{gathered}
\sigma\ge0,\quad T\ge0,\quad u\in C([0,T]),\\
\forall t\in(0,T),\quad u'(t)=-\sigma u(t)
\end{gathered}
\right\}
\Longrightarrow
\begin{cases}
\mathcal E(t)=u(t)^2/2\ge0,\\
\mathcal E'(t)=-\sigma u(t)^2\le0 & (t\in(0,T)),\\
\mathcal E(t)\le\mathcal E(s) & (0\le s\le t\le T),\\
0\le\mathcal E(t)\le\mathcal E(0) & (t\in[0,T]).
\end{cases}
$$

没有要求整个实轴满足方程或端点处有双侧导数。一般时间引理调用 mathlib 的 `antitoneOn_of_hasDerivWithinAt_nonpos`，通过 `interior_Icc` 对接内部区间。$T=0$ 单独处理，主证明零分支不使用连续性和内部方程。$\sigma\ge0$ 用于符号估计，不用于求导公式。

这是给定函数的先验能量结论，不是存在性、唯一性、严格递减或二维 PML 定理。对照例正式验证 $\sigma=-1$ 时 $\mathcal E'(0)=1>0$；没有额外声称已形式化某个区间上的 `¬ AntitoneOn`。

## 固定环境与保护范围

本阶段实际再次运行：
- Lean `4.31.0`，提交 `68218e876d2a38b1985b8590fff244a83c321783`。
- Lake `5.0.0-src+68218e8`，随上述工具链使用。
- mathlib 固定为 `v4.31.0`，提交 `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`。

`lean-toolchain`、`lakefile.toml`、`lake-manifest.json` 本轮不改动，包元数据仍为 0.0.3；研究阶段记为 v0.1.1。本次没有执行 `lake update`。缓存命令只解压新增导入所需的 145 个已有缓存文件，不更改固定依赖。

未发现适用的 `AGENTS.md`。初始 [input_hashes.json](logs/v0.1.1/input_hashes.json) 记录 41 个受保护文件，包括工具链/依赖配置、LocalEnergy、路线图、既有模型文档、旧日志、elan 设置和其他相关工程配置。[旧 README](logs/v0.1.1/before_README.md) 与 [旧 PROGRESS](logs/v0.1.1/before_PROGRESS.md) 另存修改前快照，旧阶段日志完整保留。

当前路线图 SHA-256 是 `7514ec9ef9f4e37e0945feb9b5d702e15318c6bcf7cde9c00ea3d6ab05045d83`，与 v0.0.3 日志中的哈希不同。本轮已重新读取 v0.1.1 及相邻阶段，不沿用旧版本状态推断。本轮不回写路线图；其 v0.1.1 待办勾选保持输入原样，实际完成状态以此记录和编译证据为准。原模型合同未发现本轮需修改的数学假设。

## 实际执行证据

所有命令工作目录均为：

```text
/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML
```

命令通过 `python3 scripts/run_logged.py --stage v0.1.1 标签 命令...` 执行。`.log` 是完整标准输出与标准错误合并记录；`.json` 包含实际命令参数、工作目录、退出码和时间。Python 快照命令的完整内容保存在元数据，不在表中展开。

| 实际命令/操作 | 退出码 | 完整输出 / 元数据 |
|---|---|---|
| `Python：输入哈希、AGENTS 定位、修改前快照` | 0 | [输出](logs/v0.1.1/20261006T160035_849758_input_snapshot.log) · [元数据](logs/v0.1.1/20261006T160035_849758_input_snapshot.json) |
| `lake exe cache get Mathlib.Analysis.Calculus.Deriv.MeanValue Mathlib.Analysis.SpecialFunctions.ExpDeriv Mathlib.Tactic.NormNum` | 0 | [输出](logs/v0.1.1/20261006T160045_511715_mathlib_cache.log) · [元数据](logs/v0.1.1/20261006T160045_511715_mathlib_cache.json) |
| `lake env lean --version` | 0 | [输出](logs/v0.1.1/20261006T160045_511719_lean_version.log) · [元数据](logs/v0.1.1/20261006T160045_511719_lean_version.json) |
| `lake env lake --version` | 0 | [输出](logs/v0.1.1/20261006T160045_511723_lake_version.log) · [元数据](logs/v0.1.1/20261006T160045_511723_lake_version.json) |
| `lake build` | 1 | [输出](logs/v0.1.1/20261006T160248_266606_lake_build.log) · [元数据](logs/v0.1.1/20261006T160248_266606_lake_build.json) |
| `lake build` | 1 | [输出](logs/v0.1.1/20261006T160319_324239_lake_build_retry.log) · [元数据](logs/v0.1.1/20261006T160319_324239_lake_build_retry.json) |
| `lake build` | 0 | [输出](logs/v0.1.1/20261006T160348_400758_lake_build_retry2.log) · [元数据](logs/v0.1.1/20261006T160348_400758_lake_build_retry2.json) |
| `lake env lean Audit.lean` | 0 | [输出](logs/v0.1.1/20261006T160544_665228_axioms_audit.log) · [元数据](logs/v0.1.1/20261006T160544_665228_axioms_audit.json) |

首轮构建发现 `Set.interior_Icc` 不存在，实际名称是全局的 `interior_Icc`。修正后的一次构建进一步发现连续性目标中部分应用的 `energy u` 未被预期的 `simpa only [energy]` 展开；改用 `change ContinuousOn (fun t => (u t)^2 / 2) s` 明确目标后通过。两次失败均原样保留，没有改数学假设，也没有留下失败分支或占位证明。

末次验收检查同样实际退出 0：[完整输出](logs/v0.1.1/20261006T160815_500158_final_checks.log) · [命令、目录与退出码](logs/v0.1.1/20261006T160815_500158_final_checks.json)。它确认 41 个受保护文件字节未变、旧 PROGRESS 原文完整保留、五个正式模块都有构建产物、全部 12 条定理进入审计、9 个依赖的实际提交与 manifest 一致，以及当前文档链接有效。正式源码、固定配置、日志脚本和 README 的 [交付哈希](logs/v0.1.1/verified_artifact_hashes.json) 已保存；PROGRESS 因追加本次日志链接而不包含在该交付哈希表中。

缓存命令重放了旧的链接警告 `ld64.lld: warning: directory not found for option -L/usr/local/lib`，该命令实际退出 0，最终正式构建与独立审计也退出 0。未为这条警告修改全局环境。

## 审计结论与验收

12 条定理在独立审计中均只依赖：

```text
[propext, Classical.choice, Quot.sound]
```

它们分别是命题外延性、经典选择和商类型的标准基础原则；没有 `sorryAx` 或自定义证明占位公理。审计覆盖旧求导引理、全部新增一般/标量引理以及显式参数对照例。

| v0.1.1 验收项 | 结果 |
|---|---|
| 复用原定义、原求导引理及固定环境 | 已复用；没有新定义另一套能量 |
| 能量非负、内部可导及导数公式 | 已形式化 |
| 从非负耗散参数证明真实导数非正 | 已形式化 |
| 闭区间单调性与初值界 | 已形式化，主定理只输入原函数条件 |
| $T=0$ 和端点处理 | 单点结论无导数/连续假设；端点由中值定理接口处理 |
| 修改参数假设的对照例 | $\sigma=-1,u=e^t$，能量在 $0$ 处导数为 $1>0$ |
| 默认构建覆盖 | 正式库、两新模块及 Audit 均接入；LocalEnergy 为已构建的未改动依赖 |
| 实际默认构建与独立公理审计 | 最终均退出 0，无占位公理 |
| 中文阅读、InfoView、终端复现说明 | 见 README 与源码逐步注释 |
| 阶段边界 | 未创建 Debye 模块，没有进入 v0.1.2 |

## 下一步：v0.1.2（尚未开始）

按路线图的 Debye 时间子系统入口，计划建立 `LeanPML/Debye/ScalarEnergy.lean`，以两条实际导数方程为输入，证明

$$
\frac{d}{dt}\frac12\left(\epsilon E^2+\frac{P^2}{\kappa}\right)
=-\frac{(\kappa E-P)^2}{\kappa\tau}.
$$

需显式使用 $\epsilon,\kappa,\tau>0$，从定义求导得到耗散，并给出非零实例。可以复用当前的通用时间单调性引理；这一步仍是时间子系统，不是完整 PML。这里只记录下一任务，没有实现任何 Debye 证明。

---

# v0.0.3 历史记录（以下保留原文）

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
