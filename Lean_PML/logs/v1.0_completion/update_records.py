from pathlib import Path
import json, hashlib, datetime
root=Path.cwd();folder=root/'logs/v1.0_completion'
def append(name,text):
 p=root/name
 with p.open('a') as f:f.write('\n\n'+text.strip()+'\n')
append('reports/weak_theorem.md',r'''
## 2026-10-14 v1.0_completion：实际验收结果

**当前新增版本已核验；ROADMAP v1.0 原文逐项对齐仍未完成。** 上一节为开工清单，本节为当前最终状态。一般分离 $W^{1,\infty}$ 的连续代表构造仍未闭合；不能以独立连续代表输入代替这项证明。

|任务/原文|本轮声明与实际调用|验收状态|
|---|---|---|
|(5.7) 算子核→标量核|`Analysis.dampingKernel_eq_scalarExpMultiplier` → `Weak.OriginalInterval.scalar_memory_both`、`scalar_memory_physical_x/y`|完成：实际加权商类、普通 L²、Bochner 可积性；逐时刻等式，不交换时间/a.e.量词|
|(5.1) 精确常数|`Rectangle.weak_sharp_poincare` → `sharpWeakPoincareDomain` → `OriginalInterval.sharpFiniteProblem`|完成：一维平方展开/FTC、两个方向切片与 Fubini、H¹ 图闭包极限|
|(10.1) 原数值阈值|`Rectangle.ParameterCertificate.original_parameters_threshold`、`original_parameters_explicit`、`original_amplitude_certificate`|完成：真实方形 $C_P^2=2/\pi^2$、$K=48/\pi^2$、$c=1/128$、$S=1/512$；严格用 $\pi>3$。不附带核验 (10.2) 全族，也未另证显示的 min 最小分支等式|
|(6.6)→真实时间路径|`Weak.V7ClosedCkCore.regularity` → `main_energy_RegionalSharpCk`|正长度区间充分性连接完成；真实 `ContDiffOn` 条件，并非将 OriginalJet 改名|
|(6.7)–(6.10)|`Weak.OriginalInterval.main_energy_estimate_SharpWeakOriginal`；`Weak.main_energy_RegionalSharpCk`|精确常数版本完成；区域连续代表仍输入，故未覆盖一般原文 W¹,∞ 入口|
|(8.4)–(8.8)|`sharp_original_auxiliary_control`、`sharp_original_auxiliary_initial_control`|直接控制输入 O.fields 的 Z1/Z2/Qx/Qy，以及 u/q/φ；保持原常数|
|一般弱系数代表选择|现有 `WeakRegionalAbsorption.p_continuous/r_continuous` 仍为输入|未完成；属于 v1.0 必要主线，不改列可选|

表中名称前缀分别为 `LeanPML.Analysis`、`LeanPML.Rectangle`、`LeanPML.PML.Weak`。精确完整类型见 [本轮类型输出](../logs/v1.0_completion/20261014T170234_873529_type_review.log)。

### 最终入口的输入与输出

推荐声明 `LeanPML.PML.Weak.main_energy_RegionalSharpCk` 接受非退化矩形、材料正性、区域分离系数及原 π 常数阈值、实际八变量 `OriginalInterval`、真实时间正则性和初始加权成员。`OriginalInterval` 的字段包含原八式的内部 HasDerivAt、全矩形 PEC 的 H₀¹ 表示、旋转磁通量 H(div)、闭区间连续、初始五兼容和初始零区条件；不输入全时段兼容或能量目标。

`V7ClosedCkCore` 的四项真实正则性为历史 $u\in C^2([0,T];H_0^1)\cap C^3([0,T];L^2)$、$P\in C^2([0,T];L^2)$、$\lambda\in C^1([0,T];H(\mathrm{div}))$。论文给出的 $u$ 的 H₀¹ C³ 条件更强；本轮只使用其中 C²。φ 的初始加权成员仍输入，实际演化历史、成员及所需导数复用已证结果。这里没有由有限范数估计直接推断 C²。真实 λ_tt 仍由已有图投影、兼容求导和辅助演化推出。

对 $T>0$，`canonicalInterval` 把 E/P 导数槽选为真实区间导数；内部由导数唯一性识别，闭端点由构造选择，**所有原八变量路径不变**。不要求端点 PDE 或端点能量导数公式。对 $T=0$，保留 `main_energy_estimate_SharpWeakOriginal` 的 `OriginalJet` 和 `DegenerateJetCompatibility`，不能把任意单点导数数据解释为解的唯一限制。这个分支没有从空内部推出额外事实。

输出 `SharpEnergyConclusions` 包括图范数双边界、内部 HasDerivAt 与原文定量耗散下界、闭区间 AntitoneOn/非负/初值界、真实 IntervalIntegrable 和积分平衡、输入 E/H/P 的控制；配套输出是原辅助变量的初值能量控制。既有提升选择无关定理 `CompatibleLift.twoLayerEnergy_independent` 对任意 K 有效，直接适用于精确 K，不需重证。既有弱反向八式保留。当前仍是给定足够正则兼容解的先验定理，不是一般适定性。

### 非零调用与剩余证明

`Examples/SharpWeak.lean` 中 `sharp_main_call` 覆盖 $T\ge0$，`canonical_main_call` 调用新 Cᵏ 入口，`sharp_nonzero_static_regression` 保持非零静态态的正能量、常值和零耗散。`Examples/ScalarKernel.lean` 的 `nonconstant_profile_scalar_kernel` 在真实非恒定剖面上调用核识别；它不冒充一般 W¹,∞ 代表选择。旧全零、两种非对称边层、双向吸收、不兼容增长和单层失败仍进入本轮完整构建/审计。

首个未闭合引理：在区间上，由 $\int f\eta'=-\int d\eta$（所有紧支光滑 η）和 $f,d\in L^\infty$，证明 $f=c+\int_a^x d$ a.e.，再构造闭区间 Lipschitz 代表。之后需连接二维分离弱测试关系、区域幅度及代表替换不变性，并去掉最终系数入口的独立连续性输入。已检查原函数/零弱导数路线及卷积路线；准确缺少的测试函数原函数/一致梯度估计见 [语义记录](../logs/v1.0_completion/semantic_review.md)。现有要求 AC 的定理不能反过来证明 AC，没有以普通可导定理冒充弱导数结果。

### 验证与阅读

正式工程构建 3105 jobs 通过；完整公理审计 997 项通过（新增 67 项），无 `sorryAx`；实际类型审查通过。当前未提交源码在隔离目录从零构建本项目并审计通过，只复用精确依赖缓存，未复制本项目编译产物。见 [验收](../logs/v1.0_completion/acceptance.json)、[隔离结果](../logs/v1.0_completion/isolated_result.json)。

建议先读 `weak_sharp_poincare`、`scalar_memory_both`、`main_energy_RegionalSharpCk`，再读各自上游引理。VS Code 中光标放在 `have`/`calc` 后查看 InfoView；F12 跳到定义，修改导入后先 `lake build` 再 Restart File。复现命令见 README。本轮 PDF 7、8、10、13、15 页分别追加精确常数、标量核、Cᵏ/主结论、原变量控制、数值证书范围；未给连续代表缺口打完成勾。
''')
append('README.md',r'''
## 2026-10-14 最新收尾：精确常数与标量核已接通

**当前已核验版本通过；ROADMAP v1.0 主线尚未全部完成。** 本轮证明原 (5.1) π 常数并接入最终弱原系统能量、原 (5.7) 的实际标量指数乘子/Bochner 公式；核验原 c=1/128、S=1/512 数值阈值。真实 Cᵏ 字段可在 T>0 构造路径及规范端点导数槽；T=0 继续明确初始导数兼容。一般分离 W¹,∞→连续代表仍缺，`WeakRegionalAbsorption` 的区域连续性没有被删除或伪装为已证。

先读三条声明：
1. [weak_sharp_poincare](LeanPML/Rectangle/SharpPoincare.lean)：一维→Fubini→H¹ 图闭包；保守常数版本保留。
2. [scalar_memory_both](LeanPML/PML/AuxiliaryScalarMemory.lean)：双方向真实原辅助场与标量指数核；每时刻商类等式。
3. [main_energy_RegionalSharpCk](LeanPML/PML/WeakCanonicalTime.lean)：从区域原系数、原八式、初始兼容和真实正则性到精确常数主结论。

完整输入、T=0 与非零调用见 [弱定理报告最新节](reports/weak_theorem.md)，核查记录见 [semantic_review.md](logs/v1.0_completion/semantic_review.md)。[SharpWeak.lean](LeanPML/Examples/SharpWeak.lean) 有非零实际静态解调用和正能量/零耗散回归。InfoView 中逐步查看 `have`/`calc` 的目标，F12 查原结构字段；刷新导入先构建，再执行 Lean: Restart File。

```sh
cd '/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML'
python3 scripts/run_logged.py --stage v1.0_completion lake_build lake build
python3 scripts/run_logged.py --stage v1.0_completion axioms_audit lake env lean Audit.lean
```

本轮实际通过完整构建、997项审计、类型审查和当前源码隔离复现。隔离未复制本项目编译产物，复用精确依赖缓存。证据：[acceptance.json](logs/v1.0_completion/acceptance.json)、[isolated_result.json](logs/v1.0_completion/isolated_result.json)。没有升级依赖、修改原论文/合同/路线图或提交远端。
''')
append('PROGRESS.md','''
## 2026-10-14 v1.0_completion（保留历史状态）

- 完成 (5.7) 标量核识别并接回原辅助场：MultiplierExponential / AuxiliaryScalarMemory；两个方向、零吸收、Bochner 可积。
- 完成 (5.1) 精确矩形 Poincaré：一维 Dirichlet–Wirtinger、实际切片/Fubini、H¹ 图闭包；接入 MainSharpWeakRectangle。原 (10.1) c=1/128、S=1/512 阈值严格通过。
- 完成正长度区间真实 Cᵏ→主路径充分性：WeakCanonicalTime 保持原场，规范端点导数槽；不增加端点 PDE。T=0 独立初始兼容仍明确。
- 精确常数下原 E/H/P/Z1/Z2/Qx/Qy 及提升量的控制、初值界和非零静态主定理调用均通过。
- 尚缺一般分离 W¹,∞ 弱导数→连续代表及最终入口替换；它仍是 v1.0 主线，不标可选。v1.0.1 已有空间成果保持；v1.0.2 原文范围仍有此缺口；v1.0.3 当前已核验范围完成，完整原文入口未完成。**不登记 ROADMAP v1.0 整体完成。**
- 本轮全工程3105 jobs、997项审计、真实类型审查及隔离构建/审计通过；新67项审计，旧模块保留。精确依赖缓存复用，本项目产物未复制。
- PDF第7、8、10、13、15页新增5个范围红勾、1条正则性说明，旧225条批注全部保留。证据与首个未闭合引理见 logs/v1.0_completion/acceptance.json、semantic_review.md、pdf/。
''')
append('docs/theorem_inventory.md','''
## 2026-10-14 v1.0_completion 逐项追加

历史条目保留；新证据不覆盖旧阶段范围。

- T10/加权相关、(5.7)：`LeanPML.Analysis.dampingKernel_eq_scalarExpMultiplier`；`LeanPML.PML.Weak.OriginalInterval.scalar_memory_both`、`scalar_memory_physical_x/y`。实际加权/普通 L² 标量核，双方向 Bochner 可积，固定时刻商类。已有(5.8)复用。
- (5.1)/Poincaré依赖：`LeanPML.Rectangle.weak_sharp_poincare`、`sharpWeakPoincareDomain`；真实 H₀¹，原π常数，已由 MainSharpWeakRectangle 调用。
- (10.1)：`LeanPML.Rectangle.ParameterCertificate.original_parameters_threshold`、`original_amplitude_certificate`；原数值与精确 CP 匹配，不附带(10.2)任意剖面族。
- T17–T18/T22–T28 主线新常数入口：`LeanPML.PML.Weak.OriginalInterval.main_energy_estimate_SharpWeakOriginal`；`LeanPML.PML.Weak.main_energy_RegionalSharpCk`；(6.7)–(6.10)、(8.4)–(8.8)原场及初值界。新Cᵏ入口T>0，旧jet入口含T=0明确兼容。
- (6.6)：`LeanPML.PML.Weak.V7ClosedCkCore.regularity` 与 `canonical_fields` 从实际 Cᵏ 构造路径；不是正则性自动传播。
- 未完成：一般分离 W¹,∞ 连续代表。当前区域入口仍含连续性字段，不能整项标完整弱V7。

完整声明、依赖和证据见 reports/weak_theorem.md 最新节；logs/v1.0_completion/acceptance.json（997项审计及当前源码隔离复现）。
''')
append('docs/claim_ledger.md','''
## 2026-10-14 v1.0_completion 范围追加

已证：原π常数的矩形 H₀¹ Poincaré及主定理连接；标量指数核与原辅助场实际 Bochner 公式；正长度真实Cᵏ路径到主定理；精确CP下原变量/辅助量控制和非零静态调用。原第10节 c=1/128、S=1/512 已有严格阈值证书。

未证：一般 W¹,∞ 的连续代表构造及从该最原始系数输入直接合成的入口；不得登记“ROADMAP v1.0 主线完成”。T=0 继续保留初始导数兼容，不能从空内部推出。第10节整个(10.2)族与显示min分支等式不自动随阈值证书完成。没有新增适定性、严格衰减、指数衰减或任意八变量范数等价主张。

类型审查、尝试路线和首个具体缺口见 logs/v1.0_completion/semantic_review.md；本轮数学与工程验收分开登记于 acceptance.json。
''')
append('docs/scope.md','''
## 2026-10-14 v1.0_completion 最新范围追加

已有保守CP版本保留；新增已证明原π常数及实际能量入口。新增标量核识别完成(5.7)的实际空间值表示，保持逐时刻商类/a.e.量词。新正长度Cᵏ入口选取端点导数槽而不改变输入原场；T=0另列初始导数兼容。一般区域分离 W¹,∞ 连续代表尚未构造，最终区域入口仍明确输入连续性。本轮不将该差异改称技术上已自动满足；完整原文范围仍未闭合。详见 reports/weak_theorem.md 最新验收节。
''')
append('docs/source_inventory.md','''
## 2026-10-14 v1.0_completion 来源复核追加

基线及最终哈希分别见 logs/v1.0_completion/baseline_20261014T162626.json、acceptance.json。V7 md/tex/原pdf、模型合同、路线图及依赖锁均保持原版本。本轮数学新增使用固定本地 mathlib；未升级依赖。旧closeout源码与基线匹配；新增精确CP、标量核、真实Cᵏ桥接及调用均由本轮日志重新验证，不沿用旧日志证明新文件。指定副本PDF单独追加，备份与前后哈希在 logs/v1.0_completion/pdf/backup.json 和 annotation_result.json。
''')
p=root/'docs/interface_ledger.md'
if p.exists():append(str(p.relative_to(root)),'''## 2026-10-14 v1.0_completion

精确矩形Poincaré与原π常数阈值、算子核→标量核及双方向实际原场、正长度真实Cᵏ→路径接口均已接通；详见本轮semantic_review。一般分离W¹,∞→连续代表仍未兑现。区域入口p_continuous/r_continuous仍输入，未以新字段掩盖。T=0独立初始导数兼容继续保留。''')
p=root/'docs/pdf_formalization_marks.md';s=p.read_text();a=s.index('## 2026-10-14 v1.0_completion');s=s[:a]+s[a:].replace('Cᵏ','C^k');p.write_text(s)
review={'time':datetime.datetime.now().isoformat(),'method':'pdftoppm rendered 5 modified pages at 1600px; each inspected with view_image','pages':[7,8,10,13,15],'passed':True,'findings':'新增文字和矢量勾清晰；未裁切或覆盖正文/编号/旧批注。旧历史待完成说明保留，以本轮明确范围追加更新。','renders':[f'page_{n}.png' for n in [7,8,10,13,15]]}
(folder/'pdf/visual_review.json').write_text(json.dumps(review,ensure_ascii=False,indent=2))
p=folder/'pdf/annotation_result.json';d=json.loads(p.read_text());d['visual_review']='passed; visual_review.json';p.write_text(json.dumps(d,ensure_ascii=False,indent=2))
print('appended current records; formal sources untouched')
