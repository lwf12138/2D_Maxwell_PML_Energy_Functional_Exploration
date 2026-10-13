from pathlib import Path
import json,hashlib,re
root=Path.cwd()
records={s:json.loads((root/'logs'/s/'acceptance.json').read_text()) for s in ['v0.4.1','v0.4.2','v0.4.3','v0.4.4']}
assert all(a['status']=='passed' for a in records.values())
rows='\n'.join(f"| {s} | 已验收 | [构建]({a['build']}) / [审计]({a['audit']}) | {a['audited_declarations']} |" for s,a in records.items())
r=root/'README.md';s=r.read_text();s=s.replace('v0.4.1、v0.4.2 已分别构建和审计通过；v0.4.3、v0.4.4 正在总装核验，暂不登记整个 v0.4 完成。','v0.4.1–v0.4.4 已分别完成实现、完整构建、公理审计和假设检查。')
s=s.replace('→ 总装。','→ [OriginalAssembly.lean](LeanPML/PML/OriginalAssembly.lean) 的 `originalFiniteIntervalProblem_separated` 总装。')
add=r'''
## 最后怎样进入已有能量框架

[OriginalAssembly.lean](LeanPML/PML/OriginalAssembly.lean) 的 `originalFiniteIntervalProblem_separated` 是本轮最终构造：输入真实八变量、分离光滑系数、仅内部的原方程、初始五兼容、PEC、初始零区 φ、强正则性和实际历史的坐标识别，返回旧 `FiniteIntervalProblemConditional`。它没有输入现成的条件性问题，也没有输入 Green、Poincaré、混合交换、全时段兼容或目标能量结论。

`LiftIdentified` 将八个光滑时间槽逐一识别为实际积分提升及磁场重构；不是重新选取无关的 u/q。`original_static_closed` 从初始条件产生闭区间两层静态条件；`original_smoothZeroOn` 从原场零区保持产生加权坐标所需零值，再对邻域零函数求真正的一、二阶导数。`originalFiniteIntervalProblem_second_R_continuous` 另给积分平衡所需 P_tt 的实际 L² 连续性。

T=0 时额外的 `InitialDerivativeCompatible` 只要求初始导数层极化关系及零区 φ_t；不能由空内部方程推出。有限区间能量接口只需要内部 E_t 的零迹；若另外要求整个闭区间 E_t 零迹，`BoundaryTime.velocity_PEC_on_Icc` / `twoLayer_zeroBoundary` 明确要求 T=0 时该初始迹。u 与 E 的闭区间零迹则来自 u₀ 零迹、历史积分与 PEC。

底层 `OriginalAt`/`PrimitiveAt` 用真实 `fderiv` 的总定义书写空间导数。其代数方程定理本身不自动产生空间正则性；本轮具体解释依靠 `SmoothStateData` 与 `LiftIdentified` 的真实光滑代表。`primitive_to_original_rectangle` 在这个类中恢复全部八式和 PEC，不表示方程自动改善正则性。

任意非零初始不变量的时间保持已经证明；把它们设为零后才得到本轮无源 primitive 对应。带非零不变量的额外源项系统未实现，不混入主范围。固定 u₀、q₀ 的历史唯一性也不等于同一原状态的提升规范唯一性。

| 阶段 | 状态 | 完整输出 | 审计声明数（含历史） |
|---|---|---|---|
'''+rows+r'''

审计仅出现标准 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx`；证明源码无 sorry/admit/自定义占位公理。构建还检查了此前全部模块。源码哈希、受保护文件复核、独立语义审查见 [最终验收](logs/v0.4.4/acceptance.json)、[语义审查](logs/v0.4.4/semantic_review_geometry.md)；PDF 的范围和证据集中在[原标注账本](docs/pdf_formalization_marks.md)。
'''
if '## 最后怎样进入已有能量框架' not in s:s+=add
r.write_text(s)
progress=r'''# v0.4.1–v0.4.4：所选光滑矩形类分别验收完成

用途：记录实际几何、空间分析、时间路径和原模型映射。下方保留全部旧历史；旧“未实现”仅表示当时状态。本轮停在具体接口构造，未创建 v0.5 的主定理或报告，没有依赖更新、提交或推送。

| 阶段 | 状态 | 真实构建 / 独立审计 | 审计声明数（含历史） |
|---|---|---|---|
'''+rows+r'''

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

'''
p=root/'PROGRESS.md'; old=p.read_text()
if not old.startswith('# v0.4.1–v0.4.4'): p.write_text(progress+old)
common=r'''

## v0.4 增量：具体光滑矩形与原系统接口（保留上述历史）

本次四阶段分别通过实际完整构建、公理审计与最终假设检查。证据按 [v0.4.1](../logs/v0.4.1/acceptance.json)、[v0.4.2](../logs/v0.4.2/acceptance.json)、[v0.4.3](../logs/v0.4.3/acceptance.json)、[v0.4.4](../logs/v0.4.4/acceptance.json) 保存；准确命令、目录、退出码和完整输出均在所链接日志。没有将旧“待实现”文字直接当作当前状态，也没有覆盖历史。

| 原条目/公式 | 当前新增实际证据 | 范围与剩余部分 |
|---|---|---|
| T01；(1.1)、(2.1)–(2.2) | `Concrete.OriginalAt/OriginalOn` 建模全部八式，真实 HasDerivAt 和 fderiv；`OriginalRectPEC` 全四边 PEC | 定义不是无条件证明；选定光滑表示保证导数对象的分析解释。归一化 ε=ε₀ε∞、κ=ε₀(ε_s−ε∞)、μ=μ₀μ_r，p=σ_x/ε₀、r=σ_y/ε₀，Z/Q 不另外缩放 |
| T02；(2.3) | `Concrete.integralLift_initial/hasDerivAt_integralLift`；`Rectangle.toL2_integralLift_on_Icc` | 实际历史积分与 L² Bochner 积分连接；u₀/q₀任意固定初始原函数，不默认零 |
| T03；(2.4) | `Concrete.five_invariants_on_Icc`、`five_invariants_toLp_eq_of_continuous` | 全部五个真实时间不变量，包括两个磁辅助量；任意初始常数场可随空间变化。不是仅点态代数，也不等于原变量全零 |
| T04；(2.5)、(2.6)、命题2.1 | `Concrete.original_to_primitive_rectangle`、`primitive_to_original_rectangle`、`reconstruct_lift_eqOn`、`lift_reconstruct_eqOn` | 初始零兼容后双向恢复全部八式及 PEC；固定 u₀/q₀，正则性显式。primitive 回环的空间梯度识别在内部；非零不变量附加源项系统未实现 |
| T05；§5.2 零区 | `Concrete.original_zero_region_preserved`、`original_smoothZeroOn`、`original_static_closed` | 原场 φ₀=0 与原演化推出全区间保持，再内部求导得到加权三层零值；T=0 的首层初始图条件单列 |
| T08；(5.1) | `Rectangle.poincare_estimate/poincareDomain`、`scaleK_rectangle`、`threshold_rectangle_pos` | **保守版** CP=2Lx；K=32μ(ε+2κ)Lx²，c_*同步该值。未证明原精确 π 常数，不登记原式完整完成 |
| T10、T12；(5.5)–(5.6)、(6.3)/(6.6) | `Rectangle.hasDerivAt_weighted_smooth`、`hasDerivAt_jet_gradientX/Y`、`hasDerivAt_jet_divergence`、`smoothSpatialPath` | 真实函数↔普通/加权L²及混合交换；统一和加权正则性仍是输入。(5.7)/(5.8)自动传播未证 |
| T16；(7.5) | `Rectangle.green_L2/greenDomain`、`boundary_multiplier_zero`、`twoLayer_zeroBoundary` | 已证明具体光滑矩形四边 Green，域/迹良定义并线性；两层 PEC 消去来自真实求导。不是一般弱 Green，T=0闭端点E_t迹须额外初始迹条件 |
| T11、T17–T29 的具体接口 | `Concrete.originalFiniteIntervalProblem_separated`、`originalFiniteIntervalProblem_second_R_continuous` | 从原八式、初始兼容、实际历史识别、PEC、强正则性产生旧有限区间问题；Green、Poincaré、交换、全时段静态/零区不再外传为目标假设。既有能量结论未在本轮另行发布为v0.5主定理 |
| T30–T31、T06–T07 | 暂不升级为完整完成 | v0.5.1最终具体先验定理发布、弱空间完整范围、加权传播、提升规范唯一性仍各有边界 |

表中 `Concrete.*` 完整前缀为 `LeanPML.PML.Concrete.`，`Rectangle.*` 为 `LeanPML.Rectangle.`。代码位于 [Rectangle](../LeanPML/Rectangle) 和 [OriginalAssembly](../LeanPML/PML/OriginalAssembly.lean) 导入链；逐项哈希与实际声明名见最终验收/源码。

最高入口的输入审查另见 [独立语义记录](../logs/v0.4.4/semantic_review_geometry.md)。`SmoothZeroOn`、`SmoothStaticAt` 是中间桥接需要的结论包，最终入口由原方程证明填入；不可只看结构名字或 #print axioms 就视其为已证。`SmoothStateRegular` 只给真实成员资格、连续性与可微性。光滑延拓和 C(K) 条件比完整 V7 弱范围强，且不要求延拓域外满足 PDE。
'''
for name in ['theorem_inventory.md','claim_ledger.md']:
 p=root/'docs'/name;s=p.read_text()
 if '## v0.4 增量：' not in s:p.write_text(s+common)
# 源文、配置、旧数学模块的只读核对；仅允许本轮声明过的文档及入口改变。
snap=json.loads((root/'logs/v0.4.1/source_snapshot.json').read_text())['hashes'];changed={};stable={}
for f,old in snap.items():
 now=hashlib.sha256((root/f).read_bytes()).hexdigest()
 (stable if now==old else changed)[f]={'before':old,'after':now}
allowed={'README.md','PROGRESS.md','LeanPML.lean','Audit.lean','docs/source_inventory.md','docs/theorem_inventory.md','docs/claim_ledger.md','docs/pdf_formalization_marks.md','../results/V7_Maxwell_Debye_PML/V7_global_energy_副本.pdf'}
assert not(set(changed)-allowed),set(changed)-allowed
report={'unchanged_count':len(stable),'unchanged':stable,'authorized_changed':changed,'unexpected_changed':[],'roadmap_status':'§10各阶段与§17.2仍写待实现；本轮保留原文，实际状态用新源码/日志登记。','constant_difference':'CP=2Lx保守版；原文精确π公式不变','scope_difference':'全空间/全时间技术光滑延拓、C(K)统一和加权路径正则性强于原V7；PDE仍仅Ioo0T×Ω'}
(root/'logs/v0.4.4/source_verification.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
p=root/'docs/source_inventory.md';s=p.read_text()
if '## v0.4 来源复核' not in s:s+=r'''

## v0.4 来源复核与明确差异

入场按源码哈希及真实命令重建 v0.3.5，日志 [previous_baseline](../logs/v0.4.1/20261013T222851_941152_previous_baseline.log) 退出0。本轮随后四阶段逐项构建及独立审计通过，不能只用历史进度认定接口完成。入场 [source_snapshot.json](../logs/v0.4.1/source_snapshot.json) 与最终 [source_verification.json](../logs/v0.4.4/source_verification.json) 比较：原V7 md/tex/pdf、路线图、已接受模型合同/scope、Lean/mathlib锁文件和旧数学模块未修改。

实际差异逐项登记：

- 路线图 §10 与 §17.2 仍有“待实现”和未勾框，现已落后于本轮源码；路线图保持不动，当前状态见 PROGRESS 与各阶段 acceptance。
- 本轮证明 CP=2Lx 的保守 Poincaré，不是原 (5.1) 精确 π 常数；K=32μ(ε+2κ)Lx² 和 threshold 使用本轮CP，没有沿用旧精确常数数值证书。
- 光滑延拓、C(K) 一致范数路径与加权路径假设强于 (6.6)/W¹,∞ 弱范围；不静默称为完整V7。原方程只在内部时间/全矩形成立，不要求域外PDE。
- 原文 (2.4) 旧三个点态实现已扩展到全部五个场不变量；历史标注保留，用新注说明范围，不删除旧证据。
- 源文没有新增已确认公式错误。本轮不改原归一化、PEC、初值范围，不增加磁约束、吸收正下界或权重上界。

指定PDF副本仅追加已验证范围；备份、哈希、定位、结构与视觉检查在 logs/v0.4.4/pdf。原PDF不变；其具体标注范围见现有标注账本。
''';p.write_text(s)
print('Updated README, PROGRESS and inventories; original sources/locks/old proofs unchanged.')
