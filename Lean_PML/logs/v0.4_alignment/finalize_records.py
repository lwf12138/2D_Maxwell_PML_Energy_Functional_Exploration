from pathlib import Path
from datetime import datetime
import json,hashlib
r=Path.cwd();d=r/'logs/v0.4_alignment';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
v=json.loads((d/'verification.json').read_text());assert v['status']=='passed'
pdf=json.loads((d/'pdf/annotation_result.json').read_text());plan=json.loads((d/'pdf/annotation_plan.json').read_text())
# 主代理已逐页打开全部四张144dpi最终渲染图，检查正文/旧批注/新限定文字。
observations={3:'页顶空间可导限定清晰，与原页眉/标题及旧八式红勾均无重叠。',4:'两条页顶说明分别保留；新增古典范围说明位于旧说明与2.2标题间，文字未裁切，原公式/旧标记可读。',7:'左侧区域幅度说明位于空白页边，未盖住5.2/5.3或旧输入标记；右侧保守Poincare说明保持。',15:'§10末尾空白处的独立证书红勾及旧c失效说明清晰；未给原10.1/10.2打完成勾，11节标题/旧11.1标记完整。'}
visual={'status':'passed','reviewed_at':datetime.now().astimezone().isoformat(),'method':'主代理逐页查看最终PDF经Poppler重新渲染的144dpi整页图，结合脚本原文字符/旧批注矩形无重叠检查','pages':[{'actual_page':n,'printed_page':n,'image':f'final-{n:02}.png','sha256':sha(d/f'pdf/final-{n:02}.png'),'observation':s} for n,s in observations.items()],'clipping':False,'new_text_overlap':False,'old_annotations_preserved':True,'pages_count':18}
(d/'pdf/visual_review.json').write_text(json.dumps(visual,ensure_ascii=False,indent=2)+'\n');pdf['visual_review']='passed';(d/'pdf/annotation_result.json').write_text(json.dumps(pdf,ensure_ascii=False,indent=2)+'\n')
build=v['build'];audit=v['audit'];types=v['type_review']
record=f'''# v0.4 对齐修复记录

用途：逐项核对本轮四个修复线索，区分代码结论、正则性输入和后续任务。本轮结束在 v0.4，不发布 v0.5 主定理。

## 基线与历史更正

入场 [baseline.json](baseline.json) 保存69份源码、锁文件、文档和来源哈希；与旧 v0.4.4 验收登记的源码相比无差异。旧构建/审计确实成功，见 [旧日志复核](baseline_log_review.json)，但不将其作为修改后证据。原 V7 md/tex/pdf、模型合同、scope、路线图与三份锁定配置本轮均未修改；原双向等价及 OriginalAssembly 的代码哈希保持不变。

旧 v0.4.2 的“完成”登记只覆盖符号替换 K、阈值正性，漏了保守常数下的具体参数证书。本轮补齐，保留旧 acceptance 与历史文字，追加这个更正。没有发现原文新版本变化，也没有把旧参数在新常数下失败解释成原论文错误。

## 四项线索与修复

| 线索 | 入场结论 | 本轮实际结果 |
|---|---|---|
| 保守常数数值证书 | 确认缺少；CP=2Lx 和 K 符号式已有证明 | ParameterCertificate 使用真实 (-1,1)²：CP4、A3、K384；c=1/16384、S=1/65536；三条精确小量界→旧阈值等价→c≤c_*。旧c=1/128第二条为72>1，正式排除 |
| 吸收全轴幅度 | 旧 separated 入口确实较强 | RegionalAbsorption 只要求闭坐标区间界。内部 p∘clamp/r∘clamp 构造有界可测代表，证明闭域/a.e./权重/实际可积积分一致；推荐 originalRegionalFiniteIntervalProblem 实际从原p/r方程转入旧框架 |
| 空间导数证据 | 低层 OriginalAt/PrimitiveAt 仅为方程表达式；旧最高入口已有光滑代表依据 | ClassicalSystem 明列空间 DifferentiableAt，并推得坐标 HasDerivAt；由 SmoothStateData/LiftIdentified + μ≠0 产生证据，再实际调用双向古典包装及有限区间构造。旧证明未被判失效 |
| 强光滑与6.6说明 | 部分头部注释“由…推出”过强 | SmoothPaths、StatePaths、WeightedCalculus 改为“为兑现接口选择更强技术正则性”。加权成员/路径正则性全部保留；数学声明及旧证明体没有改为更弱结论 |

## v0.4 验收分类

| 阶段/要求 | 已证明并经本轮全工程重验 | 仍作为明确输入 | 后续范围 |
|---|---|---|---|
| v0.4.1 几何/代表/导数/四边迹 | 全矩形测度/Fubini、光滑代表的L²识别和迹/算子良定义；本轮另给古典偏导证据包装 | 非退化Rect，所用真实光滑代表；物理p/r仅闭坐标区间界、时间不变、分离 | 一般弱H¹/H(div)与W¹,∞类 |
| v0.4.2 Green/Poincaré | 真实四边Green及PEC消去；CP=2Lx估计；本轮补实际CP4/K384参数证书 | 对应光滑算子域及零迹条件，使用能量定理时材料正性/阈值 | 精确π常数，不沿用其旧数值证书；完整剖面/非零初值族属于v0.5.2 |
| v0.4.3 时空/普通和加权路径/两层迹 | 混合交换、C(K)→L²真实导数；加权恢复导数识别；PEC+u₀零迹→u迹、内部E_t迹 | 联合C∞技术延拓；UniformTimeJet一致范数条件；实际√wφ三层MemLp与加权路径连续可微；需要闭端点E_t迹且T=0时的初始迹 | 加权正则性自动传播(5.7)/(5.8)，由弱论文范围推出这些更强条件 |
| v0.4.4 历史/不变量/映射/总装 | 实际历史积分、五个场不变量保持、零区φ保持、全部八式反向及PEC；本轮推荐区域入口和古典包装 | 原八方程只在(0,T)×Ω，PEC在全四边；初始五兼容、u₀零迹、零区φ₀=0；实际LiftIdentified与OriginalLiftRegular；T=0必要初始导数层兼容 | 提升规范唯一性、一般非零不变量带源primitive系统、解存在唯一性；v0.5.1最终主定理发布 |

旧中间 SmoothZeroOn/SmoothStaticAt 是已由初值与演化产生的结论；推荐最终入口不把它们、Green、Poincaré、交换或能量结论外传为待证字段。独立 [语义检查](semantic_review.md) 展开了最终入口及所有正则性结构；[实际类型输出](../../{types}) 可复查字段。最终构造只要求μ≠0，能量主定理的材料正性/小量条件仍须在后续调用时提供。

## 修改清单与验证

新增3个正式模块：ParameterCertificate、ClassicalSystem、RegionalCoefficients。五个旧Lean模块只改说明注释；没有重构已有能量、等价、Green或Poincaré证明。LeanPML.lean/Audit.lean追加导入与53项审计，原537项保留。日志脚本仅扩展安全阶段名为 v0.4_alignment，仍用参数数组执行命令、排除路径穿越、时间戳独立保存日志。

- [完整构建](../../{build})：退出0，2940 jobs。
- [独立公理审计](../../{audit})：退出0，590个声明；仅propext/Classical.choice/Quot.sound，无sorryAx。
- [类型检查](../../{types})：退出0；另有人工作用域/字段复核。
- 失败记录保留：区域weighted MemLp的首次`rw`未约化函数应用，改用congrArg传递点值等式；PDF首次读批注数组方式错误后修复；首次版式预检发现新页4注释撞页眉，未写入目标PDF，改至空白处后通过。它们均未覆盖历史。
- [证明验收与哈希](verification.json)、[最终验收](acceptance.json)。

## PDF对齐

18页与原正文可选文本保持；旧195个批注均保留，新增5个，其中只有1个红勾。第3页补古典空间证据说明，第4页补双向古典范围，第7页补区域幅度说明，第15页标独立保守参数证书并说明旧c不能迁移。未把假设、精确π常数、原(10.1)配置或v0.5主定理打勾。

[标注计划](pdf/annotation_plan.json) 和 [最终结构检查](pdf/annotation_result.json) 对应实际声明及本轮成功日志；[逐页视觉检查](pdf/visual_review.json) 已通过。原图、旧批注、页序和版框均保持，新增文字与原内容无重叠。两次修改前备份独立保留；首次预检失败的计划/备份登记另存 attempt01，未覆盖旧阶段备份。

本轮四项对齐均已补齐；可按上述明确强正则性范围进入 v0.5.1 的最终合成。尚未完成的弱空间、传播、规范及存在唯一性不属于本轮已证范围。
'''
(d/'alignment_record.md').write_text(record)
# 现有进度只前置更正，不重写历史。
p=r/'PROGRESS.md';old=p.read_text();p.write_text(f'''# v0.4 对齐修复：已验收（2026-10-14）

本次只修复 v0.4 的范围、接口、参数证书和记录；未进入 v0.5。下方历史原样保留。**更正**：此前 v0.4.2 虽登记完成，但保守常数下仅有符号替换，具体数值证书当时缺少；现已补齐。

- 实际矩形 (-1,1)² 得到 CP=4、A=3、K=384；新 c=1/16384、S=1/65536 满足完整阈值，旧 c=1/128 在此常数下失败。
- 新推荐 `RegionalAbsorption.originalRegionalFiniteIntervalProblem` 只要求闭坐标区间吸收界；内部代表域内/a.e./权重/合法积分一致，没有全轴原系数界。
- 新古典解包装明列真实空间可导证据，并由已有光滑识别推出后实际用于总装。旧最高入口的光滑依据并非失效，底层方程表达式仍不自动给空间可导性。
- 修正“由6.6推出”的注释；联合C∞、C(K)和实际加权路径仍是明确更强正则性输入。

[本轮完整构建]({build})、[独立审计]({audit})、[类型检查]({types})均退出0；审计590个声明，只用标准基础公理。PDF第3/4/7/15页补5项准确限定（1个新参数红勾），18页和195个旧批注全部保留。

逐项“已证明／正则性输入／后续任务”见 [对齐记录](logs/v0.4_alignment/alignment_record.md)，源码与受保护文件哈希、实际失败及成功记录见 [验收](logs/v0.4_alignment/acceptance.json)。旧 acceptance 未覆盖。下一步允许进入 v0.5.1 的所选强光滑类最终合成；弱空间、精确π常数、传播、规范、适定性不宣称完成。

---

'''+old)
p=r/'README.md';p.write_text(p.read_text()+f'''\n本次对齐验证： [完整构建]({build})、[独立审计]({audit})、[类型检查]({types}) 均退出 0；共审计590个声明，新增53项。PDF页3/4/7/15已按实际范围对齐，详见[账本](docs/pdf_formalization_marks.md)及[视觉检查](logs/v0.4_alignment/pdf/visual_review.json)。\n''')
# 现有清单追加，不覆盖旧阶段结论。
p=r/'docs/source_inventory.md';p.write_text(p.read_text()+'''\n## 2026-10-14：v0.4 对齐复核追加\n\n[入场哈希](../logs/v0.4_alignment/baseline.json) 与旧v0.4.4已登记源码全部一致；旧日志真实有效，但仅对应当时版本。本轮新源码由[新验收](../logs/v0.4_alignment/acceptance.json)关联本轮构建/审计。原V7 md/tex/pdf、proof_audit、路线图、合同/scope与锁定配置未变，未发现来源版本漂移。\n\n范围更正：旧保守常数仅有符号K/threshold推论，数值证书本轮补齐；原§10用精确π常数，旧c不可移到CP=4。区域幅度入口、古典空间导数包装和强光滑注释也本轮补齐。具体差异、完整证据及失败修复记录见[对齐记录](../logs/v0.4_alignment/alignment_record.md)。PDF副本独立备份后追加5项范围标注；原正文未改。\n''')
append='''
## 2026-10-14：v0.4 对齐的逐项追加

以下均为本轮实际源码、构建、公理和类型复核；不覆盖上方历史。证明范围明细见 [对齐记录](../logs/v0.4_alignment/alignment_record.md)，成功日志及哈希见 [本轮验收](../logs/v0.4_alignment/acceptance.json)。

| 对应条目/来源 | 本轮准确声明 | 本轮结论与范围 |
|---|---|---|
| T08–T09；(5.1)保守版、(5.2)–(5.3)、§10对照 | `LeanPML.Rectangle.ParameterCertificate.unitSquare_parameter_certificate`、`unitSquare_explicit_smallness`、`oldC_not_le_threshold` | 真实矩形CP4/A3/K384及新精确参数证书补齐；旧c在新常数下8cAK=72>1。未证明原(5.1)π常数，未升级原(10.1)/(10.2)例子 |
| T09–T10；(5.3)/(5.5) | `LeanPML.Rectangle.RegionalAbsorption.coefficients_eq_closed`、`coefficients_ae`、`weights_ae`、`weighted_memLp_iff` | 原p/r仅闭坐标区间界，内部有界代表域内/a.e.一致；无吸收正下界、无权重本质有界输入 |
| T11、T18；(6.2)/(7.7) | 同前缀 `energyDensity_integrable`、`fieldEnergy_eq_regional_integral`、`dissipationDensity_integrable`、`fieldDissipation_eq_regional_integral` | 已有实际能量/耗散等于原区域系数的合法全矩形积分；不是另建无联系能量，也不是新增PDE能量律 |
| T01、T04；(2.1)–(2.6) | `LeanPML.PML.Concrete.original_to_primitive_classical_rectangle`、`primitive_to_original_classical_rectangle`、`originalClassicalOn_of_liftIdentified` | 原E/H及primitive u/E/Λ有实际空间可导证据；旧低层式仍是表达式。由已有光滑识别派生证据；双向含八式/PEC，仍为所选强正则类 |
| T11–T12及具体总装 | `LeanPML.Rectangle.RegionalAbsorption.originalRegionalFiniteIntervalProblem`、`originalRegionalFiniteIntervalProblem_second_R_continuous` | 从原区域系数方程经古典包装接入已证Green/Poincare，给P_tt连续性；全时段兼容/能量不在最终输入。还没有发布v0.5.1主定理 |
| (6.6)范围说明 | SmoothPaths/StatePaths/WeightedCalculus中文说明更正 | 联合C∞、一致范数、加权成员及路径正则性是额外技术输入，不由弱论文条件推出。传播、弱范围、提升规范和适定性仍未完成 |

新增源码位于 [ParameterCertificate](../LeanPML/Rectangle/ParameterCertificate.lean)、[ClassicalSystem](../LeanPML/PML/ClassicalSystem.lean)、[RegionalCoefficients](../LeanPML/Rectangle/RegionalCoefficients.lean)。旧v0.4.2“完成”漏数值证书的登记已作本次追加更正；旧日志与验收文件保留，不能将本轮结果倒写到旧证据中。
'''
for name in ['theorem_inventory.md','claim_ledger.md']:
 p=r/'docs'/name;p.write_text(p.read_text()+append)
# PDF账本从最终计划写入，每条列完整定理/输入范围/相同验证证据。
p=r/'docs/pdf_formalization_marks.md';s=p.read_text()+f'''\n## 2026-10-14：v0.4 对齐修复标注追加\n\n本轮只追加；旧195个批注全部保持，原文/页序/版框不变。最终18页，增加5项，其中1个矢量红勾，其余为限定说明。编辑前备份及哈希见 [backup](../logs/v0.4_alignment/pdf/backup.json)，首次版式预检失败的备份信息另存 [attempt01](../logs/v0.4_alignment/pdf/attempt01_backup.json)。\n\n构建证据：[lake build](../{build})；公理审计：[Audit](../{audit})；类型/假设复核：[实际类型](../{types})、[独立审查](../logs/v0.4_alignment/semantic_review.md)。结构及逐页视觉检查通过：[检查](../logs/v0.4_alignment/pdf/annotation_result.json)、[视觉](../logs/v0.4_alignment/pdf/visual_review.json)。\n\n| 实际/印刷页 | 公式或定位 | 类型/新增标记 | 完整声明与文件 | 准确范围及剩余接口 |\n|---|---|---|---|---|\n'''
for e in plan['entries']:
 names='<br>'.join('`'+x+'`' for x in e['theorems']);files='<br>'.join('['+Path(x).name+'](../'+x+')' for x in e['modules'])
 mark=('✓ ' if e['kind']=='tick' else '说明，无新勾：')+' / '.join(e['draw']['lines'])
 s+=f"| {e['page']}/{e['printed_page']} | {e['formula']} | {mark} | {names}<br>{files} | {e['scope']} |\n"
s+=f'''\n修改前SHA256：`{pdf['sha256_before']}`；修改后：`{pdf['sha256_after']}`。定位与稳定ID见 [annotation_plan](../logs/v0.4_alignment/pdf/annotation_plan.json)，重跑会识别同ID而不叠加。原第3/4页红勾的低层引用范围容易被理解为方程自带空间可导，本轮追加古典包装声明，未删除旧记录。第7页保留“CP=2Lx非原精确值”；第15页新勾明确属于替代证书，不标原数值例完成。第10页既有“光滑/加权输入、非自动传播”说明仍准确，无新结论可勾，故只更新代码/账本说明。\n\n本轮没有给v0.5具体主定理、精确π常数、弱理论、传播、提升唯一性或解存在唯一性增加完成标记。\n'''
p.write_text(s)
print('视觉记录、README/PROGRESS及四份既有清单已追加本轮实际结果；待最终清单一致性检查。')
