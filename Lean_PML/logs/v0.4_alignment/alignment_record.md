# v0.4 对齐修复记录

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

旧中间 SmoothZeroOn/SmoothStaticAt 是已由初值与演化产生的结论；推荐最终入口不把它们、Green、Poincaré、交换或能量结论外传为待证字段。独立 [语义检查](semantic_review.md) 展开了最终入口及所有正则性结构；[实际类型输出](../../logs/v0.4_alignment/20261014T000341_178709_interface_types.log) 可复查字段。最终构造只要求μ≠0，能量主定理的材料正性/小量条件仍须在后续调用时提供。

## 修改清单与验证

新增3个正式模块：ParameterCertificate、ClassicalSystem、RegionalCoefficients。五个旧Lean模块只改说明注释；没有重构已有能量、等价、Green或Poincaré证明。LeanPML.lean/Audit.lean追加导入与53项审计，原537项保留。日志脚本仅扩展安全阶段名为 v0.4_alignment，仍用参数数组执行命令、排除路径穿越、时间戳独立保存日志。

- [完整构建](../../logs/v0.4_alignment/20261014T000055_917026_lake_build.log)：退出0，2940 jobs。
- [独立公理审计](../../logs/v0.4_alignment/20261014T000341_178705_axioms_audit.log)：退出0，590个声明；仅propext/Classical.choice/Quot.sound，无sorryAx。
- [类型检查](../../logs/v0.4_alignment/20261014T000341_178709_interface_types.log)：退出0；另有人工作用域/字段复核。
- 失败记录保留：区域weighted MemLp的首次`rw`未约化函数应用，改用congrArg传递点值等式；PDF首次读批注数组方式错误后修复；首次版式预检发现新页4注释撞页眉，未写入目标PDF，改至空白处后通过。它们均未覆盖历史。
- [证明验收与哈希](verification.json)、[最终验收](acceptance.json)。

## PDF对齐

18页与原正文可选文本保持；旧195个批注均保留，新增5个，其中只有1个红勾。第3页补古典空间证据说明，第4页补双向古典范围，第7页补区域幅度说明，第15页标独立保守参数证书并说明旧c不能迁移。未把假设、精确π常数、原(10.1)配置或v0.5主定理打勾。

[标注计划](pdf/annotation_plan.json) 和 [最终结构检查](pdf/annotation_result.json) 对应实际声明及本轮成功日志；[逐页视觉检查](pdf/visual_review.json) 已通过。原图、旧批注、页序和版框均保持，新增文字与原内容无重叠。两次修改前备份独立保留；首次预检失败的计划/备份登记另存 attempt01，未覆盖旧阶段备份。

本轮四项对齐均已补齐；可按上述明确强正则性范围进入 v0.5.1 的最终合成。尚未完成的弱空间、传播、规范及存在唯一性不属于本轮已证范围。
