# v0.3.4–v0.3.5 入场复核

用途：记录本轮依据的版本和历史状态差异；不是新数学证明。

- 原 V7 md、tex、原 PDF 与 v0.3.3 验收时哈希相同；模型合同和 Lean/mathlib 锁文件未变。
- 路线图 v0.3.2、v0.3.3 各五项已勾选，但段落“当前状态：待实现”和 §17.2 总表仍是旧文字。相对上次入场快照的实际差异保存在 roadmap_since_previous.patch。本轮不改路线图。
- 当前 README/PROGRESS 的 v0.3.2–3 已完成与源码一致；本轮再次 lake build 验证已有导入链。历史审计输出和退出码逐项复核见 previous_review.json。
- 旧证明源码 BalanceInterfaces、PrimitiveEvolution、SpatialBalance、BalanceBlocks、BalanceAbstract 与上阶段验收哈希一致；Coercivity/PhysicalControl 正式导入本轮基线构建。
- 沿用旧疑点：§8.2 严格 <B_sp 在零状态不成立，已用足够的非严格估计形式化，原文未改。本轮 §9 的假设与公式依赖按当前正文重读。
- PDF 入场为18页、168项批注；与v0.3.3最终哈希一致，详见 ../v0.3.5/pdf/read_only_inspection.json。当前阶段尚未据此添加新完成标记。
- 空间载体一般采用非空类型（二维 ℝ×ℝ 自带）；S≥0可由任一点的0≤p≤S推出。这不要求积分测度非零或吸收正下界。
