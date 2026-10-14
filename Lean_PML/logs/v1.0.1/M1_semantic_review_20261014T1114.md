# M1：一般零迹光滑场到现有 H₀¹ 图闭包的复核

本记录只审查本轮新增数学证明，不代替根工程统一构建和全量 Audit。

- 新文件：`LeanPML/Rectangle/SmoothWeakClosure.lean`。
- SHA-256：`3a3444e5ad1c04f649c69001ec12db58d14673fb7f44a59b6c2eaaed3b54a00a`。
- 主定理：`LeanPML.Rectangle.smoothToWeakH1_mem_zeroBoundaryGraph`。
- 全部输入仅为非退化矩形 `D`、旧类型 `SmoothField` 中的函数 `f`、四边实际零值 `ZeroBoundary D f`。
- 未输入逼近序列、图闭包成员、Green、Poincaré 或任何目标能量结论。

## 已核对的证明链

1. `exists_partial_bound` 由闭矩形紧致性及真实偏导连续性推出统一常数 M；`norm_le_four_distances` 对四条坐标切片使用 HasDerivAt 和中值定理，得到 |f|≤M×距相应边的距离。
2. `boundaryCutoff` 是四个实际 C∞ smoothTransition 的乘积。δ>0 时，其拓扑支撑包含在 [xlo+δ,xhi−δ]×[ylo+δ,yhi−δ]，该闭集紧致并严格包含于原开矩形；`cutoffTest` 因而确为原定义中的 TestFunction。
3. `cutoffTest_dx`、`cutoffTest_dy` 从真实切片 HasDerivAt 通过乘积和链式法则得出。`cutoffTest_partial_bound` 的两个导数分别受 4BM+M 控制；1/δ 因子由零迹线性距离估计抵消。没有只控制函数而遗漏梯度。
4. δ_n=1/(n+1)。每个内部点在 n 足够大时落入距四边 >2δ_n 的内核；截断在该点邻域恒等于 1，因此函数及两个真实偏导最终相等。
5. `smoothToL2_tendsto_of_bounded_eventuallyEq` 对平方差使用真实 Bochner 积分支配收敛，统一常数在整个有限测度矩形可积。通过 norm_toL2_sq 和平方根连续性得到实际 L² 范数收敛。
6. `cutoffSequence_toL2_convergence` 对函数、x 偏导、y 偏导分别调用第 5 步。主定理使用有限乘积拓扑与子类型拓扑组成原有最大值 H¹ 图范数收敛；闭集包含序列极限。
7. `rectangleBubble_weakH01` 用旧多项式泡函数实际调用一般桥接，且调用旧定理证明其 L² 类非零。该函数是全平面多项式，未作为内部紧支测试函数输入；本次未另外新增“此多项式没有紧支撑”的否定性定理，因为桥接调用本身完全不要求该条件。
8. `smooth_zero_mem_weakZeroFieldDomain` 与 `smooth_trace_zero_mem_weakZeroFieldDomain` 将结果接回现有 L² 值域，沿用旧代表无关的迹定义。

## 实际验证

- 模块构建：`20261014T111324_867759_M1_module_build.log`，`lake build LeanPML.Rectangle.SmoothWeakClosure`，退出 0。
- 类型及公理：`20261014T111402_861413_M1_types_and_axioms.log`，退出 0。
- 审计源：`M1_Audit_20261014T1113.lean`。
- 主要五条交付定理只依赖 `propext`、`Classical.choice`、`Quot.sound`；无 sorryAx。
- 初始失败和修复日志均保存在本目录，没有覆盖旧记录。

M1 本身没有尚未完成的数学子项；根入口接入、全量构建和审计由父任务统一完成后验收。
这不表示 W¹,∞ 乘积、提升唯一性、加权传播或弱原系统总装已经完成，也不改变 v0.5 主定理的强正则性输入。
