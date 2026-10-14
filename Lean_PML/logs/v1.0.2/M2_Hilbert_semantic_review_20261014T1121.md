# M2：精确耗散 ODE 时间估计

新文件 `LeanPML/Analysis/DissipativeMemoryEstimate.lean`，SHA-256
`f2800b02e5d20c57c78bce79c7fed8fcd357d88868539bbc0d2dc86a04e0737b`。

主声明 `LeanPML.Analysis.dissipative_memory_square_bound` 的输入为：

- 真实实内积空间 H；固定连续线性算子 B；已需在具体调用处证明的算子耗散性 ⟪X,BX⟫≥0；
- 实际 W,F : ℝ→H，在 [0,T] 连续；
- 仅在 (0,T) 的真实 HasDerivAt W (−B(W s)+F s) s；
- t∈[0,T]。

结论：

$$\|W(t)\|^2\le 2\|W(0)\|^2+2t\int_0^t\|F(s)\|^2\,ds.$$

证明没有输入该范数估计。对 sqrt(‖W‖²+δ) 使用 norm_sq/sqrt 求导规则，再由耗散性和 Cauchy–Schwarz 得到导数≤‖F‖。导数右端从实际连续 W,F 及 B 构成连续函数，因而可积；调用允许内部求导的 FTC，无端点 PDE/导数假设。取 δ=ε² 消去正则化，得到 ‖Wt‖≤‖W0‖+∫‖F‖。时间 Cauchy 平方界由实际积分非负平方 (t‖F‖−∫‖F‖)² 得到，t=0 单独化简。最终使用 (a+b)²≤2a²+2b²，保留精确 2 与 2t。

这只是低层真实路径估计；只有实际 WeightedL2 路径调用它、证明算子耗散性和 forcing 平方界，再合法积分两个方向后，才能登记 V7 (5.8) 场版本。它没有证明一般解存在性，也没有从有限范数估计推断 C²。

模块构建：`20261014T112020_927869_M2_memory_estimate_build.log`，退出 0。
专属类型/公理审计由 `M2_HilbertAudit_20261014T1120.lean` 保存，日志为 `20261014T112044_259631_M2_memory_estimate_axioms.log`。
正式总入口接入、全量构建及实际加权调用由父任务统一完成。
