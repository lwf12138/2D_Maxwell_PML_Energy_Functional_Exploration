# M1 / M3 最终独立语义审查

日期：2026-10-14。只读源码审查；未修改正式源码。本记录审核声明类型、结构字段、证明依赖和实际调用，不替代父任务最终完整构建与公理审计。

## 审查快照

- `LeanPML/Rectangle/SmoothWeakClosure.lean`：`3a3444e5ad1c04f649c69001ec12db58d14673fb7f44a59b6c2eaaed3b54a00a`
- `LeanPML/PML/WeakCoefficients.lean`：`9b12ab46128b9e8f0929e128621782f940fd50a1524f330dbb43e110942ac8f7`
- `LeanPML/PML/WeakCoefficientExamples.lean`：`1d0f9b483239534f86540a49e3c9cac4ece87d0b12bd6763bce19a35f7c3725f`
- `LeanPML/Rectangle/WeakDirectionalPoincare.lean`：`c5932453aeb8ad4e2a8764c4b77d99d918628c2c844c1d03ff230a5f918313a0`

## M1：指定的一般桥接已经在数学内容上补齐

核心声明 `LeanPML.Rectangle.smoothToWeakH1_mem_zeroBoundaryGraph` 的输入只有实际 `Rect`、原有 `SmoothField` 和四边 `ZeroBoundary D f`。输出正是现有 `smoothToWeakH1 D f ∈ zeroBoundaryGraph D`，没有改变 H₀¹ 定义，也没有输入闭包成员、逼近序列或目标收敛。

实际证明链逐项核对如下：

1. `exists_partial_bound` 从闭矩形紧致性及真实偏导连续性推出共同上界。`norm_le_four_distances` 通过四次一维中值估计，从零边界得到函数按到边界的距离衰减；没有把这一关键衰减假设进最终定理。
2. `boundaryCutoff` 使用 mathlib 的 C∞ 阶跃构造四边截断。`cutoffTest` 证明拓扑支撑落在严格缩小闭矩形，因此每项确为 Ω 内部紧支 C∞ 测试函数。δ 较大时截断可能为零，这不影响成员和后续收敛。
3. `cutoffTest_dx/dy` 以真实切片 `HasDerivAt` 求乘积导数。`cutoffTest_partial_bound` 使用距边界估计抵消 1/δ，得到与 δ 无关的两个偏导上界。没有对吸收系数除法。
4. `cutoffSequence_eventually_eq_with_derivatives` 对每个严格内部点先建立邻域上的截断恒等于一，再以 `EventuallyEq.fderiv_eq` 识别两个偏导，未把单点相等当作求导依据。
5. `smoothToL2_tendsto_of_bounded_eventuallyEq` 对实际平方差积分使用支配收敛。支配函数是有限矩形上可积常数；函数及两偏导分别调用。由 `norm_toL2_sq` 与平方根连续性得到真实 L² 商类范数收敛。
6. `cutoffSequence_toL2_convergence` 同时给出三个坐标的 L² 收敛；有限乘积及子类型拓扑组成原来最大值 H¹ 图范数收敛，最后用现有 H₀¹ 图闭包的闭性得到目标成员。这不是普通 L² 密度替代 H¹ 密度。
7. `rectangleBubble_weakH01` 实际调用一般桥接处理原矩形多项式泡函数 `(x-xlo)(xhi-x)(y-ylo)(yhi-y)`，并复用其 L² 非零证明。该函数没有以“内部紧支测试函数”为输入；因此满足本轮要求的非预先紧支非零调用。
8. `smooth_zero_mem_weakZeroFieldDomain` 与 `smooth_trace_zero_mem_weakZeroFieldDomain` 将结果接入现有实际 L² 值域/迹核，不只是孤立证明一个闭包命题。

M1 完成范围是旧 `SmoothField`（全空间技术 C∞ 代表）的四边零迹到现有 H₀¹ 图闭包。它不是任意弱 H¹ 的迹核刻画，也不自动给出一般 H¹ 局部磨光逼近。该区别不妨碍用户本轮指定的 M1 目标已经实现。

## M3：真实弱系数乘法的准确完成范围

`RegionalBounded` 的幅度输入仅作用于 Ω。零延拓用于普通 L² 乘子，`extended_ae` 保证整个计算域限制测度下与原系数相等。代码没有声称零延拓在跨边界意义上保持弱导数。

`RegionalWeakCoefficient` 的字段只有区域有界函数、两个区域有界导数代表及 `HasWeakPartial` 测试函数关系。这是具有有界可测代表的实际区域 W¹,∞ 表示；没有 C∞、Green、Leibniz 法则、能量或规范唯一性字段。它不是已经完成全部 Banach 结构的抽象 W¹,∞ 库，也尚不是完整的分离吸收 `p=p(x),r=r(y)` 入口。

`weak_product_test` 对系数的弱导数使用合法乘积测试函数 fφ，并将真实光滑测试偏导展开。`weakCoefficientGraphMap_mem` 将候选乘积图映射到弱 H¹ 图的闭集，以连续性从紧支测试的张成推广到 H₀¹ 闭包。输出真实 Leibniz 坐标及 **H¹ 成员**，没有输出 H₀¹ 成员。

`weakCoefficientMulCLM` 将已证图成员装为实际 H₀¹→H¹ 连续线性映射。`hasDerivAt_weakCoefficientMul` 从实际 H₀¹ 图范数导数推出乘积 H¹ 图路径的导数；没有由逐点导数推断图范数可导。

`weakCoefficient_nonzero_call` 复用旧真实二维 bump，通过一般乘积构造和常数 1 系数得到非零函数坐标。这验证非零空间调用，但不是一个低正则性系数的非光滑实例或弱 PDE 解。

## M3：方向 Poincaré 的准确完成范围

`poincare_integral_top_zero` 在真实 Green 中选 `(0,(y-ylo)f)`，由上边零值和下边乘子零消边界，再以非负平方积分证明仅含 y 偏导的保守界。x 方向复用旧 `poincare_integral_right_zero`。二者没有输入目标 Poincaré。

`weak_directional_poincare` 以同一图闭包方法得到

$$\|g\|_2^2\le (2L_i)^2\|\partial_i g\|_2^2.$$

`weak_zero_of_dx_zero`、`weak_zero_of_dy_zero` 的实际类型分别只输入一个偏导为零；它们没有要求另一个偏导为零。函数坐标先由方向估计为零，再以弱导数唯一性确定整个图为零。因此不是重命名旧 `weak_zero_of_gradient_zero`。

`nonzero_directional_poincare_call` 对任意 `Fin 2` 方向调用已证估计，输入为实际非零二维 bump。方向常数 2Ly 仅服务于此辅助估计，主能量的 CP=2Lx、K 与数值证书保持不变。

## M3 的首缺目标及后续依赖

第一条尚未证明的精确目标仍是：

`∀ (m : RegionalWeakCoefficient D) (g : zeroBoundaryGraph D), weakCoefficientMul D m g ∈ zeroBoundaryGraph D`。

下一条需要的引理是：对每个内部紧支光滑 f，实际弱 H¹ 乘积 m*f 在三个 L² 图坐标中可由同域内部紧支光滑函数逼近；再通过已证乘子图连续性推广到一般 g。本轮 M1 只处理已有光滑代表，不能直接套用于尚非光滑的 m*f。

另外仍须完成：

- 真正分离区域 W¹,∞ 系数入口，包括横向弱导数为零及与 p(x)、r(y) 原区域函数的识别；当前通用二维弱系数类型没有自动给出这些性质。
- 从同一原状态的两个合法提升得到差值约束的真实场层映射。
- 利用乘积 H₀¹ 保持和横向 Leibniz 后，可用已证方向零分离从 p∂y g=0、r∂x g=0 推出 pg=rg=0。但这些前置事实尚未接通，不能直接登记 pg=rg=0 已证。
- 从 g=0 于 Ω₊ 推出弱梯度在那里为零所需的零水平集/局部性结论；随后才能与 Z 上梯度条件合并并调用 Poincaré。
- 提升规范唯一性及能量与提升选择无关尚未完成。方向零分离只能标为 §5.3 的辅助子结论，不能给规范唯一性整体打勾。

## 验证与登记建议

本审查未发现隐藏目标结论的输入。M1 指定桥接可在最终构建和公理审计通过后登记完成；M3 只能登记上述通用区域弱乘积、方向 Poincaré及非零调用子项。不得将其登记为分离系数接口、H₀¹ 乘积保持或提升唯一性整体完成。正式总入口和最终审计由父任务负责，此处不以早先模块成功日志代替修改后全工程证据。
