# M2 独立语义审查（只读）

审查日期：2026-10-14。审查人：并行子任务 m3_uniqueness。
本记录核查声明、定义和证明调用链；不替代父任务的最终构建/公理审计。
没有修改被审查源码。源码快照：

- `LeanPML/PML/WeightedForcing.lean`：`96b8e69b6b5fd6e5ac51b4977bf40a00dd1bd28cfc2cefdb4774f3002315a109`
- `LeanPML/PML/AuxiliaryWeightedEvolution.lean`：`57a3a0b7245cff625446fa38d588327543612e7d82e86559b8a141b88a43360b`

## 结论

未发现把全时段加权成员、加权导数或目标范数估计藏入输入的问题。
当前代码严格支持“加权强迫算子、导数值估计、由普通 L² 演化构造加权历史并识别原场”。
尚不能登记完整场版 (5.7)、精确 (5.8)、C² 加权正则性传播或弱原系统主定理。

## 逐项核查

1. `weightedForcing` 以普通 `ScalarL2` 为输入。由已证 `w*m²≤B` 构造有界的 `sqrt(w)*m`，输出实际 `WeightedL2` 的平方根坐标。没有假定 `w` 本身有界，零区坐标由定义和系数界直接证明为零。
2. `physicalL2_weightedForcing` 在正区约去 `sqrt(w)`，零区使用单独的 `hzero`。实际吸收调用 `physical_xAbsorptionLift` 从非负吸收及 `a=0` 推出两吸收为零，未新增吸收正下界。
3. `auxiliaryRateX` 的物理恢复为 `r*h-p*l`；`auxiliaryRateX_norm_sq` 保留原文未编号导数估计的因子 `2*c*S`。`auxiliaryRate_weak_norm_sq` 的 x/y 方向通过 `C.swap` 正确交换，梯度坐标与 H(div) 通量坐标均来自现有真实弱图空间。
4. `auxiliary_derivative_weighted_representative` 有真正 `HasDerivAt φ dφ t` 输入，再以原演化识别导数值。其结论只给普通 L² 导数的加权代表；注释正确地没有将其称为 φ 在加权范数中的可导性。
5. `auxiliaryWeightedHistory` 以唯一的初始加权元素 `W₀` 为输入，在实际加权空间积分已构造的右端。后续连续性/求导/识别证明都先从连续性取得 Bochner 可积性，没有利用不可积积分的总定义。
6. `physical_auxiliaryWeightedHistory` 的 `φ` 只有普通 L² 闭区间连续性；`hODE` 仅在 `(0,T)` 给真实导数。将物理恢复连续线性映射移过实际时间积分后，以普通 L² 的 FTC 识别给定原场。全时段加权成员因此是结论，而不是输入。
7. `auxiliary_weighted_membership` 通过已证 `physicalL2_range_iff` 给出 `sqrt(w)*φ(t)` 的真实 L² 成员及零区 a.e. 为零。`W₀` 与 `φ(0)` 的恢复相等包含正确的初始零区条件，未由 `p=r=0` 单独推断任意原场为零。
8. `continuousOn_auxiliaryWeightedHistory` 的结论覆盖 `[0,T]`；`hasDerivAt_auxiliaryWeightedHistory` 只在 `t∈(0,T)` 证明普通双侧导数。后者使用内部邻域连续性，无端点 PDE 或端点双侧导数输入。`T=0` 时初值恒等式及成员识别仍成立，内部求导结论为空，不推出额外端点导数。
9. `auxiliary_weak_field_membership` 通过图空间的连续坐标投影得到普通 L² 梯度/通量连续性，因此没有将逐点连续或逐点可导冒充 L² 正则性。

## 必须保留的范围限制

- 当前演化形式是 `φ_t = r*h-p*l`。输入未要求也未推出 `l=h+φ`，故不能将本构造直接登记为阻尼形式 (5.7) 的完整场版，更不能据此给 (5.8) 完成勾。
- 精确 (5.8) 仍需利用 `l=h+φ`、非负阻尼的传播算子/变常数公式和时间积分平方估计，保留 `2`、`4*c*S` 常数。当前仅构造强迫的空间提升和另一种严格历史表达。
- 新历史具备闭区间加权连续和内部真实加权可导；没有证明 C²，亦没有证明来自同一原解的导数层再次满足相应演化。不能因一般定理可再次调用，就把实际导数层接口登记为完成。
- `auxiliary_weak_field_membership` 的 u、Λ 是真实弱图路径，但仍是分别给定的路径。全部原八方程、空间关系、历史提升及兼容保持不在本文件的推导范围。
- `SpatialAbsorption` 是低层全底空间有界代表。若对外声称仅有矩形内幅度要求，仍需引用/建立内部延拓代表与原区域系数一致的桥接；这两个模块本身没有取消或替代该桥接。
- 当前“加权路径”是显式构造的 `auxiliaryWeightedHistory`。它的恢复与原普通 L² 路径相等，因此可以称为原场的一个已识别加权表示；不要把原普通 L² 类型的 φ 直接写成已证加权 HasDerivAt 而省略表示说明。

## M3 的具体未证目标

本轮 `weakCoefficientGraphMap_mem` 证明真实区域 W¹,∞ × H₀¹ → H¹ 的乘积法则。
第一条尚未兑现的边界连接是：对任意 `m : RegionalWeakCoefficient D` 和 `g : zeroBoundaryGraph D`，证明
`weakCoefficientMul D m g ∈ zeroBoundaryGraph D`。
其下一条必要引理是：对每个内部紧支光滑测试 f，实际弱 H¹ 场 `m*f` 可由同域内部紧支光滑函数在三坐标 L² 图范数中逼近。再以乘子图连续性推广到一般 g。

这仍不完成 §5.3：还需分离系数的横向弱导数为零的实际入口、方向零导数与零迹推出切片/场为零（或等价的方向 Poincaré）、以及零水平集上的弱梯度性质。只有先由原差值约束推出全域弱梯度为零，才能调用既有 `weak_zero_of_gradient_zero`。当前没有将该末步冒名为提升规范唯一性。
