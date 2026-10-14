# M3 数学补齐记录（2026-10-14 12:04）

本记录只登记本轮新增且实际编译、公理审计通过的子链；不据此单独宣布全部 v1.0 主定理完成。

## 已完成的证明链

1. `Rectangle.HasWeakPartial.zero_on_open`：真实弱偏导由内部测试分布定义；函数在开子域 a.e. 为零，则弱偏导也在该处 a.e. 为零。证明利用测试函数支撑外导数为零与 mathlib 的分布基本引理，没有把目标梯度零作为输入。
2. `PML.hasWeakPartial_y_of_separated_x`、`hasWeakPartial_x_of_separated_y`：区域有界系数值在 Ω 内分离，Fubini 加一维切片真实 FTC 推出横向弱偏导零。所有乘积可积性先由实际 L² 乘积证明。
3. `SeparatedRegionalWeakCoefficients.transverse_zero`：区域 W¹,∞ 的实际分布弱导数具有上述横向零值。结构只保存 `RegionalWeakCoefficient` 及域内分离值；不含横向零导数结论，不要求全轴 C∞ 或域外幅度界。
4. `PML.HasWeakPartial.mul_smooth`：直接测试 χφ，从真实弱偏导推出光滑乘子的弱 Leibniz 法则，作用对象不要求 H₀¹。
5. `coefficient_product_zero_of_transverse`：令 f=pg；由 ∂y f=0 得 ∂y(yf)=f。对通量 (0,yf) 和原 g∈H₀¹ 调用已证弱 Green，结合 p∂yg=0 得 ∫p g²=0。p≥0 推出 pg=0。x 方向同理。本步骤不要求 pg∈H₀¹，也不依赖尚在其他模块发展的粗糙图逼近。
6. `weak_lift_difference_zero`：从 g∈H₀¹、p∂yg=r∂xg=0、Z 上梯度零，推出 g=0。上一步得到 pg=rg=0；连续区域代表使 Ω₊ 为开集，局部性与 Z 条件拼合后调用弱 Poincaré。原文附加 bg=0 在这条已证等价路线中不必使用，没有删除原文约束。
7. `Weak.CompatibleLift.u_unique`：从同一 `Weak.OriginalState` 的两个实际合法提升出发，差值约束由磁通量和 Qx/Qy 重构相减推出；Z 上梯度差由加权物理恢复的零区性质推出。未将这些差值目标放进结构。
8. `CompatibleLift.state_unique`、`energy_independent`、`twoLayerEnergy_independent`：u 唯一后 polar 确定 q；flux 确定物理 ψ；`physicalL2_injective` 确定加权 ψ。由完整实际 `FieldState` 相同得到原 `fieldEnergy`/`twoLayerEnergy` 相同。
9. `nonzero_lift_energy_choice_call`：使用既有二维物理区 bump 的非零 L² 证据，构造非零原瞬时电场数据及一个合法提升，再与任意同原场合法提升调用能量选择无关。这是瞬时数据/规范回归，不是 PDE 解存在性或非零演化解证书。

## 范围与真实输入审查

- 区域 W¹,∞ 的函数与弱偏导均为可测、有界区域代表，弱导数是实际分布测试关系；未用光滑函数名称代替弱对象。
- `SeparatedRegionalWeakCoefficients` 是二维区域弱导数表示加分离值识别。尚没有“由独立一维 W¹,∞ 数据自动构造整个二维结构”的便利桥接。结构本身无 C∞ 条件。
- 规范定理额外明确要求系数代表在 Ω 内 `ContinuousOn`。本轮没有证明任意既有可测 W¹,∞ 代表自动连续，也没有宣称已形式化代表选择定理。该输入只用于 Ω₊ 开集；它不同于要求全轴 C∞。
- `CompatibleLift` 是同一瞬时原状态的合法提升类：包含 polar、flux、Z/Q 重构以及真实 H₀¹/WeightedL2 成员，不是全时段原解定义。它没有 Green、目标能量、兼容保持或唯一性字段。
- 原系统从初值产生这些瞬时兼容关系的演化保持，需由父任务的原方程/历史模块调用。这里不把合法瞬时类成员资格当作全时段保持已证。
- 唯一性在 L²/H₀¹/加权等价类意义成立，不是任意代表每点相等；没有读取边界点或零区某点的 L² 值。
- 两层选择无关是两组合法状态的组合结论；两层来自同一解的真实时间微分仍由父任务路径接口证明。
- 全零、单向及双向吸收均保留；不除以 p、r 或 a，不要求吸收正下界。实际非对称系数回归 `separatedWeakOneZero_transverse` 调用真实 Fubini 定理。

## 验证证据

- `20261014T115043_353716_m3_weak_locality.log`：开集局部性编译成功。
- `20261014T115441_272244_m3_separated_locality.log`：分离/Fubini及局部拼合编译成功。
- `20261014T115835_239093_m3_lift_uniqueness.log`：完整规范差值证明编译成功。
- `20261014T115918_533502_m3_lift_audit.log`：13 个主要结论公理及结构类型审计成功。
- `20261014T120308_341423_m3_lift_choice_call.log`：合法提升、实际能量选择无关、非零瞬时调用编译成功。
- `20261014T120336_854522_m3_lift_choice_audit.log`：8 个主要结论与结构字段审计成功。
- 以上退出码均为 0，完整工作目录/命令在对应 JSON。失败修复日志保留（114803、115212、115253、115733、120106、120135 等）。
- 审计只有 `propext`、`Classical.choice`、`Quot.sound`；无 `sorryAx`。未修改 root/Audit、旧源码、依赖或原始材料。根构建及最终全集审计由父任务接入后另行保存。

## 当前源码 SHA-256

- `LeanPML/Rectangle/WeakLocality.lean`：`43ff7920f2527c92fb7d590891af7b79546fa018b8179b4eb7f294416cb63f97`
- `LeanPML/PML/SeparatedWeakCoefficients.lean`：`ea94d8a606e8ba30c673482e5cf2d2def03dc64a7ac4a6258eb35e65a325b2b5`
- `LeanPML/PML/LiftUniqueness.lean`：`0aa92314b0301de74880e00bb1cc5a93b5b63f8881dbcdb23386b7005106f831`
- `LeanPML/PML/WeakLiftCompatibility.lean`：`e98e0f565dce6fe3d2a06d9480b91a3a834d91815789572156a357912bc4970c`
