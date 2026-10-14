# v0.5.1 独立类型与范围复核

复核者：geometry/profile 子代理；本记录只说明实际逐段读过的输入、调用链和输出，不代替构建或全工程审计。时间：2026-10-13T17:00:33.078621+00:00。

## 已核对事项

1. `SmoothCompatibleSolution` 输入包括材料正性、阈值、原八变量、历史初值、`SmoothStateData`、显式正则性、`LiftIdentified`、原方程、初始兼容、零区初值、四边 PEC、u0 零边界及 T=0 的初始导数层兼容。没有把 Green、Poincaré、微分交换、全时段兼容、耗散非负、单调性或积分平衡设成字段。
2. `SmoothStateRegular` 展开后是 C(K) 路径连续/可微和实际 sqrt(w)φ 三层 L² 成员、加权曲线连续/可微。其可微性不指定能量导数或耗散公式。`SmoothTimeJet` 的两个 HasDerivAt 只绑定实际函数的相邻时间层；混合微分交换由既有 TimeSpace 定理导出。
3. `LiftIdentified` 的八个函数相等把实际积分历史 u/q、磁场旋转缩放 Λ、Λ−∇u 的 φ 与光滑槽绑定。不是用任意两份独立状态代替同源路径；域外相等只是技术延拓识别，不要求 PDE 在域外。
4. `problem` 调用 `originalRegionalFiniteIntervalProblem`。该入口先从光滑识别及 μ≠0 得到真实原场空间可导；再将原 p/r 改写成闭矩形内相同的内部截回代表。调用者没有原 p/r 的全轴幅度假设。`RegionalAbsorption` 只在闭坐标区间要求非负与幅度。
5. 完整原方程范围保留 `(0,T)×Ω`；闭区间静态约束由保持及连续性取得。T=0 仅额外要求 `InitialDerivativeCompatible` 的初始极化和零区约束，未由空内部方程推导端点 PDE。最终能量律仍只在 Ioo，单调比较及积分平衡覆盖 Icc。
6. `energy/dissipation/graphSquare` 直接沿用 energy7/dissipation7/graphSquare7。原系数能量与耗散的积分相等、可积性分别交付；不存在仅依赖不可积积分总定义的证明。
7. `electricL2/polarL2/magneticXL2/magneticYL2` 从输入原场 MemLp.toLp 构造，以 a.e. 代表证明等于状态/重构槽，故 physical_current_bound 实际控制输入 E/H/P。`auxiliary_initial_bounds` 的直接类型仍是兼容重构控制包；其与输入原 Z/Q 的对应依赖先前全时段兼容保持，不应把裸类型误读为再次独立证明完整八变量等价。
8. 实际 CP 使用 `poincareConstant D=2Lx`，报告没有冒称精确 π 常数。报告明确 C∞ 延拓、全轴技术正则性及加权正则性比 V7 弱表述强，未声称自动传播、存在唯一性或严格衰减。
9. `SmoothEnergyConclusions` 是输出包，`main_energy_estimate_smoothRectangle` 逐项调用已经由原模型构造的问题；该包没有回填为输入。预算保持空间项1/2与 Debye 项 μτ/(4κ)，积分平衡单独调用 FTC 所需连续性。

## 结论与边界

所读最终入口未发现把目标结论藏入输入字段、偷加全域正吸收、扩大 PDE 时间区间、或沿用旧精确 CP 数值的问题。复核只覆盖下列文件的主入口和相关字段/调用链，不把本记录称作独立重新验证每个旧证明。正式成功构建和审计仍由根任务保存。

## 被复核版本

- `LeanPML/PML/MainSmoothRectangle.lean`: `62f7a7d7826d916d2283a3a84a62c92dceb9f65bc445f6d2815cb927d7a1538e`
- `reports/smooth_theorem.md`: `c32b8c4bba254a8557f75892301946b28b595d0f18eb6633e9c7ebb49151a462`
- `LeanPML/Rectangle/RegionalCoefficients.lean`: `f7a5bf667a9dc9d5914f63c9747b95372227922de41912fcf6a8a44ff0277623`
- `LeanPML/PML/ClassicalSystem.lean`: `63ea7a2dae932b24c15bf71f10711bdcd8c0754177b43e917d503f8305125d8a`
- `LeanPML/PML/OriginalAssembly.lean`: `e4bb5214237490b05b608fc289f67aa84e550e8cb9ac2266a94ed4bce674572e`
- `LeanPML/Rectangle/StatePaths.lean`: `915c8204230cbb954cfe4403be3b3ce7c7ac9cc24ba78ca824b9066f906c9850`
- `LeanPML/Rectangle/SmoothPaths.lean`: `aa905c50a6618435f1c021c3473ddc0777f9d140c6aabd07c0fb899b0e9a2288`
