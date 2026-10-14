# v1.0 closeout：逐项语义核对（2026-10-14）

本记录区分当前可调用版本与 V7 原文逐项对齐。基线 `baseline.json` 对照上一轮 completion 快照：原 92 个正式源码与锁定配置匹配；本轮不覆写旧验收。新源码均由默认入口导入，完整类型另见 `TypeReview.lean` 及实际 type_review 日志。

## 六项清单

| 项目 | 本轮准确状态 | 证据及未覆盖部分 |
|---|---|---|
| (6.6) → jet | 需要的 λ_tt 推导、新入口及非零调用完成；不声称与论文正则性逻辑等价 | `V7TimeRegularity.fluxDot_eq`、`flux_second`、`toOriginalJet`、`main_energy_and_auxiliary`；仍保留 T=0 初始导数兼容 |
| (8.4)–(8.8) | 完成直接原变量控制及初值界 | `OriginalInterval.auxiliary_reconstruction`、`original_auxiliary_control`、`original_auxiliary_initial_control`，结论 Z/Q 直接取 `O.fields` |
| 命题 2.1 反向 | 所列弱图路径类的八式、真实导数、PEC 及兼容完成 | `primitive_to_original_WeakAt`、`primitive_to_original_WeakOn`、`reverse_compatible`，非零 `reverse_static_call`；不是任意分布解等价或一般适定性 |
| (5.7) 空间核 | 加权商类的算子指数核及原解调用完成；与逐点标量核的代表元识别仍未完成 | `operator_memory_formula`、`auxiliary_operator_memory`、`OriginalInterval.operator_memory_both`、非零 `kernel_static_call`。未证明 exp(t M_p) 的作用等于代表函数 e^(tp(x)) 乘法，不把此项登记为原公式逐项完全对齐 |
| 一般 W¹,∞ → 连续代表 | 未完成 | `WeakRegionalAbsorption.p_continuous/r_continuous` 仍是明确输入；已存在区域延拓、a.e.、乘子与积分识别，未重复实现 |
| (5.1) 精确常数 | 未完成 | 本轮仍用已证 C_P=2Lx，K、阈值与旧证书不变。没有给论文 π 常数或第10节原数值证书增加完成标记 |

## (6.6) 与字段的逐项对应

- `OriginalInterval.electric` 是 H₀¹ 路径 E，`continuous_electric` 给闭区间图连续；`historyU` 在 H₀¹ 中构造 u，故 u_t=E 有真实证据。
- `V7TimeRegularity.electric_deriv` 给 E 的 H₀¹ 导数 `electricDot`，`continuous_electricDot` 给闭区间连续；对应 u 的二阶 H₀¹ 时间数据。投影定理 `zeroCoordinate_hasDerivAt` 真实推出函数及弱梯度的 L² 导数。
- `electricDot_value` 在闭区间将图导数坐标与原电场 L² 导数数据识别；`electric_second` 给 E_tt 的 L² 导数，即 u 的三阶 L² 数据。本入口没有将整套 C^k 的类型与论文符号建立 iff；实际定理使用所列内部导数证据。
- 原八式给 P_t；`continuous_polarDot`、`polar_second`、`continuous_polarDDot` 给 P 的二阶 L² 数据。
- `OriginalInterval.continuous_flux`、`flux_deriv`、`continuous_fluxDot` 对应 λ 的 C¹(H(div)) 数据。
- λ=∇u+φ 来自已证历史与原场识别。在内部邻域求导，原辅助演化给 λ_t=∇E+M_r∂xu−M_pλx（y方向交换）。再用图投影和固定有界乘子求导，得 λ_tt。**不再输入 λ_tt。**
- φ 通过原八式演化先在普通 L² 中识别，再由既有加权历史构造给出加权路径；没有将普通光滑性当成无界权重可积性。既有 `firstState/secondState` 接入加权实际导数，不靠点态交换积分。
- q 是 P 的真实历史，q+τP=κu 是初始兼容保持的结论。
- `OriginalInterval` 的原场连续、图识别和初始五兼容覆盖 [0,T]；原八式及导数只在 (0,T)。T=0 仍要求 `DegenerateJetCompatibility` 的初始 polar/spatial 两层条件。没有端点 PDE 或端点能量导数输入。

## 定理输入审查

`V7TimeRegularity` 的 13 个字段都是路径、真实导数、闭区间连续或同一电场导数的识别；不含 Green、Poincaré、能量或全时段不变量。`toOriginalJet` 的两个二阶通量字段在证明中填入。

`PrimitiveIntervalData` 的图成员、时间导数、极化约束、primitive 主方程及辅助演化是反向方向的合理输入；不含重构后的 `OriginalAt`。其 H₀¹ 电场成员表达 PEC，H(div) 表达旋转磁通量的实际散度。兼容约束属于 primitive 解类；原解方向仍只输入初始五兼容。本轮输出八式及八个 HasDerivAt，不构造或声称一般低正则解的拓扑同构。

`OriginalAuxiliaryBounds` 和 `EnergyConclusions` 仅作输出。控制常数保持 V7 的 8、4、16、8 以及 S⁴；无新吸收正下界。输入的原 Z1/Z2/Qx/Qy 先由兼容保持识别再使用 PhysicalControl，不以名称替代识别。

## 指数核的范围与证明

对 Banach 空间中 W'=−BW+F，固定 t，微分 exp((s−t)B)W(s)。乘积法则给两项 BW 精确抵消；闭区间连续、内部真实导数与可积性经 FTC 得

$$W(t)=e^{-tB}W(0)+\int_0^t e^{(s-t)B}F(s)\,ds.$$

本项目 B 是有界吸收乘子，F 是已证普通 L² 到加权空间的差值提升。权重 w 没有成为有界算子。`auxiliary_operator_memory` 同时输出 IntervalIntegrable 与等式；`operator_memory_both` 从原解证明中取得所有演化/空间/连续性条件。x方向 B=M_p、强迫(r−p)∂xu；y方向交换。无除以 p/r，包含零吸收。已证 (5.8) 仍直接依赖阻尼估计，不需要新增指数核定理。

## 首个尚未闭合的数学步骤与尝试路线

1. **一般连续代表**：需先从区域分离弱测试等式取得一维 profile 的分布导数，再证明有界弱导数的一维函数 a.e. 等于某个 Lipschitz/绝对连续原函数，最后传递幅度界。检查固定 mathlib 的 `Convex.lipschitzOnWith_of_nnnorm_deriv_le`：它要求每点普通 `DifferentiableAt`，不能用于当前弱测试输入；`AbsolutelyContinuousOnInterval.exists_bound` 也以绝对连续为前提。已有弱零梯度/局部性及图逼近不能直接给未选代表的点值连续性。缺少的是该一维弱 FTC/代表构造，不是再包装一个 `ContinuousOn` 字段。
2. **精确常数**：对固定源码的检索未找到可直接调用的 Dirichlet–Wirtinger 不等式。可行路线是先对内部紧支测试函数证明一维 $\int|f'|^2\ge(\pi/L)^2\int|f|^2$，再 Fubini 两方向求和、用现有图闭包取极限。具体候选是积分展开 $|f'-(\pi/L)\cot(\pi(x-a)/L)f|^2$；需要证明支撑离端点时 cot 系数、积分分部及精确三角恒等式的合法性。本轮尚未形式化这条积分不等式，不能用数值近似或保守常数替代它。
3. **算子核→标量核**：需证明有界可测乘子的算子指数与乘 e^(tp) 的算子一致（可经幂级数、算子范数收敛和合法乘法表示）。当前证明停在真实算子指数商类公式，不声称共同零测集上的全时间逐点公式。

这些缺口不使当前已核验弱原系统定理失效，但阻止登记“V7 原文逐项对齐完成”。无解存在唯一性、严格/指数衰减等新增主张。
