# v0.4 矩形与接口语义审阅（独立审阅记录）

用途：检查已读代码的命题含义，不能用公理审计替代对普通结构字段的检查。
本记录由几何子任务执行者在完成自己的模块后交叉审阅 Green、Poincaré、TimeSpace、WeightedCalculus、原系统映射。
它不是独立第三方证书，也不等于最终总装已验收；以下结论严格限于列出的源码版本。

## 当前结论

**已核对部分未发现必须修复的数学范围错误。v0.4.1–v0.4.2 可支撑其已登记验收；v0.4.3–v0.4.4 仍须以总装最终源码和整个工程验证另行验收。**

### 几何、代表和边界

- `Rect.measure` 直接复用旧 `rectangleMeasure`，域为整个非退化开矩形。`measure_eq_closed` 使用真实二维 Lebesgue 乘积测度和区间端点零测事实；`integral_fubini` 先要求实际可积性再调用 mathlib Fubini。
- 连续场的 Lp 成员由紧致闭矩形的一致有界性证明。没有把空间积分的总定义当成可积性。
- `smoothFields` 只包含 `ContDiff ℝ ∞`。`fieldDomain` 为光滑场 `toL2` 的像，梯度不是整个 L² 上有界算子。
- 同一 L² 类的两光滑代表先在开矩形相等（Lebesgue 开集正测度＋连续性），再在闭包相等。内部邻域相等保证实际 fderiv 相等，故梯度、四边迹均代表无关。
- `descend` 是一般商兼容工具，其独立性参数在每个实际梯度/迹构造处均由定理填入，不是未实现分析结论。
- 边界数据使用四个紧区间上的连续函数。顺序为右、左、上、下。`ZeroBoundary` 是整个外边界，仅 E 被指定该条件时称 PEC；代码没有磁场法向条件或内部子区边界条件。
- `rectangleBubble` 非零、四边零值，且其 L² 类非零；不是仅以单点非零推断任意 L² 类非零，而是调用光滑代表唯一性。该实例未被冒称 PML 解。

### Green 与保守 Poincaré

- `green_smooth_functions` 对乘积 `(fX,fY)` 调用固定 mathlib 的真实矩形散度定理。所有体积分密度先由连续性证明可积，乘积求导来自 fderiv 规则。
- `edgePair` 是独立定义的一维实际积分；任意边界输入属于 C(Icc)，使其乘积可积，因此双线性成立。`boundaryValue` 符号为右−左＋上−下，法向分量相应为 X、X、Y、Y。
- `green_L2` 先选光滑代表再由已经证明的原函数 Green 导出。`greenDomain` 没有 hGreen 输入；其 green 字段直接填 `green_L2`。
- `poincare_integral_right_zero` 用右边零值、乘子 x−xlo、真实 Green 和积分非负平方，推出保守平方常数 `4 Lx²`。随后加入非负 y 梯度项。
- `poincareConstant = 2 Lx > 0`。`poincareDomain` 用同一矩形 trace 的核，estimate 由 `poincare_estimate` 填入；不接受未经证明的 estimate。
- `scaleK_rectangle` 给出 `K = 32 μ (ε+2κ) Lx²`；阈值继续用这个 C_P。没有证明 V7 (5.1) 的 π 精确常数，不能给原式无限定完成勾，也不能沿用旧精确常数的数值证书。

### 时间、真实 L²、历史与加权

- `TimeSpace` 的四个声明从联合 C∞、真实链式法则及二阶 FDeriv 对称性证明时间—空间交换。邻域版仅需空间邻域中的真实时间导数，不要求域外 PDE。
- `L2Paths` 用矩形连续截断构造 C(K)→有界连续函数→原 L² 的 CLM；截断在域内恒等。`continuousToL2_restrict` 证明它与既有光滑 toL2 完全一致。
- `hasDerivAt_of_pointwise` 的 C(K) 可导性是额外统一正则性，而导数值经 evalCLM 和真实导数唯一性识别。随后 CLM 求导才产生 L² HasDerivAt；没有把逐点可导直接当 L² 可导。
- `HistoryL2` 在 C(K) 中作实际 Bochner 时间积分，再用 evalCLM 的积分交换接到 `OriginalSystem.integralLift`；同一历史再经 continuousToL2 接到实际 L² Bochner 积分。闭区间一致连续性提供可积性，T=0 不要求内部导数。
- `BoundaryTime` 由 u₀ 零迹＋真实 u_t=E＋PEC 推出 u 零迹；由内部 E≡0 推出真实 E_t 内部零迹。T>0 用 E_t 闭区间连续延到端点；T=0 单独输入初始 E_t 图迹兼容。这避免从空内部条件推出端点导数。
- `WeightedCalculus` 使用已有真实 WeightedL2 及恢复 CLM 的单射，不将无界 w 当普通 L² 乘子。加权 DifferentiableAt 只断言导数存在；其值经物理恢复、普通 L² 导数唯一性识别。
- 加权成员、加权可微/连续仍是本轮允许的明确正则性输入，不能声称 (5.7)/(5.8) 自动传播。低层 weighted_smooth 仍要求零区物理代表为零；最终原解总装必须由原场零区保持填入，不能把全时段 φ=0 写成正则性假设。

### 已浏览的原系统与等价初稿

- `OriginalAt` 包含原八方程和八个真实时间导数证据；未包含 primitive、全时段兼容、能量律。`OriginalOn` 明确只在 (0,T)×Ω 成立。
- `integralLift` 是任意 u₀/q₀ 加实际 0..t 时间积分。全实轴连续/联合光滑属于技术延拓正则性，未把 PDE 扩展到域外或全部时间。
- `five_invariants_on_Icc` 从真实原演化、历史 FTC 和已证混合导数取得五个场的时间保持；磁场方向与 λ=(μHy,−μHx)、φx,t=−(p−r)λx+Qy、φy,t=(p−r)λy−Qx 相符。
- `five_invariants_toLp_eq_initial` 先有全空间域函数等式，再转 a.e./Lp；不是单个预选数值点的代数结果。初始不变量可以是非零常数场；零兼容只在初始时刻加入。
- `original_to_primitive` 从初始保持取得兼容，然后推原→primitive；`primitive_to_original` 使用开放空间/时间邻域取得真实混合求导及约束求导，再调用逐条八方程恢复，包括四个辅助变量。
- `primitive_zero_absorption_preserved` 保留 φ₀=0、时间连续性及实际辅助演化，不从 p=r=0 单独推 φ=0。
- 本审阅没有声称完整总装已经调用这些结果。`FiniteIntervalProblemConditional` 总装、所有初始图状态/T=0 分支、加权零区导数保持和最终原场恢复仍需核对最终版本。

## 明确范围差异与不应宣称的结论

本轮采用全空间 C∞ 延拓、C(K) 一致范数时间正则性和明确的加权成员/路径正则性，比 V7 的 W¹,∞ 系数及 (6.6) 弱空间范围更强。保守 C_P 也使允许参数范围变化。

以上没有证明弱 H₀¹–H(div) Green、最优 Poincaré 常数、加权正则性自动传播、提升规范唯一性、解存在唯一性、严格衰减或完美匹配。

## 已检查的工程证据

- `logs/v0.4.1/20261013T224101_375806_lake_build.json`：退出码 `0`，状态 `finished`。
- `logs/v0.4.1/20261013T224142_908894_axioms_audit.json`：退出码 `0`，状态 `finished`。
- `logs/v0.4.2/20261013T224801_700595_lake_build.json`：退出码 `0`，状态 `finished`。
- `logs/v0.4.2/20261013T225034_426223_axioms_audit.json`：退出码 `0`，状态 `finished`。

本记录没有重新执行整体构建；上述命令输出由主任务实际运行，本审阅检查了其 JSON 元数据。新模块的各单文件失败/修复日志均保留在相应阶段目录。

## 此次阅读源码哈希

| 文件 | SHA256 |
|---|---|
| `LeanPML/Rectangle/Domain.lean` | `6961af4f6b9e5d47ff3d773557d59778f6ab630d70e096c023685e3a563bc9d0` |
| `LeanPML/Rectangle/Fields.lean` | `282409219402b5e0c415b4487bc76925389382cbf27b0e4cb6e50a7452947fd7` |
| `LeanPML/Rectangle/Boundary.lean` | `c2dc823a7d1a76a1f8be7d502a16e29f79e26a902d63aee4a2d807bd443268b0` |
| `LeanPML/Rectangle/Green.lean` | `2ad892998bbb1903480743fdc8bf6663b266c5bc723b92c33a514ea4d08c1289` |
| `LeanPML/Rectangle/Poincare.lean` | `d81389ea5445a9acd8b683b36119da56662dd9df8eb1df6e0787c02412bead9d` |
| `LeanPML/Rectangle/TimeSpace.lean` | `777c35c9e4d84874baa8d92b93048b81019799741bd4430c669b3cde5447d19f` |
| `LeanPML/Rectangle/L2Paths.lean` | `90e2417b51bc2d3d50d435b4c1e8f38d93b2b70eaf5b842b1263e65900e3a616` |
| `LeanPML/Rectangle/HistoryL2.lean` | `172431b85ca66fe6aa35782e828ad22f6506d7f35fb57d82ef3a77387183ebf3` |
| `LeanPML/Rectangle/BoundaryTime.lean` | `b7a45cd50d8a2c710619ef5db4dd9b8dff240e90d290c6c737bc695954bb7edb` |
| `LeanPML/PML/WeightedCalculus.lean` | `b092ab64fe52ea571decf3b2c5e9b7fe3d69ecffaf436e07f2ea2114df640d9f` |
| `LeanPML/PML/OriginalSystem.lean` | `5c2f29c3c59cc1bb6ca71d98c27d607d0dd4f773077219804b1a10a1701797e8` |
| `LeanPML/PML/PrimitiveSystem.lean` | `b4226fb9f2497bfe7badfed7622c69308f6a848251dbe2ec1b2b32fb5fa97d64` |
| `LeanPML/PML/Equivalence.lean` | `7f2b492a0f843dce1eda7521d9ca06f4c5c12fa02371e27a81082f3146965010` |

## 追加：状态/原场装配的形成中复核

读取 `Rectangle/StatePaths.lean`、`Rectangle/InterfaceAssembly.lean` 与 `PML/OriginalAssembly.lean` 当前版本（最高原系统入口尚在追加）。

- `SmoothStateRegular` / `WeightedJetRegular` 仅给成员资格、连续性、可微性。无 Green、Poincaré、全时段兼容或能量字段。`SmoothZeroOn` 与 `SmoothStaticAt` 是低层中间输出包，最高入口仍须从初值/方程证明填入。
- `LiftIdentified` 八个函数等式逐一将光滑时间槽识别为真实历史积分、缩放磁场以及该磁场减真实梯度。它没有把 primitive PDE 作为识别条件。全延拓等式比最小局部表示强，但未要求域外或整个实轴满足 PDE。
- `lift_velocity_coordinates` 用真实历史 FTC 及导数唯一性得到 `v.first=E`、`z.first=P`，因此 SameSourcePath 的坐标不是只凭名称认定。
- `original_smoothZeroOn` 先从原系统和初始兼容/零区 φ₀ 得到全闭区间零值，再在开时间邻域对零函数求导得到 first/second。没有将全时段零区保持作为“正则性”输入。
- `lift_first_polar_closed` 在 T>0 时对邻域兼容求真实导数，再用连续性延拓至端点；仅 T=0 需要首层初始极化兼容。不能把这项初始图约束解释为由空内部方程推出。
- `smoothSpatialPath` 的梯度与散度交换实际调用 `hasDerivAt_jet_gradientX/Y` 等已证混合求导，边界来自真实迹及对开时间 PEC 求导。`finiteIntervalProblem_of_smooth` 尚是中间装配器，其 hprim/hzero/hstatic 必须由最终 original 入口实际产生，不能把此中间构造单独宣称全部验收。

范围注意：底层 `OriginalAt` / `PrimitiveAt` 使用 mathlib 总定义 `fderiv` 表达空间导数；它们自身不携带所有场的空间 `DifferentiableAt` 证据。通用反向方程定理因此首先是关于这些实际 fderiv 表达式的正确恒等式。最终选定的 `SmoothStateData` / `LiftIdentified` 给 E、λ、φ 等场的真实 C∞ 表示，才支持光滑场类的 PDE 解释；不可把底层恒等式夸大为方程自动改善正则性。此点已告知主代理。

## 最终原系统入口复核

已继续核对 `originalFiniteIntervalProblem` 与 `originalFiniteIntervalProblem_separated` 的完整类型及构造体。最高入口没有要求调用者提供 primitive 演化、全时段零区/静态兼容、现成有限区间问题、Green、Poincaré 或微分交换。它实际调用 `original_to_primitive`、`original_smoothZeroOn`、`original_static_closed`，再进入 `finiteIntervalProblem_of_smooth`。

分离入口明确要求 C∞ 的 p(x)、r(y)，并从非负和幅度约束构造旧 `SpatialAbsorption`。保留 a=0，无正吸收下界。`InitialDerivativeCompatible` 仅在 T=0 要求初始导数层极化与零区兼容；T>0 的相应端点条件从内部求导和连续性推出。`originalFiniteIntervalProblem_second_R_continuous` 给出实际 P_tt 的闭区间 L² 连续性，不输入耗散可积或积分平衡。

`ConditionalSpatialPath` 的 E_t 零迹只在内部要求，空区间不据此推出端点导数；单独的 `BoundaryTime.velocity_PEC_on_Icc` 若要覆盖 T=0 的 E_t 边界，仍准确要求相应初始迹条件。最高构造无须该额外空区间时间求导结论，不能在说明中超额声称其自动成立。

此独立检查支持最终入口的数学假设边界；编译、公理审计及项目整体验收仍由主代理完成。本检查不替代实际构建，也不表示已发布 v0.5 能量主定理。

本次读取版本 SHA256：

- `LeanPML/Rectangle/SmoothPaths.lean`：`30098ea7a04a1148fd0191b8f6c9ea52b7c13541e5604f64150f19fedff2302d`
- `LeanPML/Rectangle/StatePaths.lean`：`457b9277a72e8078c747daec5dd0573c1668c37423509f2eb08d750a4f490f69`
- `LeanPML/Rectangle/InterfaceAssembly.lean`：`05bcf055d2c20172f718870455b740ebf07060ad5ed0c0fb300cfb75fc8940f8`
- `LeanPML/PML/OriginalAssembly.lean`：`e4bb5214237490b05b608fc289f67aa84e550e8cb9ac2266a94ed4bce674572e`
- `LeanPML/PML/Equivalence.lean`：`7f2b492a0f843dce1eda7521d9ca06f4c5c12fa02371e27a81082f3146965010`
