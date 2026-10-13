# v0.4 对齐修复：独立语义复核

本记录检查实际声明的类型与构造体，不能由 `#print axioms` 替代。代码仍在并行追加；每次复核记录读取范围与哈希，最终工程构建由主代理执行。

## 1. 精确数值证书

`ParameterCertificate.lean` 使用实际 `Rect(-1,1,-1,1)`，从 `poincareConstant=2Lx` 得到 C_P=4，而不是传入一个名为 CP 的任意实数。旧 `materialA`、`scaleK` 实际给出 A=3、K=384。新 c=1/16384、S=1/65536 满足 S=c/4，三条显式小量条件依次为 3/2097152≤1、9/16≤1、3/2048≤1。

`unitSquare_le_threshold` 实际调用 `le_threshold_iff_explicit.mpr`，因此与原 min/sqrt 阈值接通。旧 c=1/128 的第二条左端精确为72，`oldC_not_le_threshold` 再用等价的正向推出矛盾。没有数值浮点近似、没有把阈值条件作为结构字段。

本文件单独检查、导出、13条公理审计均退出0；审计只有 propext、Classical.choice、Quot.sound，无占位公理。记录：

- `20261013T235407_046203_parameter_certificate_check.log`
- `20261013T235445_903365_parameter_certificate_export.log`
- `20261013T235509_200980_parameter_certificate_audit.log`

这些不是整个工程构建记录；没有因此单独宣布本轮整体完成。

## 2. 区域系数（当前主体）

已读 `RegionalAbsorption` 至 `fieldEnergy_eq_regional_integral`。

- 原 p/r 的非负、上界只分别在 Icc xlo xhi、Icc ylo yhi。C∞ 延拓是正则性条件，不携带域外物理幅度界。
- `pExtend/rExtend` 使用 p∘clamp、r∘clamp 产生旧乘子需要的全空间有界可测代表。clamp 在闭区间恒等；证明只用连续性和可测性，未把端点不可微的截回函数当作 C∞ 系数。
- `coefficients_eq_closed`、`coefficients_ae`、`weights_ae` 实际证明原区域系数和实现代表一致，零区分支也在其中。`weighted_memLp_iff` 以 a.e. 改写连接实际成员条件。
- `energyDensity_integrable` 由旧密度可积性沿 a.e. 等式传递；`fieldEnergy_eq_regional_integral` 接回同一能量，未利用不可积时的总定义冒充合法性。
- 当前尚须核对 final regional bridge：旧全轴 hp/hr 等式入口不能直接以原 p/r 通过；应内部使用延拓代表，并由域内一致性转换原方程/初始兼容，不应增加新的全轴幅度输入。

## 3. 古典解包装（当前主体）

已读 `OriginalSpatialAt` 至 `primitive_to_original_classical_rectangle`。

- `OriginalClassicalOn` 在原八条真实时间方程之外，给出 E、Hx、Hy 的实际 `DifferentiableAt`；时间/空间要求均仅在 Ioo×Ω。其字段没有兼容保持、Green、能量或等价结论。
- `PrimitiveClassicalOn` 对实际使用的 u、E、Λx、Λy 给空间可导证据，未要求未被空间微分的 P/Z/Q 额外可导。
- `hasDerivAt_spaceDx/Dy_of_differentiable` 通过真实 Fréchet 导数与坐标切片复合取得 HasDerivAt。`OriginalClassicalOn.spatial_derivatives` 覆盖原式使用的 Ex、Ey、Hx_y、Hy_x，避免仅凭 fderiv 总函数命名认定偏导存在。
- `reconstruct_spatialOn` 从 primitive 的空间证据经常数乘法给原 E/H 的空间可导性；反向八方程复用既有真实时间证据，不从普通导数值槽推断。
- `originalSpatialOn_of_liftIdentified` 由实际光滑状态代表和 μ≠0 推出原 E/H 可导，因此旧光滑入口没有重新假设其本来应提供的证据。若只使用低层 OriginalOn，仍仅是方程谓词；文档不得继续把它本身称为已提供所有空间可导条件的古典解。
- 两个矩形方向均保留整个四边 PEC；没有追加磁场法向、散度或子区域边界条件。

## 当前读取版本

- `LeanPML/Rectangle/ParameterCertificate.lean`：`afbcb8afbe20c9042ca9726e7c7849d42e257c28eb60462a5646d24e225223d4`
- `LeanPML/Rectangle/RegionalCoefficients.lean`：`011f80c5ba2843fed2d5431c146ea29af56ce1d7b720199df7d19f51a65facf7`
- `LeanPML/PML/ClassicalSystem.lean`：`63ea7a2dae932b24c15bf71f10711bdcd8c0754177b43e917d503f8305125d8a`

## 追加：古典桥接最终三个声明

已核对 `originalClassicalFiniteIntervalProblem`、`originalClassicalFiniteIntervalProblem_of_liftIdentified` 与 `originalClassicalFiniteIntervalProblem_second_R_continuous`。第一条实际从古典原系统得到古典 primitive，再使用既有真实 L² 装配；第二条从原方程及 μ≠0、光滑磁场代表生成空间可导证据后调用第一条。输入没有全时段 primitive 兼容/零区目标、Green、Poincaré 或有限区间问题对象。T=0 仍只分列必要初始导数层兼容，演化仍在 Ioo 0 T。P_tt 连续性直接来自同源第二层的实际一致范数正则性。未发现新增语义问题。

- `LeanPML/PML/ClassicalSystem.lean` 当前 SHA256：`63ea7a2dae932b24c15bf71f10711bdcd8c0754177b43e917d503f8305125d8a`

## 追加：区域古典最高入口复核完成

已核对 `RegionalAbsorption.originalRegionalFiniteIntervalProblem` 及其 `second_R_continuous`。最高入口输入的是原 p/r 的 OriginalOn，而不是截回系数的原 PDE。内部依次：

1. 从 LiftIdentified 和 μ≠0 生成真实古典原场空间可导证据。
2. 用闭矩形内 pExtend=p、rExtend=r 的逐点事实逐条改写八条方程，保留所有 HasDerivAt 与空间证据；PDE 条件仍仅在 Ioo 0 T×Ω。
3. 仅将 t=0 的五兼容条件改写为内部代表；零区初始条件从原 p+r=0 改写，没有把全时段保持作为输入。
4. 调用真正的 originalClassicalFiniteIntervalProblem；Green/Poincaré、混合微分、全时段兼容与零区保持仍由已证构造产生。

旧高层 reg 与 hregular 的字段也重新展开检查：OriginalLiftRegular 只含原场时间连续性和实际历史联合 C∞；SmoothStateRegular 只含一致范数时间正则性、实际加权成员和连续/可微。它们均不含原 p/r 的全轴幅度要求。LiftIdentified 是实际历史/磁场/辅助场代表的全函数识别，不含 PDE 或系数幅度。因此新推荐入口没有经隐藏字段重新加上域外非负或上界条件。

本轮追加的耗散密度 a.e. 相等、可积性及积分表示与能量密度相同地传递；零区 c|∇v|² 分支沿旧定义保留，没有重新定义耗散或删去物理区。

**当前独立语义复核结论：未发现需修复的假设隐藏、域外物理幅度加强、仅凭 fderiv 命名认定可导、T=0 空条件推理或未证能量目标输入。** 仍采用明确更强的联合 C∞/全轴正则延拓和加权时间正则性；这不是弱 V7 范围，也不包含加权正则性自动传播、提升规范唯一性或 PDE 解存在唯一性。精确 π 常数仍未证明，数值证书使用 C_P=4。

本记录是对类型和证明结构的独立复核；最终全工程构建/公理审计状态以主代理随后保存的真实日志为准。

### 最后读取版本哈希

- `LeanPML/Rectangle/RegionalCoefficients.lean`: `f7a5bf667a9dc9d5914f63c9747b95372227922de41912fcf6a8a44ff0277623`
- `LeanPML/PML/ClassicalSystem.lean`: `63ea7a2dae932b24c15bf71f10711bdcd8c0754177b43e917d503f8305125d8a`
- `LeanPML/Rectangle/ParameterCertificate.lean`: `afbcb8afbe20c9042ca9726e7c7849d42e257c28eb60462a5646d24e225223d4`
- `LeanPML/PML/OriginalAssembly.lean`: `e4bb5214237490b05b608fc289f67aa84e550e8cb9ac2266a94ed4bce674572e`
- `LeanPML/PML/Equivalence.lean`: `7f2b492a0f843dce1eda7521d9ca06f4c5c12fa02371e27a81082f3146965010`
- `LeanPML/Rectangle/StatePaths.lean`: `915c8204230cbb954cfe4403be3b3ce7c7ac9cc24ba78ca824b9066f906c9850`
- `LeanPML/Rectangle/SmoothPaths.lean`: `aa905c50a6618435f1c021c3473ddc0777f9d140c6aabd07c0fb899b0e9a2288`
