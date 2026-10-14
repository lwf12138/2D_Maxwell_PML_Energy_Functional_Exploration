# M2 最终只读语义核查

本记录核查当前新增的实际加权辅助演化及 V7 (5.8)，不改变源码，也不代替最终弱原系统总装。核查时间：2026-10-14T11:33:04.108729+08:00。

## 结论与输入审查

本轮已经证明：从初始加权成员、普通 L² 辅助路径的闭区间连续性及内部真实 ODE，构造加权 Bochner 历史，证明恢复后等于原普通 L² 路径，得到全时段加权成员与零区保持。加上通量 = 弱梯度 + 辅助场这一空间关系后，精确证明 V7 (5.8) 的 2 与 4cSt 常数；并有原辅助场的实际空间积分版本。没有发现把目标加权估计、全时段成员或范数非负放进结构输入的情形。

这仍是**真实辅助演化与空间关系下的场定理**。本模块没有从弱原八条方程构造这些路径及空间关系，不能登记为 M4 或弱原系统主定理已完成。

输入逐项核对：

- `SpatialAbsorption` 给出可测实际系数、非负、幅度上界及 `S ≤ c/4`。没有吸收正下界或能量权重本质有界条件。底层引理允许一般可测有界系数；这并不宣称已完成区域 W¹,∞ 原系统接口。
- `W₀ : WeightedL2` 与 `physicalL2 W₀ = φ 0` 是初始成员及初始零区兼容；没有预先输入 `φ t` 对所有时间的加权成员。
- `ContinuousOn φ/h/l (Icc 0 T)` 是普通 L² 连续性。二维调用使用 `u : ℝ → weakH1Graph D`、`L : ℝ → weakHDivGraph D` 的图空间连续性，坐标投影有界性推出相应普通 L² 连续性。
- `hODE` 是 `(0,T)` 内 `HasDerivAt φ (r h − p l)`。不是名为导数的自由代数槽。
- (5.8) 的 `hspace` 是内部时刻 `l = h + φ`，属于辅助系统结构条件，尚需未来弱原系统总装推出。它不是目标估计，也不能对外声称已经由原八式保持证明。
- 单向终点 `ht : t ∈ Icc 0 T` 保证 `0 ≤ t ≤ T`，进而 `T ≥ 0`。PDE/ODE 只在开区间输入；`T=0` 时历史积分为零、恢复值取初值，没有利用空的内部条件推导端点导数。

## 声明和数学对应

以下 `SpatialAbsorption` 声明的完整前缀均为 `LeanPML.PML.SpatialAbsorption`。

| 位置与声明 | 已核验内容 |
|---|---|
| `WeightedForcing.lean:105` `LeanPML.PML.weight_absorption_squares`，`:134` `weight_difference_square` | 从原非负幅度条件证明 `w p²,w r² ≤ cS` 和 `w(r-p)² ≤ 2cS`；正吸收分支合法消分母，零区独立处理。 |
| `WeightedForcing.lean:216` `differenceLift`，`:226` `differenceLift_norm_sq` | 实际普通 L² → 平方根坐标加权空间的有界线性算子；强迫界为 `2cS‖h‖²`，不把无界 w 当普通 L² 有界乘子。 |
| `WeightedForcing.lean:252` `physical_auxiliaryRateX`，`:261` `auxiliaryRateX_norm_sq` | 恢复值确为 `r h − p l`；加权平方范数至多 `2cS(‖h‖²+‖l‖²)`。 |
| `WeightedForcing.lean:280` `auxiliaryRate_weak_norm_sq` | 对真实弱梯度及 H(div) 通量求两个分量和，得到 (5.8) 后未编号的 φ_t 估计；不误用普通乘积类型的最大范数作欧氏和。 |
| `AuxiliaryWeightedEvolution.lean:33` `auxiliaryWeightedHistory` | 实际 WeightedL2 值 Bochner 积分，不是形式积分符号。 |
| 同文件 `:45` `continuousOn_auxiliaryWeightedHistory`，`:58` `hasDerivAt_auxiliaryWeightedHistory` | 连续右端的实际可积性、闭区间连续性及内部加权空间 HasDerivAt。 |
| 同文件 `:77` `physical_auxiliaryWeightedHistory` | 有界物理恢复映射与 Bochner 积分交换，加普通 L² FTC，证明恢复历史 = 输入原辅助路径。 |
| 同文件 `:111` `auxiliary_weighted_membership`，`:164` `auxiliary_weak_field_membership` | 推出 `sqrt(w) φ(t) ∈ L²` 及零区 a.e. 为零；后者明确接到真实 weakH1Graph 梯度。 |
| 同文件 `:128` `hasDerivAt_auxiliaryWeightedHistory_damped` | 由已识别历史及 `l=h+φ` 得到 `W'=-M_p W+differenceLift h` 的真实加权 HasDerivAt。 |
| `WeightedMemoryBound.lean:22` `auxiliary_weighted_memory_bound` | 单向加权历史范数的准确 (5.8) 常数。 |
| 同文件 `:68` `auxiliary_weighted_integral_bound` | 原普通 φ(t) 的 `w φ(t)²` **可积性及实际空间积分估计**；不借不可积积分总定义。 |
| 同文件 `:94` `auxiliary_weak_memory_bound` | 两个真实弱偏导方向相加的准确 (5.8)，y 方向显式交换 p、r，并有 `swap_wx_eq_wy`。 |

平方根坐标恢复、范数积分公式和 a.e. 等价类处理复用已证 `WeightedL2`/`WeightedL2Operators`。当前结论不读取商类在任意指定点的值。空间积分版本可写代表元函数，但通过商类等式、已证恢复及 a.e. 积分定理保证代表元无关。

## (5.8) 常数的逐步复核

`LeanPML.Analysis.dissipative_memory_square_bound` 从真实 Hilbert 路径 `W'=-BW+F`、`⟪X,BX⟫≥0` 推出

$$\|W(t)\|^2\le 2\|W(0)\|^2+2t\int_0^t\|F(s)\|^2\,ds.$$

其证明使用正则化 `sqrt(‖W‖²+δ)` 的真实导数、FTC、δ→0 的序估计及时间 Cauchy–Schwarz；不是把该界作为 ODE 假设。`weighted_absorption_inner_nonneg` 通过实际积分 `p·|W|²` 证明 B=M_p 的非负性。

`differenceLift_norm_sq` 给出 `‖F‖²≤2cS‖h‖²`。`WeightedMemoryBound` 明确证明两个实数时间密度可积并应用积分序关系，乘以非负 `2t`，得到

$$\|W(t)\|^2\le 2\|W_0\|^2+4cSt\int_0^t\|h(s)\|^2\,ds.$$

二维版本分别取 x、y，再用已证明可积性合法拆开时间积分；结果是 `4cSt` 乘两个弱梯度平方范数之和，没有重复乘 2。这里的初始加权空间范数经物理恢复与原 φ₀ 的加权积分一致。

## 零吸收与退化分支

`w=0` 时 p=r=0 来自非负吸收及已证权重分支关系。加权算子在此恢复为零，普通辅助 ODE 和初值识别使原 φ(t) 在此 a.e. 为零。因此是“初始零区兼容 + 真实演化 ⇒ 保持”，不是“p=r=0 ⇒ φ=0”。没有除以 p、r 或要求它们有正下界。

一般定理允许全零、x 单向、y 单向及双向吸收。y 方向使用 `C.swap`，方向次序可在二维声明直接检查。全零配置不会删除普通梯度/通量字段；本模块也不声称完整空间耗散为零。

## φ_t、导数层与正则性边界

- `auxiliary_derivative_weighted_representative` 将普通路径的真实 HasDerivAt 值识别为一个加权元素；`auxiliaryRate_weak_norm_sq` 给出原文随后 φ_t 的二维 `2cS` 界。
- `hasDerivAt_auxiliaryWeightedHistory` 给出构造后的加权路径在内部真实可导。右端连续性也已证明。
- `hasDerivAt_auxiliaryRateX` 接收 h、l 在一个时刻的真实 HasDerivAt，证明加权右端路径的真实导数及相同 `2cS` 界。这是可供时间微分层使用的算子结论。
- 没有从有限范数估计自动推导 C²；没有构造完整原解的二阶时间层，也没有证明原弱八式及其时间微分层提供所有需要的导数关系。将导数层再接到完整原系统仍属于 M4/相应正则性总装。
- 当前严格表示是实际加权 Bochner 历史、普通 L² ODE 的 FTC 识别及等价阻尼 ODE。**没有在场层原样交付 (5.7) 的指数核卷积公式**；旧点态公式不能单独代表该场公式。可为 (5.8) 与成员保持作完成登记；(5.7) 如标记须限定为已证等价历史/ODE 表示。

## 非零调用

`LeanPML.Examples.WeightedEvolution.nonzero_memory_bound` 实际调用本轮一般估计；同文件 `nonzero_weighted_propagation`、`nonzero_weighted_path_derivative`、`nonzero_rate_derivative` 调用成员、求导和导数层接口。

取 p=1、r=0、c=4、S=1，f 是已有非零内部光滑紧支函数的实际 L² 类，φ(t)=exp(-t)f，h=0、l=φ。真实指数导数、连续性和初始加权恢复均已证明，路径非零且非恒定。它检验不对称方向与非零加权调用；梯度强迫在该例为零，不能夸称非零强迫回归，也不是完整二维 PDE 解或全材料阈值证书。

## 验证证据及限制

本报告只读复核源码及已产生的当前验证输出，没有另行声称运行全工程命令：

- `logs/v1.0.2/20261014T112814_522179_continuation_lake_build.json`：当前正式 `lake build`，退出码 0。
- `logs/v1.0.2/20261014T112845_938004_continuation_axioms_audit.json`：当前正式 `lake env lean Audit.lean`，退出码 0。
- 同名 `.log` 保留完整输出；新 `auxiliary_weighted_integral_bound`、`auxiliary_weak_memory_bound`、`nonzero_memory_bound` 及通用真实时间估计的审计输出仅使用标准 `propext`、`Classical.choice`、`Quot.sound`。
- 对所审查五个新增 Lean 文件检索未发现 `sorry`、`admit`、自定义 axiom 或 `unsafe`。结构/定理输入同时人工核查，不能仅据 `#print axioms` 推断无隐藏目标。

本次 M2 成果补齐成员保持、实际空间积分 (5.8)、φ_t 范数界及实际时间导数接口。**不据此登记 W¹,∞ 全原模型总装、提升规范唯一性、C² 自动传播、完整弱 (6.7)–(6.10) 或解存在唯一性完成。**

## 当前文件 SHA-256

旧日志和验收快照不覆盖。下面仅记录本报告读取版本；以后源文件变化需要重新核查。

| 文件 | SHA-256 |
|---|---|
| `LeanPML/PML/WeightedForcing.lean` | `99b4c12bbf0c540507bcd7a2d6cd37ca0625adcd834f2c24bac8d628c0821f22` |
| `LeanPML/PML/AuxiliaryWeightedEvolution.lean` | `1b6fe9f25ce06ef88ac99aad161720c30c6257783bb47a4d5e754690c6e1509e` |
| `LeanPML/PML/WeightedMemoryBound.lean` | `98371900b9193c5568641aed08e57e376fa57c01dcaaf4c0670778bc88fdc63e` |
| `LeanPML/Examples/WeightedEvolution.lean` | `097bfd028353631cbb29ebbaec71e4e79f06542f3ddabb60b1bd8272ad8fb831` |
| `LeanPML/Analysis/DissipativeMemoryEstimate.lean` | `f2800b02e5d20c57c78bce79c7fed8fcd357d88868539bbc0d2dc86a04e0737b` |
| `LeanPML/Analysis/WeightedL2.lean` | `6be3ed7daca127d0a07aa79fe7dcc3ff0a65d43599f3229ee8a6549a280fab08` |
| `LeanPML/Analysis/WeightedL2Operators.lean` | `d036e8ab2f3fd4ac94dcf0f2bfbb58812484da7aec2315f7976d0db6788d81fe` |
| `LeanPML/Rectangle/WeakSpaces.lean` | `bcb9d6a3c79678fab18b65e9df6e8e1e45a64aec973bcda6492b900555bb8bc5` |
| `LeanPML/Rectangle/WeakPaths.lean` | `2c7e4c71adf0808160f151e1322eaddfa36c3e71ac787a9006d09b7c734e3c52` |
| `LeanPML/PML/SpatialCoefficients.lean` | `07223cf17bdbf48daff2078f543070d760d1dc5464f47a8c2b8d0d0438e84392` |
| `LeanPML.lean` | `0ca4649bbdb842446a16f5e4b8cf6ae2afa0292eefb294cdd07bca8d1e891492` |
| `Audit.lean` | `dc10162c7d182168c2bb3bc0e09f767af757f3821dbde90762eeb83c995624ae` |
| `lean-toolchain` | `efac0b94923b2d8b6840cd35be9177ad0fc5ab2332f4f4311c98712cee92fdee` |
| `lakefile.toml` | `3a3ab926f99cfeb3ae9fa6309696858b0aabb7ce62469de72405a74dd64fab9e` |
| `lake-manifest.json` | `6bd522ed18f94813b2e6fb5e7b9ea39d95a5098df2465acc0d815a09bb5dbf33` |
| `../results/V7_Maxwell_Debye_PML/V7_global_energy.md` | `0a7f73a25cb119eeb75b3e7b3c3f2fbb3b319250f3354ed4dcad0ecff8eff4fb` |
