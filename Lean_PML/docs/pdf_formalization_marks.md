# PDF 形式化标注账本（截至 v0.2.3）

用途：把 PDF 旁的每个红勾连接到当前可编译的 Lean 定理、实际公理审计和明确的范围限制。定义与假设的录入不算证明；局部时间结论不算完整空间/PDE 结论。

## 来源与保护

- 目标仅为 `results/V7_Maxwell_Debye_PML/V7_global_energy_副本.pdf`；原 PDF、MD、TEX 及既有“标注前备份”保持原样。
- 副本为 18 页，实际页序号从 1 开始，逐页与印刷页码 1–18 相同。修改前已有 16 处红勾/说明批注以及 110 个链接；全部保留。
- 本轮修改前备份：[带阶段和时间的副本](../logs/v0.2.3/pdf/before_v0.2.3_20261010T232231.pdf)。
- 修改前 SHA-256：`066b6d82f7539c0270b343ab162f5553f8728f120ec03b34b8438dd467a31a1d`。
- 原正文 SHA-256 仍为 `0a7f73a25cb119eeb75b3e7b3c3f2fbb3b319250f3354ed4dcad0ecff8eff4fb`。现有副本的 18 页抽取文字都以原 PDF 全页文字为前缀；额外内容为此前标注。未将另一版本公式混入。
- [输入版本、页面与原批注快照](../logs/v0.2.3/pdf/before_inspection.json)；[坐标及机器可核对计划](../logs/v0.2.3/pdf/annotation_plan.json)。

## 当前源码、构建与审计证据

- **B**：[本轮默认构建](../logs/v0.2.3/20261010T232910_472603_lake_build_retry.log)／[命令、目录、退出码](../logs/v0.2.3/20261010T232910_472603_lake_build_retry.json)，退出 0。
- **A**：[本轮独立审计](../logs/v0.2.3/20261010T232931_121820_axioms_audit_retry.log)／[命令、目录、退出码](../logs/v0.2.3/20261010T232931_121820_axioms_audit_retry.json)，退出 0。
- [证据核对脚本](../logs/v0.2.3/pdf/build_mark_plan.py)重新读取当前声明、正式根入口和这次审计。134 条定理逐项审计，仅有标准 `propext`、`Classical.choice`、`Quot.sound`；没有 `sorryAx`。
- 下列每项都使用 **B + A**，不单凭旧 PROGRESS 打勾。定义另列，不伪装成已证明定理。具体源码 SHA-256 已写入机器计划，PDF 编辑前再次检查未变。

## 逐项登记

### old-01：(2.4) 的 CD

- 页码：实际第 **4** 页；印刷页码 **4**。
- 类型：**局部时间**。
- 文件：[LeanPML/PML/TimeInvariants.lean](../LeanPML/PML/TimeInvariants.lean)。
- 完整定理名：`LeanPML.PML.hasDerivAt_CD_zero`、`LeanPML.PML.CD_eq_initial`、`LeanPML.PML.CD_compatibility`。
- 已核验的准确范围：(2.4) 仅 CD：固定空间点的真实导数为零和区间常值；初始零兼容推出全时段兼容。u,q的积分构造、函数空间尚未形式化。
- 未完成接口：时间积分提升、实际场正则性及另外两个磁不变量。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“CD；局部时间”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### old-02：(2.4) 的 CZ1、CZ2

- 页码：实际第 **4** 页；印刷页码 **4**。
- 类型：**局部时间**。
- 文件：[LeanPML/PML/TimeInvariants.lean](../LeanPML/PML/TimeInvariants.lean)。
- 完整定理名：`LeanPML.PML.hasDerivAt_CZ1_zero`、`LeanPML.PML.hasDerivAt_CZ2_zero`、`LeanPML.PML.CZ1_eq_initial`、`LeanPML.PML.CZ2_eq_initial`。
- 已核验的准确范围：(2.4) 仅 CZ1、CZ2 的真实求导及常值保持，允许 b=0。磁辅助不变量 Cx、Cy 尚未形式化。
- 未完成接口：磁辅助 Cx、Cy；不是五个不变量全部完成。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“CZ1/CZ2；局部时间”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### old-03：(2.5) 中 Z1、Z2 两项

- 页码：实际第 **4** 页；印刷页码 **4**。
- 类型：**局部时间**。
- 文件：[LeanPML/PML/TimeInvariants.lean](../LeanPML/PML/TimeInvariants.lean)。
- 完整定理名：`LeanPML.PML.CZ1_compatibility`、`LeanPML.PML.CZ2_compatibility`、`LeanPML.PML.Z1_zero_of_zero_absorption`、`LeanPML.PML.Z2_zero_of_zero_absorption`。
- 已核验的准确范围：(2.5) 仅 Z1=-εbu、Z2=-bq 的固定空间点版本，从初始兼容和原时间方程推出全时段兼容。Qx,Qy重构与完整时域等价未完成。
- 未完成接口：Qx、Qy 重构及完整双向 PDE 等价。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“Z1/Z2；初值保持”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### old-04：(5.2) 定义后的 A、K、c* 正性

- 页码：实际第 **7** 页；印刷页码 **7**。
- 类型：**代数；定义不计证明**。
- 文件：[LeanPML/PML/Coefficients.lean](../LeanPML/PML/Coefficients.lean)。
- 完整定理名：`LeanPML.PML.materialA_pos`、`LeanPML.PML.scaleK_pos`、`LeanPML.PML.threshold_pos`。
- 已核验的准确范围：(5.2) A、K、c* 的定义及正性已验证；CP只是给定正参数。(5.1)的矩形Poincaré不等式尚未证明。
- 未完成接口：CP 仅为给定正参数；矩形 Poincaré (5.1)。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“参数代数；正性已证”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### old-05：(5.3) 邻旁的阈值等价子结论

- 页码：实际第 **7** 页；印刷页码 **7**。
- 类型：**假设；派生代数**。
- 文件：[LeanPML/PML/Coefficients.lean](../LeanPML/PML/Coefficients.lean)。
- 完整定理名：`LeanPML.PML.le_threshold_iff_explicit`。
- 已核验的准确范围：(5.3) 仅 c≤c* 与 c²K≤1、8cAK≤κτ、8cAτ≤κ 的双向等价；L∞吸收场及空间幅度条件未在本阶段构造。
- 未完成接口：(5.3) 本身是输入；尚无 L∞ 场和空间幅度模型。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“阈值等价；实数条件”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### old-06：(5.4) 全部系数界

- 页码：实际第 **7** 页；印刷页码 **7**。
- 类型：**代数**。
- 文件：[LeanPML/PML/Coefficients.lean](../LeanPML/PML/Coefficients.lean)。
- 完整定理名：`LeanPML.PML.absorptionSum_le_half`、`LeanPML.PML.absorptionProduct_le_c_sq_sixteenth`、`LeanPML.PML.absorptionSum_mul_sub_product_nonneg`、`LeanPML.PML.le_threshold_iff_explicit`、`LeanPML.PML.c_mul_tau_bounds`。
- 已核验的准确范围：(5.4) 从非负p,r、幅度限制和精确阈值推出所列 a,b,ac-b,c²K,cτ 的界。是固定空间点的实数代数，保留零吸收。
- 未完成接口：从点值界提升到实际空间场。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“全部系数界；固定点”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### old-07：(5.5) 分支定义与零区值

- 页码：实际第 **8** 页；印刷页码 **8**。
- 类型：**定义；派生代数**。
- 文件：[LeanPML/PML/Weights.lean](../LeanPML/PML/Weights.lean)。
- 完整定理名：`LeanPML.PML.weights_of_sum_zero`。
- 仅作定义登记：`LeanPML.PML.energyWeightX`、`LeanPML.PML.energyWeightY`；不因此添加完成红勾。
- 已核验的准确范围：(5.5) w的正吸收分支和零延拓定义及分支性质；零区取0。尚未构造(5.6)的加权函数空间。
- 未完成接口：定义本身不是待证结论；(5.6) 加权空间。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“权重分支；含零吸收”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### old-08：(5.5) 后 w≥3/2 和可能无界

- 页码：实际第 **8** 页；印刷页码 **8**。
- 类型：**代数**。
- 文件：[LeanPML/PML/Weights.lean](../LeanPML/PML/Weights.lean)。
- 完整定理名：`LeanPML.PML.energyWeights_lower_bound`、`LeanPML.PML.energyWeights_unbounded`。
- 已核验的准确范围：正吸收分支w≥3/2，及满足幅度限制的趋零吸收族无统一有限上界。下界不适用于零延拓；未证明加权空间嵌入。
- 未完成接口：下界限 a>0；加权空间构造及嵌入。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“下界/无界；系数性质”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### old-09：(7.2) 后耗散权重有界子结论

- 页码：实际第 **11** 页；印刷页码 **11**。
- 类型：**代数**。
- 文件：[LeanPML/PML/Weights.lean](../LeanPML/PML/Weights.lean)。
- 完整定理名：`LeanPML.PML.dissipationPlus_bounds`、`LeanPML.PML.dissipationPlus_le_five_quarters`、`LeanPML.PML.dissipationMinus_bounds`。
- 已核验的准确范围：(7.2) 仅分式耗散系数非负及有界性已证；未证明空间积分或全域恒等式。零区c|∇v|²仍按原文保留。
- 未完成接口：全积分 (7.2) 和空间时间链式法则。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“仅系数界；非空间积分”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### old-10：(7.3)

- 页码：实际第 **11** 页；印刷页码 **11**。
- 类型：**局部时间；代数**。
- 文件：[LeanPML/PML/LocalElectric.lean](../LeanPML/PML/LocalElectric.lean)。
- 完整定理名：`LeanPML.PML.electric_rate_identity`、`LeanPML.PML.hasDerivAt_electricEnergyAlong`、`LeanPML.PML.hasDerivAt_electricEnergyAlong_exampleU`。
- 已核验的准确范围：(7.3) 电块代数与实际时间函数HasDerivAt求导。二阶证据直接针对deriv v；Fe含ε/2，完整能量还需μ和空间积分。De未宣称非负。
- 未完成接口：实际场、μ 因子、空间积分；De 未证非负。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“局部时间；真实求导”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### old-11：(7.4) 前未编号移位约束

- 页码：实际第 **11** 页；印刷页码 **11**。
- 类型：**局部时间**。
- 文件：[LeanPML/PML/LocalDebye.lean](../LeanPML/PML/LocalDebye.lean)。
- 完整定理名：`LeanPML.PML.polar_constraint_derivative`、`LeanPML.PML.polar_shifted_constraint`。
- 已核验的准确范围：由真实导数与邻域内z+τR=κv，推出κv_t=R+τR_t，再推出移位约束。单点兼容不足以求导。
- 未完成接口：场层兼容、微分与积分的接口。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“兼容求导；邻域关系”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### old-12：(7.4)

- 页码：实际第 **11** 页；印刷页码 **11**。
- 类型：**局部时间；代数**。
- 文件：[LeanPML/PML/LocalDebye.lean](../LeanPML/PML/LocalDebye.lean)。
- 完整定理名：`LeanPML.PML.polar_rate_algebra`、`LeanPML.PML.hasDerivAt_polarQuadratic`、`LeanPML.PML.hasDerivAt_polarEnergy`、`LeanPML.PML.hasDerivAt_polarEnergy_on_Ioo`、`LeanPML.PML.hasDerivAt_example_polarEnergy`。
- 已核验的准确范围：(7.4) Q逐项真实求导，再由邻域兼容和κ≠0证明FD=Q/(2κ)的HasDerivAt恒等式；含开区间入口和非零路径实例。未乘μ、未空间积分；DD未宣称非负。
- 未完成接口：实际场、μ 因子、空间积分；DD 未证非负。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“局部时间；真实求导”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### old-13：(8.1)

- 页码：实际第 **12** 页；印刷页码 **12**。
- 类型：**代数**。
- 文件：[LeanPML/PML/LocalDebye.lean](../LeanPML/PML/LocalDebye.lean)。
- 完整定理名：`LeanPML.PML.polarQuadratic_eq_reduced`、`LeanPML.PML.polarEnergy_eq_reduced`。
- 已核验的准确范围：(8.1) 在单点z+τR=κv下精确重写Q，及由调用者得到FD表达式（仍除以2κ）。不是完整能量正定性。
- 未完成接口：Q 到 FD 仍除 2κ；完整能量正定性。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“约束消元；代数已证”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### old-14：(8.2)

- 页码：实际第 **12** 页；印刷页码 **12**。
- 类型：**代数**。
- 文件：[LeanPML/PML/LocalDebye.lean](../LeanPML/PML/LocalDebye.lean)。
- 完整定理名：`LeanPML.PML.polar_coefficients_bounds_of_local_conditions`、`LeanPML.PML.polar_coefficients_bounds_of_threshold`。
- 已核验的准确范围：(8.2) 全部四组界，保留3/4、5/4、37/64、9/16；最高入口从材料正性、c≤c*及吸收幅度推导中间界，没有预设目标界。
- 未完成接口：空间范数估计和后续正定性。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“四组系数界；全部已证”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### old-15：(9.2) 前 θ 分支及 0≤θ≤1、和为1

- 页码：实际第 **14** 页；印刷页码 **14**。
- 类型：**代数；定义不计证明**。
- 文件：[LeanPML/PML/Weights.lean](../LeanPML/PML/Weights.lean)。
- 完整定理名：`LeanPML.PML.theta_partition`。
- 仅作定义登记：`LeanPML.PML.thetaX`、`LeanPML.PML.thetaY`；不因此添加完成红勾。
- 已核验的准确范围：(9.2)前的θ分支定义、0≤θ≤1及θx+θy=1；零区各取1/2。J的空间积分、(9.3)、(9.5)未形式化。
- 未完成接口：J 空间积分与 (9.3)、(9.5)。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“分配权重；分支已证”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### old-16：(9.6) 后文字中的 KS²≤1/16

- 页码：实际第 **14** 页；印刷页码 **14**。
- 类型：**代数**。
- 文件：[LeanPML/PML/Coefficients.lean](../LeanPML/PML/Coefficients.lean)。
- 完整定理名：`LeanPML.PML.scale_mul_amplitude_sq_le_sixteenth`。
- 已核验的准确范围：本句中KS²≤1/16的系数代数已证；(9.6)完整空间估计及耗散分配未证明。
- 未完成接口：完整 (9.6) 空间估计与耗散分配。
- 本轮红勾：**不重复添加**，保留原勾及其批注。原旁注概括：“KS²≤1/16；代数已证”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### zero-preservation：§5.2：在 Z 上 φ_t=0，因此 φ₀=0 保持（未编号）

- 页码：实际第 **8** 页；印刷页码 **8**。
- 类型：**局部时间**。
- 文件：[LeanPML/PML/LocalSpatial.lean](../LeanPML/PML/LocalSpatial.lean)。
- 完整定理名：`LeanPML.PML.zeroSpatial_compatibility_preserved`。
- 已核验的准确范围：固定点两个时间函数闭区间连续，内部真实辅助演化；非负吸收且 a=0，从初始 l(0)=h(0) 推出整段 l=h，包括 T=0。
- 未完成接口：不是 (5.7) 一般积分解公式、五个不变量整体、加权正则性或 PDE 提升。。
- 本轮红勾：**新增**，旁注明确为“✓ 时间保持；须初值 f=0；空间接口待证”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### spatial-positive：(7.1) 的正吸收分支

- 页码：实际第 **10** 页；印刷页码 **10**。
- 类型：**局部时间**。
- 文件：[LeanPML/PML/LocalSpatial.lean](../LeanPML/PML/LocalSpatial.lean)。
- 完整定理名：`LeanPML.PML.spatial_weight_balance`、`LeanPML.PML.spatial_rate_identity`、`LeanPML.PML.hasDerivAt_spatialAuxiliary`、`LeanPML.PML.hasDerivAt_spatialEnergy_pos`、`LeanPML.PML.hasDerivAt_spatialEnergy2D`。
- 已核验的准确范围：a>0 下权重平衡、数值恒等式，以及真实时间 h'=V、l'=V+σⱼh−σᵢl 推出的 Fsp 求导；包含两个方向。
- 未完成接口：h 与真实空间梯度、混合导数交换、可测可积、空间积分、Green/PEC 未实现。。
- 本轮红勾：**新增**，旁注明确为“✓ 局部时间版；空间接口待证；积分待完成”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### spatial-zero：(7.1) 后零吸收区未编号二维公式

- 页码：实际第 **10** 页；印刷页码 **10**。
- 类型：**局部时间**。
- 文件：[LeanPML/PML/LocalSpatial.lean](../LeanPML/PML/LocalSpatial.lean)。
- 完整定理名：`LeanPML.PML.hasDerivAt_zeroSpatialComponent`、`LeanPML.PML.hasDerivAt_zeroSpatial2D`、`LeanPML.PML.hasDerivAt_spatialEnergy_zero`、`LeanPML.PML.zeroSpatial_compatibility_preserved`。
- 已核验的准确范围：h 的实际时间导数给出 h²/2 和双分量平方和的导数；接回分支能量时明确需要 l=h，保留 c(hx²+hy²)。
- 未完成接口：p=r=0 不自动给出兼容；完整 PDE 中零辅助量来源、实际梯度及空间积分仍待兑现。。
- 本轮红勾：**新增**，旁注明确为“✓ 局部时间版；零区须兼容；空间接口待证”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

### spatial-pointwise：(7.2) 被积式的点态非负与独立零区密度（不是整式）

- 页码：实际第 **11** 页；印刷页码 **11**。
- 类型：**代数；点态**。
- 文件：[LeanPML/PML/LocalSpatial.lean](../LeanPML/PML/LocalSpatial.lean)。
- 完整定理名：`LeanPML.PML.spatialDissipation_nonneg`、`LeanPML.PML.spatialDissipation2D_nonneg`、`LeanPML.PML.spatialDissipation2D_of_sum_zero`。
- 已核验的准确范围：0≤p,r≤S≤c/4、c>0 下，两个方向的分支密度非负；零区精确为 c(hx²+hy²)。
- 未完成接口：该勾只指被积子表达式；没有完成 (7.2) 积分算子、可积性、加权路径求导或全域能量恒等式。。
- 本轮红勾：**新增**，旁注明确为“✓ 点态非负；空间积分；待完成”。
- 证据：**B + A**；上列每个定理均在本次审计输出中。

## 对旧勾的限定与本轮图例

| 位置 | 本轮处理 | 原因 |
|---|---|---|
| 第 1 页上方空白 | 新增三行图例，无完成勾 | 区分代数、真实时间、空间/PDE；明确假设与定义不计证明 |
| 第 7 页 (5.3) 左侧 | 增加“(5.3) 为输入；旧勾仅指阈值等价” | 保留原勾，但排除把小量假设本身当结论的歧义 |
| 第 8 页 (5.5) 左侧 | 增加“(5.5) 为定义；旧勾仅指零分支计算” | 保留原勾，准确对应 `weights_of_sum_zero`；不能用定义录入代表证明完成 |
| 第 11 页 (7.3)、(7.4) 旧旁注下方 | 各补“积分待完成” | 旧局部时间勾不扩展为空间积分结果 |

以上不删除、不改写任何用户旧批注。第 8 页新“时间保持”只定位于未编号零区保持句，不覆盖邻近 (5.7) 或 (5.8)。第 11 页新点态勾位于被积子表达式左侧，未给 (7.2) 整个积分编号打全完成勾。

## 不打完成勾的内容

- (2.4) 的两个磁辅助不变量、(2.5) 的磁场重构、(2.6) 完整 primitive/PDE 对应。
- (5.1) 矩形 Poincaré，(5.6) 加权空间及嵌入，(5.7) 一般积分表示和 (5.8) 加权正则性估计。
- (6.1) 在局部极化路径中是明确的邻域兼容输入；(6.2) 只有局部块定义，完整积分能量不是本轮结论。
- (6.7)–(6.10) 的图范数等价、最终耗散、单调性及场控制；(7.5)–(7.8) 的 Green/边界和整体能量恒等式。
- (9.5)–(9.7) 的空间估计和耗散闭合。旧第 14 页勾仅覆盖 θ 的代数性质与 KS²≤1/16，不能覆盖这些整体结论。
- v0.0.3、v0.1.1、v0.1.2 的教学标量与无空间 Debye 能量，以及一般时间单调/常值接口，均已在当前正式导入和审计中复核；它们没有可直接等同的完整 V7 公式，因此不硬给论文 PDE 结论打勾。
- v0.1.3 的非零实例、v0.2.2 的局部路径、v0.2.3 的四区代数和非零路径均是上述定理的正式调用证据；不额外冒充完整二维解。

## 编辑、复核与可重复性

- [编辑脚本](../logs/v0.2.3/pdf/annotate_pdf.py)只叠加矢量线条和嵌入字体文字；保留原页面大小、页序、公式和可选中文本。
- 每个新增标记使用稳定 ID `LeanPML.v0.2.3.*`；PDF 元数据保存计划哈希。重复运行同一计划直接跳过，不重复画勾；若用户在此后改变副本，脚本拒绝从旧备份覆盖。
- 改前备份只新建，不覆盖旧“标注前备份”。实际操作记录、标记定位和渲染均保存在 [本阶段 PDF 日志目录](../logs/v0.2.3/pdf)。
- 当前状态：**编辑与最终视觉验收已通过；见下方证据。**

## 最终编辑与视觉验收结果

- [初次编辑日志](../logs/v0.2.3/20261010T233326_922813_pdf_annotate.log)保留真实失败：目标已写入后，统计旧批注数遇到间接对象取值错误；并非公式核对失败。修复统计后，[重试](../logs/v0.2.3/20261010T233406_456228_pdf_annotate_retry.log)识别同一计划已在 PDF 中，未重复画勾，退出 0。
- [独立重新打开、核对和渲染](../logs/v0.2.3/20261010T233406_716661_pdf_verify_render.log)，退出 0；[逐页视觉与像素核验](../logs/v0.2.3/20261010T233454_140775_pdf_visual_qa.log)，退出 0。
- [最终核验数据](../logs/v0.2.3/pdf/verification.json)：18 页不变；126 个旧批注/链接全部保留；新增 4 个红勾和 5 个图例/限定说明，当前共 135 个批注/链接。
- 修改页 1、7、8、10、11 均已查看最终渲染。红勾及中文可见，没有裁切、遮公式或遮旧批注；标记矩形之外的渲染像素与改前完全相同。其余 13 页内容流字节不变。原文可选文本逐页保留。
- 最终副本 SHA-256：`0735771fa5d38adc70a74f21be3c109b490d1c91587414f874ac0c2d049409be`。
- 使用已有 PDF 技能、pypdf/reportlab 叠加和 pdftoppm 渲染；未安装依赖，未修改原始 PDF/MD/TEX。

## 2026-10-11 注释变更说明

本次只为 LocalSpatial 的注释补充公式与页码，PDF 和红勾没有变动。历史标注计划中的源码 SHA-256 对应 [本次保留的修改前源码](../logs/v0.2.3/comments_20261011T211945/before_LocalSpatial.lean)，继续作为 2026-10-10 标注时的证据，不改写历史哈希。
[逐字比较](../logs/v0.2.3/comments_20261011T211945/comment_only_check.json)确认剔除注释后的 Lean 代码完全相同；[新构建](../logs/v0.2.3/20261011T212242_143462_comments_lake_build.log)和[新审计](../logs/v0.2.3/20261011T212322_994625_comments_axioms_audit.log)退出 0。定理范围、定义、假设、公理依赖和红勾范围均未变化。

同日进一步精简注释，PDF 与定理范围仍未变化；[当前源码核对](../logs/v0.2.3/comments_short_20261011T214308/check.json)和[构建及默认审计](../logs/v0.2.3/20261011T214335_015307_shortened_comments_build.log)保留，历史哈希不覆盖。

同日按阅读反馈补齐关键证明过渡，保持公式与简短实例；仅注释及一处换行改变。[最新源码核对](../logs/v0.2.3/comments_readable_20261011T214656/comment_only_check.json)和[实际构建及默认审计](../logs/v0.2.3/20261011T214957_195523_readable_comments_build.log)通过。PDF、定理和标注范围未变，以上记录作为历史保留。
