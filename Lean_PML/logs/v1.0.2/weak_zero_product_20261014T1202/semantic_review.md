# 区域 W¹,∞ × H₀¹ → H₀¹：证明与语义核查

本记录对应新 `Rectangle/WeakCompactApprox.lean`、`PML/WeakZeroProduct.lean`。最终结论已实际编译并审计，不再保留“输出只有 H¹”的旧缺口。旧阶段记录不改写。

## 实际交付

`LeanPML.PML.weakCoefficientMul_mem_zeroBoundaryGraph (D) (m : RegionalWeakCoefficient D) (u : zeroBoundaryGraph D)` 证明既有 `weakCoefficientMul D m u` 属于**原来同一个** `zeroBoundaryGraph D`。没有修改该空间定义，也没有输入闭包成员、逼近序列、Green、能量律或额外系数光滑性。

`LeanPML.PML.weakZeroCoefficientMulCLM` 调用该定理，构造真实有界线性算子 H₀¹ → H₀¹。`weakZeroCoefficientMul_nonzero` 使用矩形多项式泡函数及旧一般零迹桥接，再实际调用新算子，证明其函数坐标非零。实例的系数取 1 只为简洁验证调用；一般声明接收任意已有 RegionalWeakCoefficient。

## 关键数学链

1. 对粗糙系数 m 与内部测试函数 f，选择 `compactWeakProduct = m.extended·f`，弱偏导代表为 `(∂ᵢm).extended·f + m.extended·∂ᵢf`。区域零延拓仅用于积分/卷积，未声称它跨矩形边界保持原弱导数。紧支 f 保证实际粗糙乘积支撑严格内部。
2. 值与两个弱偏导代表的全空间可积性、统一幅度界以及矩形 L² a.e. 识别均真实证明。系数界只在 Ω 要求，域外延拓的界由定义推出。
3. `mollifiedField` 是实际 normalized ContDiffBump 卷积，实际 C∞ 性来自 mathlib 卷积微分。`mollifiedField_support_inside` 从紧支与 Ω 开性证明一个正边界余量 δ；核半径 ≤ δ 时卷积拓扑支撑仍在 Ω。
4. `compactWeakProduct_integral_partial` 以合法测试函数 `f·q` 调用 m 的真实弱导数定义，证明针对任意光滑全空间探针 q 的分部积分。q 不必紧支于 Ω；f 负责提供合法支撑。
5. `compactWeakProduct_mollified_partial` 取 q 为平移反射卷积核。先用真实 Fréchet 链式法则处理反射负号，再调用上条弱测试关系，证明**同一个光滑卷积的实际 x/y 偏导**分别等于两个弱偏导代表的同核卷积。
6. `mollifiedField_toL2_tendsto` 调用 mathlib 的 Lebesgue 微分定理取得 a.e. 收敛，继以统一界对平方差做支配收敛，得到实际 L² 范数收敛。`shrinkingMollifier` 明确定义 rOut=δ/(n+1)、rIn=rOut/2，并证明半径收敛及支撑条件。
7. `weakCoefficientMul_test_mem_zeroBoundaryGraph` 同时组合值、x 导数、y 导数三份 L² 收敛，用有限乘积/子类型拓扑得到**既有最大值 H¹ 图范数**收敛，然后用闭包闭性获得测试图乘积的 H₀¹ 成员。
8. 最终 `weakCoefficientMul_mem_zeroBoundaryGraph` 利用既有连续线性乘积图映射、H¹ 图闭性和 H₀¹ 闭包，对线性张成及其图闭包推广。没有用普通 L² 密度代替梯度逼近。

## 准确适用范围

- 系数对象有真实测试函数弱偏导，函数及两个偏导具有区域有界可测代表；不要求全轴 C∞，不增加吸收正下界。
- 输入 u 是既有真实 H₀¹ 图闭包元素；系数乘子保持其零边界类现为结论。
- 内部粗糙函数的光滑图逼近在本证明中针对 `m·f` 及其 Leibniz 弱导数实现。这足以证明任意 W¹,∞ 乘任意 H₀¹ 的目标；没有额外宣称已经建立所有不受有界限制的 H¹ 函数的全套通用卷积密度理论。
- 不改变 v0.5 光滑主定理，不自动推出弱八变量总装、规范唯一性或最终弱能量定理。其他代理对这些任务的证明应另行登记。

## 固定 mathlib 实际调用

- `ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`：`Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean:107`，提供 a.e. 收敛，**不是直接提供 H¹ 收敛**。
- `HasCompactSupport.contDiff_convolution_left`：`Mathlib/Analysis/Calculus/ContDiff/Convolution.lean:430`，提供实际 C∞。
- `HasCompactSupport.hasFDerivAt_convolution_right`：同文件 `:63`；`MeasureTheory.convolution_precompR_apply`：`Mathlib/Analysis/Convolution.lean:928`，用于实际导数与积分的连接。
- `IsCompact.exists_cthickening_subset_open`：`Mathlib/Topology/MetricSpace/Thickening.lean:443`，给出严格内部支撑余量。
- `tendsto_integral_of_dominated_convergence` 与已有项目 `norm_sq_eq_integral`：共同把平方差积分收敛变成实际 L² 范数收敛。

## 验证

- 成功模块构建：`logs/v1.0.2/20261014T120240_563227_weak_zero_product_final.log`，`lake build LeanPML.PML.WeakZeroProduct`，3001 jobs，退出码 0。此前失败日志均保留，包括缺少首次引用 mathlib olean、局部 Haar 实例、反射复合化简、核半径及 L² 图类型适配错误；均已修复，没有把待证目标改为假设。
- 成功专属类型/公理审计：`logs/v1.0.2/20261014T120321_788407_weak_zero_product_axioms.log`，退出码 0。八条核心声明只依赖 `propext`、`Classical.choice`、`Quot.sound`，没有 sorryAx。
- 审计脚本：`logs/v1.0.2/weak_zero_product_20261014T1202/Audit.lean`；包含最终完整类型与证明打印，确认最终输入只有 D、m、u。
- 正式总入口及全工程 Audit 由主代理接入、另行运行；上述模块构建不冒充最终全工程验收。

## 当前 SHA-256

- `LeanPML/Rectangle/WeakCompactApprox.lean`：`e829066db51d5aa63ab60040f37a7a443ec582af0a3dfca0e60489c35d838f6b`
- `LeanPML/PML/WeakZeroProduct.lean`：`21d7a37cb440be7e69449deee535d4e566441c643ee8e5216fa779f114876a16`
- `LeanPML/PML/WeakCoefficients.lean`：`9b12ab46128b9e8f0929e128621782f940fd50a1524f330dbb43e110942ac8f7`
- `LeanPML/Rectangle/WeakSpaces.lean`：`bcb9d6a3c79678fab18b65e9df6e8e1e45a64aec973bcda6492b900555bb8bc5`
- `lean-toolchain`：`efac0b94923b2d8b6840cd35be9177ad0fc5ab2332f4f4311c98712cee92fdee`
- `lakefile.toml`：`3a3ab926f99cfeb3ae9fa6309696858b0aabb7ce62469de72405a74dd64fab9e`
- `lake-manifest.json`：`6bd522ed18f94813b2e6fb5e7b9ea39d95a5098df2465acc0d815a09bb5dbf33`
