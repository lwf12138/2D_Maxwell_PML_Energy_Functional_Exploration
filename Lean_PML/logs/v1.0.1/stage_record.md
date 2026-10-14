# v1.0.1：弱空间与退化权重构造记录

用途：记录本轮实际构造、固定 mathlib 的 API 核验和未完成连接。它是阶段证据，不是新的阅读指南。只处理 v1.0.1；v0.5 光滑先验定理和回归证明不改名、不削弱输入。

## 基线与来源

- Lean `v4.31.0`；mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`。锁定文件没有修改。
- 开始时全部 58 个正式 Lean 源文件与 `logs/v0.5.3/overall_acceptance.json` 的哈希相同。端点文档修订是已登记的历史文档变化，不是 Lean 源码变化。
- [基线](baseline_20261014T095152.json) 保存本轮修改前源码、文档、锁定文件、合同、路线图及 V7 原文件/PDF 副本哈希。
- [来源/API 清单](source_api_inventory.json) 再次核对 v0.5 保护文件：原 V7 md/tex/pdf、proof_audit、合同、scope、路线图和锁定配置均相同。没有新的来源差异。本轮不编辑 PDF。
- 数学依据：V7 (5.5)–(5.6) 的加权辅助空间、(6.6) 的 $H_0^1$ / $H(\mathrm{div})$ 路径范围；新空间构造和表示定理为这些要求的分析基础，原文未单列公式。

## 固定 mathlib 核验：哪些对象可以复用

下表路径相对 `.lake/packages/mathlib/`。完整声明文本、源码行号和文件哈希见 `source_api_inventory.json`；实际 `#check/#print` 输出见 API 日志。没有根据名称相似认定等价。

| 准确名称 | 源码位置 | 实际内容及本轮用法 |
|---|---|---|
| `TemperedDistribution.MemSobolev` | `Mathlib/Analysis/Distribution/Sobolev.lean:149` | 输入全空间上的复值或复 Banach 值缓增分布、阶数 $s$、指数 $p$；要求 Bessel 势由全空间 `Lp` 表示。不是矩形零边界 Sobolev 域，本轮没有拿它替代 $H_0^1$。 |
| `TemperedDistribution.MemSobolev.lineDerivOp` | 同文件 `:316` | `MemSobolev s 2 f → MemSobolev (s-1) 2 (∂ₘ f)`。是上述分布空间中的方向导数，未直接提供矩形弱迹或 $H(\mathrm{div})$ 接口。 |
| `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` | `Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean:219` | 开集上局部可积函数与全部内部紧支光滑测试函数配对为零，推出域内 a.e. 为零。**实际用于**新弱导数/散度唯一性。 |
| `MeasureTheory.MemLp.integrable` | `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:658` | 有限测度、$1\le p$ 下 `MemLp f p ν → Integrable f ν`。用于矩形 L² 场的局部可积性。实际类型由本轮 `ApiProbe.lean` 核验。 |
| `MeasureTheory.MemLp.exist_eLpNorm_sub_le` | `Mathlib/Analysis/Normed/Lp/SmoothApprox.lean:82` | 普通 Lp 的紧支光滑逼近；不同时控制弱导数，也不保证支撑严格留在指定开域。不能据此直接宣称 H₀¹ 图范数密度或无界加权逼近完成。 |
| `MeasureTheory.Lp.dense_hasCompactSupport_contDiff` | 同文件 `:97` | 上述普通 Lp 密度；本轮核验 API，未用于掩盖缺失的边界/加权逼近。 |
| `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one` | `Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean:442` | 对经典 `ContDiff ℝ 1`、紧支函数的 Sobolev 不等式；不是 H₀¹/H(div) 类型，也不是本矩形弱 Poincaré。这里只读取源码，未作新定理调用。 |
| `Submodule.isClosed_topologicalClosure`、`Submodule.topologicalClosure.completeSpace` | `Mathlib/Topology/Algebra/Module/Basic.lean:174,197` | 子空间闭包及完备性。用于 H₀¹ 的闭包表示。 |
| `Continuous.inner`、`isClosed_eq`、`isClosed_iInter` | `Mathlib/Analysis/InnerProductSpace/Continuous.lean:90`；`Mathlib/Topology/Separation/Hausdorff.lean:487`；`Mathlib/Topology/Basic.lean:147` | 固定测试函数的配对连续，所有配对约束构成闭图。 |

全树检索 Sobolev、弱导数、H(div) 和相关测试/分布 API 后，没有定位到可直接填入本工程矩形域的完整 H₀¹/H(div) 接口。这不是断言 mathlib 没有任何 Sobolev 理论。`Sobolev.lean` 及测试函数基本引理确实存在；本轮在固定源码上补编译了原先缺失的 olean，没有下载新版本或改 manifest。

## 新空间实际包含什么

`LeanPML/Rectangle/WeakSpaces.lean` 中命名空间为 `LeanPML.Rectangle`。

1. `TestFunction D`：真实全空间 C∞ 函数，拓扑支撑紧且包含在整个矩形 $\Omega$ 内。旧 `SmoothField` 提供真实 `fderiv`。四边为零由支撑推出，不是独立假设。
2. `HasWeakPartial D i f g`：$f,g\in L^2(\Omega)$，对每个测试函数 $\varphi$，
   $$\langle g,\varphi\rangle=-\langle f,\partial_i\varphi\rangle.$$
   这是内部弱导数的定义；所有乘积由现有 L²×L² 可积性保证。内积直接作用在等价类上。
3. `weakH1Graph D`：三个实际 L² 坐标 $(u,g_x,g_y)$，两个弱导数条件。`HasWeakPartial.unique` 和 `weakValue_injective` 证明导数不是独立自由坐标。
4. `weakHDivGraph D`：$(\Lambda_x,\Lambda_y,d)\in(L^2)^3$，
   $$\langle d,\varphi\rangle=-\langle\Lambda_x,\partial_x\varphi\rangle-\langle\Lambda_y,\partial_y\varphi\rangle.$$
   不要求每个通量分量都在 H¹，不附加法向为零或磁场约束。弱散度唯一性已证明。
5. 两个图是**闭且完备**的子空间。Lean 继承有限乘积的最大值范数。`graph_norm_sq_equivalence` 已证
   $$\|U\|_{\max}^2\le\sum_{i=0}^2\|U_i\|_2^2\le3\|U\|_{\max}^2.$$
   因此闭包使用与通常平方和图范数相同的拓扑；没有给最大值范数错误安装 Hilbert 实例。
6. `zeroBoundaryGraph D`：紧支光滑图的线性张成在上述 H¹ 图中的闭包，作为 H₀¹ 的具体闭包表示；完备性及测试函数成员已证明。**尚未证明它等于某个弱迹算子的核，也未完成所有旧光滑零边界场进入此闭包的逼近证明。**
7. `weakFieldDomain/weakFluxDomain` 是图投影在实际 L² 中的像；`weakSpatialDomain/weakZeroSpatialDomain` 填入旧受限梯度接口，`weakDivergence` 是受限域上的真实线性弱散度。唯一性保证选择无关。注意：这些像作为普通 L² 的子空间，不宣称其继承的 L² 范数完备；完备性属于前面的**图范数空间**。梯度/散度也未被声称在整个普通 L² 上有界。

定义中的测试配对只针对 $C_c^\infty(\Omega)$，是分布导数的标准定义；不是把后续针对任意 H₀¹/H(div) 元素的 Green 关系、边界配对、Poincaré 或能量律放进输入。弱 Green 尚未实施。

## 既有 WeightedL2 的真实范围及本轮补充

旧 `Analysis/WeightedL2.lean` **保持原文件不变**。它已经实现：

- 普通测度 $\nu$ 下的平方根坐标 $X=\sqrt w\,\psi$，并要求 $X=0$ a.e. on $\{w=0\}$；不是任意抽象类型，也不是忽略零区的加权商类。
- `weightedSubspace_isClosed`、`weighted_completeSpace`：闭子空间及完备内积空间。
- `physicalL2`：$\psi=(\sqrt w)^{-1}X$，在零区延拓为零；`physicalL2_injective`、`physicalL2_zero_on_zero` 保证恢复没有额外零区自由度。
- `physicalL2_norm_sq_le`：普通 L² 平方不超过加权平方。输入是可测性及点态 $w=0$ 或 $w\ge1$；实际吸收权重由 `SpatialAbsorption.wx_gap/wy_gap` 证明这些条件，并未增加吸收正下界。
- `weighted_norm_sq_eq_integral`、`weighted_inner_eq_integral` 和对应可积性、真实路径求导；`weightedOfFunction_congr` 保证 a.e. 相同函数构造相同元素。

新 `Analysis/WeightedL2Operators.lean` 补充：

- `physicalL2_range_iff`：普通 L² 类 $f$ 在恢复映射的像中，**当且仅当** $\sqrt w f\in L^2$ 且 $f=0$ a.e. on $\{w=0\}$。
- `weightedMul`、`weightedMul_norm_le`：可测有界系数 $m$ 在平方根坐标上乘法，$\|m\psi\|_w\le C\|\psi\|_w$。
- `physicalL2_weightedMul`：恢复与有界系数乘法交换；证明采用 a.e. 公式。
- `Examples.WeakSpaces.absorption_weighted_range/absorption_weighted_multiplication` 实际调用原吸收系数 `SpatialAbsorption` 的已证性质；不是重新把目标权重界作为物理结构字段。

$w$ 本身仍可无界；只对 $m$ 使用有界乘子。没有新增 $p,r,a$ 的正下界；全零吸收时辅助加权空间为零，但普通场与零区空间耗散仍保留。对物理函数，不能只输入加权平方可积而漏掉零区条件。

## 光滑连接、已完成子项与缺口

| 子项 | 本轮状态 | 证据/边界 |
|---|---|---|
| 固定 API、来源、版本核验 | 完成 | 实际类型输出、源码摘录及基线哈希 |
| 真实弱 H¹ / H(div) 图、唯一性、闭性、完备性 | 完成 | `weakH1Graph`、`weakHDivGraph` 及各自定理 |
| H₀¹ 闭包构造与非零紧支成员 | 完成 | `zeroBoundaryGraph`；复用旧非零物理区 bump，`physicalTest_nonzero_member` |
| 所有旧光滑场进入弱 H¹、光滑通量进入弱 H(div) | 完成 | `smoothFieldDomain_le_weak`、`weakSpatialDomain_smooth`、`smoothToWeakHDiv` |
| 零权重、a.e.、嵌入、完整物理像、有界系数作用 | 完成 | 旧 WeightedL2 结果及本轮算子模块 |
| 所有旧光滑零迹场进入新 H₀¹ 闭包 | **未完成** | 还需边界局部化及导数同时收敛的图范数逼近；普通 L² 光滑密度不足。不能据此声称整套光滑 PDE 状态已经切换到新 H₀¹。 |
| 弱法向迹、弱 Green、弱 Poincaré | 后续 v1.0.2 | 当前只给真实内部弱导数/散度和闭包；未构造弱 `ConditionalGreenDomain` |
| W¹∞ 系数的弱乘积法则、切片、零水平集、加权传播与提升唯一性 | 后续 v1.0.2 | 本轮有界乘法只证明 L²/加权 L² 作用，不声称保持 H¹ 或自动获得全时段加权正则性 |
| 完整 V7 弱主定理 | 后续 | v0.5 主定理仍用原联合 C∞、C(K)、加权路径技术输入；没有删掉端点延拓正则性 |

**阶段状态：本轮构造子项经验证后分别登记通过；因一般光滑零迹到闭包的连接尚缺，v1.0.1 保留“部分完成”，不标整个弱范围完成。**

空间对象现在允许只有 L² 弱导数的成员，不再把 C∞ 作为物理空间元素的条件；C∞ 仅用于测试函数和既有光滑桥接。这个放宽发生在新空间层。它没有放宽现有 v0.5 主定理中的任何输入，也没有证明低正则性路径满足新 PDE 能量结论。

## 验证与失败记录

所有实际命令均由 `scripts/run_logged.py --stage v1.0.1` 保存工作目录、退出码及完整输出；未覆盖旧阶段日志。首次依赖检查发现缺失 olean，随后只编译锁定的 mathlib。编译过程中发生过 API 名称、集合表达式转换、Lean 子类型化简和声明类型缺失错误，均在原日志保留；没有用占位证明绕过。

最终完整构建、独立 `Audit.lean`、实际类型检查的精确日志路径及源码哈希见本目录 `acceptance.json`。审计允许 `propext`、`Classical.choice`、`Quot.sound`；不能把“没有 sorryAx”误认为普通结构字段已自动受到语义审查。

语义复核：`TestFunction` 仅含真实光滑函数/紧支/域内支撑；两个弱图的约束只含测试函数定义；H₀¹ 为闭包；加权像定理有且仅有实际成员与零区条件。未输入一般 Green、Poincaré、时间兼容或目标能量结论。所有旧正式证明文件保持；导入/审计只追加本阶段内容。
