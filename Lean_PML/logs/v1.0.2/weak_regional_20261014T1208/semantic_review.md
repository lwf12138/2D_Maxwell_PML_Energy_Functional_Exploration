# 弱区域吸收桥接核查

新增文件 `LeanPML/PML/WeakRegionalAbsorption.lean`。它不是弱主定理本身，而是把原区域分离弱系数连接到已有实际能量/乘子框架的推荐入口。

## 输入条件与区域范围

`WeakRegionalAbsorption D` 的 `coefficients : SeparatedRegionalWeakCoefficients D` 复用已有真实弱导数类型，保留区域 p(x)、r(y) 分离关系。物理幅度字段仅为：

- `∀ x ∈ Icc D.xlo D.xhi, 0 ≤ profileX x ∧ profileX x ≤ S`；
- `∀ y ∈ Icc D.ylo D.yhi, 0 ≤ profileY y ∧ profileY y ≤ S`。

此外输入 c>0、S≥0、S≤c/4，以及两个区域代表在 Ω 上的 `ContinuousOn`。连续代表目前供 §5.3 唯一性使用；本文件没有声称已经从所有 W¹,∞ 商类自动选择 Lipschitz/连续代表。没有全轴 C∞、全轴原 profile 幅度界、吸收正下界、Green、Poincaré、目标能量律或兼容保持字段。

已有 `RegionalWeakCoefficient` 中的函数、两个弱导数是可测区域有界代表；弱导数通过所有内部测试函数配对定义。这些条件保留，未以普通 L² 乘子冒充 H¹ 乘积法则。

## 内部延拓和实际一致性

`WeakRegionalAbsorption.spatial` 使用既有 `RegionalBounded.extended`，即 Ω 内保留原区域代表，Ω 外置零。由域内分离形式和上述坐标界推出非负/幅度，域外由零值与 S≥0 推出界，因此构造了已有 `SpatialAbsorption`。

该内部二维延拓可在矩形边界跳跃，域外不必维持 p=p(x)、r=r(y)。这只是整个矩形限制测度下使用的内部代表；不要求原系数在域外满足幅度，不声称零延拓在全空间仍有原来的弱导数，不将其用于域外 PDE 或空间求导。真正分离的原 profile 在 Ω 内由 `profile_match` 明确恢复。

已证声明（全名加前缀 `LeanPML.PML.WeakRegionalAbsorption`）：

- `regional_bounds`：从坐标区间的原假设推出 Ω 内幅度。
- `p_match`、`r_match`：区域弱系数与内部 C 在 Ω 内逐点一致；方向适合 `Weak.CompatibleLift.u_unique` 的 hp_match/hr_match。
- `profile_match`、`profiles_ae`：C 与原 p(x)、r(y) 在全矩形限制测度下 a.e. 一致。
- `operators_eq`：区域弱系数的有界 L² 乘子和 C.pCoeff/C.rCoeff 的乘子作为连续线性映射相等；不同界证据没有改变实际商类算子。
- `weights_ae`：C.wx/C.wy 与原 profile 构成的两分支权重 a.e. 一致；没有假设 w 有界。
- `integral_profiles`：任意系数密度换代表后实际空间积分相等；`integrable_profiles_iff` 另外证明可积性等价，因此不把积分总定义视为可积性。

与规范唯一性的连接无需改写其结构：传入 A.coefficients、A.p_match、A.r_match、A.p_continuous、A.r_continuous 即可。弱原模型方程/能量可用 A.spatial，而原域内系数通过上述乘子和积分一致性恢复。

## 参数和四分支调用

`certificateConfiguration xActive yActive` 采用实际 `ParameterCertificate.unitSquare`，c=1/16384、S=1/65536，材料阈值沿用 C_P=4 的已证证书。

`certificate_threshold` 调用 `unitSquare_le_threshold`；没有重复脱离实际矩形常数的数字验证。

`certificate_four_branches` 从实际区域入口的 `profile_match` 分别验证：p=r=0、p=S>0/r=0、p=0/r=S>0、p=r=S>0。两个不对称方向分别调用，均不把正吸收加为一般结构条件。这只是系数接口与参数证书调用，不声称构造四个非零 PDE 解。

## 验证与改动边界

- `logs/v1.0.2/20261014T120815_337606_weak_regional_final.log`：`lake build LeanPML.PML.WeakRegionalAbsorption`，2998 jobs，退出码 0。
- 公理/结构审计脚本：`logs/v1.0.2/weak_regional_20261014T1208/Audit.lean`。
- 公理审计日志：`logs/v1.0.2/20261014T120853_183268_weak_regional_axioms.log`（对应 JSON 记录最终退出码）。
- 本模块及本记录为新增文件；未改旧证明、模型合同、路线图、依赖锁、主入口或旧 Audit。正式总导入及总审计由主代理接入。

## 当前源码与配置哈希

- `LeanPML/PML/WeakRegionalAbsorption.lean`：`fd0bba38b74bcc9aefc5e5f22a287d305d331f71b75fb1d53acbafc50798da62`
- `LeanPML/PML/SeparatedWeakCoefficients.lean`：`ea94d8a606e8ba30c673482e5cf2d2def03dc64a7ac4a6258eb35e65a325b2b5`
- `LeanPML/PML/WeakCoefficients.lean`：`9b12ab46128b9e8f0929e128621782f940fd50a1524f330dbb43e110942ac8f7`
- `LeanPML/PML/SpatialCoefficients.lean`：`07223cf17bdbf48daff2078f543070d760d1dc5464f47a8c2b8d0d0438e84392`
- `LeanPML/Rectangle/ParameterCertificate.lean`：`afbcb8afbe20c9042ca9726e7c7849d42e257c28eb60462a5646d24e225223d4`
- `lean-toolchain`：`efac0b94923b2d8b6840cd35be9177ad0fc5ab2332f4f4311c98712cee92fdee`
- `lakefile.toml`：`3a3ab926f99cfeb3ae9fa6309696858b0aabb7ce62469de72405a74dd64fab9e`
- `lake-manifest.json`：`6bd522ed18f94813b2e6fb5e7b9ea39d95a5098df2465acc0d815a09bb5dbf33`
