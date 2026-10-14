# v0.5 实例的独立语义复核

复核者：geometry/profile 子代理。记录时间：2026-10-13T17:05:36.888592+00:00。此处记录实际逐段阅读的定义、定理类型与证明调用，不代替 root 的最终完整构建/公理审计。

## 完整吸收剖面与共享函数

`profile=S*smoothTransition(4x²−1)` 为实际 C∞ 函数；零集精确为闭物理坐标区间，外侧严格正。`regional` 使用 CP=4 的合法小量证书，四边和四角分别有具体域内点。采用 C∞ 替代而不是冒称原正部幂剖面逐字核验。physicalBump 的拓扑紧支撑、支撑上原 profile=0，以及内部点真正 dx>0 均单独证明。

## 非平凡兼容初值（CompatibleData）

- 实际时间延拓 E=P=f、H=(-t f_y,t f_x)、其余辅助原变量为零；只证明 t=0 的 OriginalAt，不声称延拓是完整时间 PDE 解。
- `lift_values` 由实际历史积分和真实空间求导得到 u=tf、q=(t−1)f、φ=0。`identified` 连接实际历史与时间 jet，未把两个能量层独立指定。
- 五个初始不变量由定义计算；Z₂ 初始条件依赖pf=0，不能对任意 f 省略。
- φ=0 使加权成员真实成立，普通与梯度均实际 L²。图平方公式为 2‖f‖²+K(‖f_x‖²+‖f_y‖²)，K从实际CP证书取得；物理 bump 在内部非零推出真实 L² 非零及正图平方。
- 全四边初始 PEC、物理区初始零辅助已验证，未由数据可容许性推出一般解存在性。

## 非零静态模态（StaticMode）

- 单向 r=0、u=E=P=q=0、λ=φ=(0,F)，Hx=−F、Qx=pF。dyF=0 由真实切片求导，全部8式有真实时间导数并核验空间导数。
- `sideField` 支撑在 p=S 正平台；加权成员由矩形测度下 a.e. 的 sqrt(wy)F=固定常数*F 得到。没有要求权重全域有界或吸收有正下界。
- `solution/concreteSolution` 逐项构造最终原模型输入并真正调用 energy_antitone、energy_integral_balance。正能量由实际 L² 非零及正式图下界推出，恒定由实际状态定义推出。
- D=0 由同一真实常值路径的导数唯一性与正式能量律推出；先在 [0,1] 的内点调用后识别常值状态，故 T=0 没有从空内部条件偷推。
- 此例反驳无条件严格递减，不反驳单调不增。

## 非兼容增长族（UnrestrictedData）

- H=t∇ψ、Q=μ∇ψ、E=P=Z=0 为实际函数。curlH=0 来自真 C² 混合导数对称性；八式及 PEC 按支撑内外分支核验，未将整个矩形吸收替换为零。
- 原 H 空间平方与真实 toL2 范数和实际积分通过独立定理识别；各密度可积由光滑场 MemLp 取得。
- 内部点(-1/8,0)的真实 dx>0，通过连续代表唯一性得到正梯度 L² 平方，而非一般 f≠0 冒充 a.e.非零。
- 对任意 u0/q0，在该物理点 p=0 而 Qx≠0，因此初始磁不变量不可能为零；不能换一个提升规避不兼容。
- 不可能性只排除：同一全未来族上以固定m>0控制磁L²、有限初能量且全未来单调不增的实值能量。没有宣称所有形式能量均不存在，也没有否定兼容类主定理。
- 独立单层候选回归只证明原候选失败；最新版本已采用 smallC，未用与当前阈值脱节的c=1数值。

## 四分支入口回归（DegenerateBranches）

全零、仅x、仅y、完整profile四个RegionalAbsorption共享合法阈值。泛型zeroSolution从实际零场构造全部原条件和历史，四种都调用最终main。它仅验证分支入口、不冒充非零静态证书。新增整个零历史函数相等，确保在fderiv内部改写合法，未对单点值直接求导。

## 复核结论

以上当前版本未发现将待证能量目标藏入输入、忽略零区、用数值变量替代真实导数/实际积分、将初始证书冒称一般存在性或混用兼容/非兼容范围的问题。后续源码若改变，应对比下列哈希并追加核对；最终能否登记整阶段完成仍以实际完整构建和审计为准。

## 当前被复核版本

- `LeanPML/Examples/FullDomainProfile.lean`: `d50463bd0cbcf67fabe5404be526b0876e6e98be0ced6ba9ebfd8eefc5168e53`
- `LeanPML/Examples/SmoothBump.lean`: `6688bd55f66b5e7daca2bd78886d8ad72874fb7d131ce658a4b0ffa3ac395e73`
- `LeanPML/Examples/CompatibleData.lean`: `7fd53d09e712043b4d6958ad9d6a778bd767dc99a926bf39e069d619092a1287`
- `LeanPML/Examples/StaticMode.lean`: `354acc85785bd701f29fc6bb09ecc894e05a8695873f4fa215a0db57186a34cf`
- `LeanPML/PML/Obstructions/UnrestrictedData.lean`: `99df8bbe693c4f4aee92e333491bf67aafe4c8d2f575eb5f0571cd1921d152d4`
- `LeanPML/Examples/DegenerateBranches.lean`: `fb5f65160d05a1bd276196c05730538245b358145794c6a35415eab52b3bf50e`
- `LeanPML/Examples/PathHelpers.lean`: `226901138399542777cbcd74d15f28922b46411d1bcfc941065faa89b39d44b0`


## 冻结版本追加复核（2026-10-13T17:14:16.986483+00:00）

保留上方历史哈希；本段对最终冻结文件重新逐段检查。

- `initial_values` 只计算初始八槽的值，`spatial_regular` 证明实际延拓的空间 C∞；它们没有增加全时间 PDE 结论。
- `initial_derivative_compatible` 从真实 jet 的 q_t=f、P_t=0、u_t=f、φ_t=0 得到初始导数层极化及零区兼容，对 T=0 也可直接调用，没有使用空内部方程。
- `physical_initial_traces` 明确给 u0、E0、Et0 的四边零迹。E0 来自真实物理紧支；Et0 使用已由常函数求导核验的0值，不把“边界值0”直接当作任意端点导数0。
- `physical_data_certificate` 的方程字段仍是 `∀ X, OriginalAt ... 0 X`，没有 `OriginalOn`、存在量词解或兼容类最终结论。真实三层普通/加权正则性由 `regular` 给出，但只是方便延拓的正则性。原函数初始数据可容许、图平方有限正，不意味着该延拓满足 t>0 原 PDE。
- 注意汇总证书直接包含 f 的四边迹；u0/Et0 的明确两条零迹在相邻 `physical_initial_traces` 中单独交付。两处共同覆盖初始两层迹，不能把该汇总类型文字扩大成全时间边界结论。
- `PathHelpers` 新增函数零元/光滑零代表的 `[simp]` 规则都转用原来的 `weightedOfFunction_zero`，其证明仍通过实际 L² a.e. 代表识别零；没有新增可积性或求导假设，也没有构造新占位公理。
- `StaticMode` 最终版本删去了冗余机械步骤；逐段重新核查了 `solution`、平台 a.e. 权重识别、实际 MemLp、`concreteSolution`、`concrete_integral_balance`、`concrete_energy_pos` 与 `concrete_dissipation_zero`。它确实调用正式图界、能量律和积分平衡，其正的恒定能量与零耗散不是输入字段。
- `UnrestrictedData` 最终单层回归使用 smallC；增长族完整八式、全域 PEC、正实际积分、不兼容及全未来限定不可能性与前次一致。

结论：新补项未改变前次语义边界，未发现把初始数据或三层技术延拓误升级为一般解存在性。最终整工程成功证据仍由根任务保存，本复核不替代构建或公理审计。

| 文件 | 相较前次 | 冻结版本 SHA-256 |
|---|---|---|
| `LeanPML/Examples/CompatibleData.lean` | 已变化，重新核对 | `333f581dd831cb6a6a71f3ea9f429db21d4d5e6eba736cfd44f528d636694740` |
| `LeanPML/Examples/PathHelpers.lean` | 与前次相同 | `226901138399542777cbcd74d15f28922b46411d1bcfc941065faa89b39d44b0` |
| `LeanPML/Examples/StaticMode.lean` | 已变化，重新核对 | `308e5fd57dda70b4546b57cd668e72992dc4b4f917bf9aa92b7cebe6d32ea9dc` |
| `LeanPML/PML/Obstructions/UnrestrictedData.lean` | 与前次相同 | `99df8bbe693c4f4aee92e333491bf67aafe4c8d2f575eb5f0571cd1921d152d4` |
| `LeanPML/Examples/DegenerateBranches.lean` | 与前次相同 | `fb5f65160d05a1bd276196c05730538245b358145794c6a35415eab52b3bf50e` |
| `LeanPML/Examples/FullDomainProfile.lean` | 与前次相同 | `d50463bd0cbcf67fabe5404be526b0876e6e98be0ced6ba9ebfd8eefc5168e53` |
| `LeanPML/Examples/SmoothBump.lean` | 与前次相同 | `6688bd55f66b5e7daca2bd78886d8ad72874fb7d131ce658a4b0ffa3ac395e73` |
