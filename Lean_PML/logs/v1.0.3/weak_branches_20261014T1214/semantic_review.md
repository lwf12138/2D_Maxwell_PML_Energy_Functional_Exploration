# 四个吸收分支的真实弱原系统调用核对

本文件仅登记本轮独立回归结果；不替代整个 v1.0 的总验收。

- `zeroInterval` 的全部八坐标是整个 unitSquare 测度上的实际 L² 零元；electric、flux 是 H₀¹/H(div) 图空间零元。
- 八条原式逐条由零乘子及代数恒等式验证。八个 `HasDerivAt` 由常值函数真实求导得到；不存在能量公式、耗散符号或闭区间单调性输入。
- `zeroJet` 使用同一零原场的真实图空间及 L² 二阶导数。它不是把“导数层也满足 PDE”设为输入。
- `zero_degenerate` 直接核验 T=0 时的极化和两个空间初值兼容，不从空的内部方程推导。
- `zero_initial_weighted` 用加权空间真实零元及恢复映射，与原物理 φ 初值识别；无除以 p、r 或 a。
- `configuration_parameters` 调用实际矩形的原参数证书：C_P=4、K=384、c=1/16384、S=1/65536。
- `configuration_main` 真正调用 `OriginalInterval.main_energy_estimate_WeakOriginal`，输出其完整 `EnergyConclusions`，包括图范数双边界、内部真实求导、定量耗散、闭区间单调性与积分平衡、原 E/H/P 控制。
- `all_four_configurations` 分别调用 (p,r)=(0,0)、(S,0)、(0,S)、(S,S)。两个单向分支不对称；取值性质来自 `WeakRegionalAbsorption.certificate_four_branches`。
- 幅度条件来自区域坐标范围；内部 Ω 指示延拓只用于空间乘子，未要求原剖面在全实轴满足幅度条件。
- 四例均为零解，是退化接口回归；本文件不宣称给出非零 PDE 解。非零静态调用由独立 `WeakStaticMode` 交付。

## 实际验证

- `20261014T121313_257293_weak_branch_first`：真实失败，图空间常值导数的类型推断未确定；保留原输出。修复为显式 `zeroBoundaryGraph D` / `weakHDivGraph D` 类型。
- `20261014T121356_207825_weak_branch_fix1`：单文件检查 exit 0。
- `20261014T121427_111676_weak_branch_build`：3018 项依赖与目标模块构建 exit 0。
- `20261014T121447_617433_weak_branch_axioms`：独立审计 exit 0；五个定理仅依赖 propext、Classical.choice、Quot.sound，没有 sorryAx。审计对象包含全部主结论、结构定义及实际主定理调用。

源码与依赖锁哈希见相邻 `source_hashes.json`。正式全工程导入与 Audit 汇总由父任务处理。
