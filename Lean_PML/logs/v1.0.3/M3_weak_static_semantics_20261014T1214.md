# 非零弱原系统静态解调用审查

本记录只审查 `LeanPML/Examples/WeakStaticMode.lean`；不是整体 v1.0 验收。

实际采用矩形 `ParameterCertificate.unitSquare`、ε=κ=τ=μ=1、c=smallC、S=amplitudeS、p=S、r=0。现有矩形参数证书给 C_P=4、K=384。场 E=P=Hy=Z₁=Z₂=Qy=0，Hx=−1，Qx=S，在真实 L² 中构造。φy 的非零加权成员资格由恒定权重 3 下的平方可积性证明。这里是 §11.3 同一静态机制的常系数变体，不冒充原文紧支 F 的原样实现。PEC 只作用于 E，不添加磁场边界条件。

`originalAt` 同时给八个真实 HasDerivAt 及八条弱方程。`solution` 输入的五个初始兼容关系已逐项计算；没有将全时段不变量、耗散非负或单调性填作字段。`jet` 的所有真实图空间/L² 导数由常值函数规则证明，包括 T=0 的显式初始导数层兼容。

`main_call` 实际调用 `OriginalInterval.main_energy_estimate_WeakOriginal`，不重新证明一套脱离工程定义的能量。`energy_pos` 用主定理对输入磁场的 L² 控制及 `oneField_ne_zero` 推出闭区间能量严格为正；`energy_constant` 证明自动历史构造所得两个实际状态不变；`dissipation_zero` 以主定理 HasDerivAt 能量律和常值导数唯一性推出内部耗散零。未将目标能量律或耗散作为例子输入。

当前 `dissipation_zero` 的结论只登记 t∈(0,T)。正能量覆盖 [0,T]；能量恒定的直接计算覆盖所有实时间，但一般主定理的 PDE 条件仍只在内部。非零静态解不能严格递减，与能量单调不增相容。

构建和公理审计分别见本记录同目录 acceptance JSON 的路径；均 exit 0。审计八条主要声明只出现 propext、Classical.choice、Quot.sound，无占位公理。其余系数分支回归和不兼容增长排除由主代理统一汇总，本文件未声称完成这些独立项目。
