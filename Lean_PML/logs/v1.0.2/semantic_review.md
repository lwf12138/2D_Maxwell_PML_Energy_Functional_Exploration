# 当前增量的语义审查

对照实际源码及 DeclarationTypes.lean 的运行输出，不只查看 #print axioms。

1. weak_green 只输入真实 zeroBoundaryGraph/weakHDivGraph。新文件没有修改图定义；弱散度仍只对 C_c∞ 测试定义，闭包推广由连续泛函闭核完成。
2. weakGreenDomain 的 trace=0/boundary=0 是**已限制 H₀¹ 定义域**上的零迹接口。不是把任意 H¹ 场边界值抹掉，也没有限制 H(div) 通量法向。没有 general trace theorem。
3. weakPoincareDomain 的 estimate 由 weak_poincare 填入，调用者不能传任意 estimate。常数仍 CP=2Lx，原参数证书未变。
4. weakH1Coordinate/weakHDivCoordinate 的连续性在图范数中证明。hasDerivAt_* 输入真正图空间导数，没有输入交换恒等式；不从普通 L² 路径可导推出 H¹ 可导。
5. auxiliary_memory_formula 的输入是连续实值函数和内部真实 ODE；FTC 及指数运算推出积分公式。g 是时间函数，当前没有弱空间梯度来源，因此不能登记完整弱场 (5.7)/(5.8)。
6. weak_zero_of_gradient_zero 输入两个梯度分量为零，仅完成规范唯一性链最后一步。原文四条规范约束到零梯度未证；没有定义名为 LiftUniqueness 的空包装。
7. 本轮未建立新的弱原解结构或主定理；旧 SmoothCompatibleSolution 保持全部强正则性。没有把接口未完成目标改写成普通字段。
8. 新非零例是原物理 bump 的弱分析调用和非恒定图路径、指数 ODE。旧静态/增长场随全工程构建保留，但没有冒称调用新弱主定理。

本轮缺口见 reports/weak_theorem.md；不把没有 sorryAx 等同于数学范围已经闭合。
