# V5–V6 核心定理与 Lean 验证范围对照

审阅日期：2026-09-24。

## 结论

目前 V5、V6 的 Lean 文件验证了部分代数恒等式、标量吸收不等式和二元二次型正定性引理，**没有形式化证明文档中的完整二维 PDE 能量恒等式、能量与状态范数等价性，或沿 PDE 解的条件单调性定理**。

因此，“核心能量定理已经通过 Lean 验证”不符合当前代码的实际覆盖范围。“部分辅助代数经过 Lean 验证；核心 PDE 结论仍由文档中的数学推导承担”是准确表述。本次核查的是形式化覆盖范围，不据此断定纸面定理错误，也不代替对纸面证明的完整独立审稿。

## 文档中的核心结果与代码对照

下列路径均相对于本项目根目录。

| 文档中的核心结果 | 文档位置 | Lean 实际覆盖 | 未形式化的关键内容 |
|---|---|---|---|
| 变系数完整能量恒等式 E_B' = -D_0 + R_sigma + B | `results/v5-tex/variable_coefficient_baffet_energy_analysis.tex:235`；`results/v6_tex/nonlocal_memory_strict_pml_analysis.tex:183` | Debye 多项式展开、若干代数整理 | 实际能量定义、沿 PDE 解求导、积分与求导交换、空间分部积分、边界通量 |
| E_B 正定，并在角域与扩展状态的 L2 范数平方等价 | V6 TeX 第 216–225 行 | 行列式展开；通用二元二次型的正定充分条件 | 对真实能量各块应用这些引理、统一上下界、完整积分能量的范数等价 |
| V5 小梯度单调定理；V6 Level-B 条件单调性 | V5 TeX 第 305–347、491–499 行；V6 TeX 第 234–254 行 | 假设 g²≤4m_u m_lambda 后，证明 -m_u u²-m_lambda l²+g u l≤0 | 从真实耗散和梯度余项得到积分估计、点态向量/矩阵 Schur 条件、统一耗散余量、能量导数非正及时间单调性 |
| 坐标拉伸模型与 primitive 系统严格等价、内界面完美匹配 | V6 TeX 第 115–164 行 | 假设 Yp=Y0 后，证明反射公式为零 | 变换与初始历史、导纳相等的推导、出射平方根分支、界面传输 |
| 椭圆非局部候选的完整导数与未消去余项 | V6 TeX 第 262–304 行 | 标量代理 z=-g*u/ell 的代入展开 | 椭圆算子及弱解、逆算子与时间求导、真实函数空间内积的乘积法则，以及代理到 PDE 的对应 |
| Port 吸收层的 PDE 耗散恒等式与斜入射失配 | V5 TeX 第 501–505 行及其前文推导 | V5 Lean 无对应的完整定理；部分代数另由 SymPy 检查 | 实际模型的能量求导、通量及匹配分析 |

## Lean 文件具体证明了什么

### V5：六个定理陈述

`verification/algebra/VariableCoefficientBaffet.lean` 与
`lean_verification/PMLVerification/VariableCoefficientBaffet.lean` 内容相同，不是两份独立证明。

1. `debye_primitive_product_identity`：Debye 相关多项式展开。
2. `pq_determinant_identity`：极化二次型的行列式展开。
3. `two_a_sq_sub_b_expansion`：2a²-b 的多项式展开。
4. `grad_multiplier_component_identity`：u_tx+(a_x*u+a*u_x)=u_tx+a*u_x+u*a_x。
5. `absorption_sum_of_squares_identity`：完成平方恒等式。
6. `absorption_quadratic_nonpos`：给定系数条件下的标量二次式非正。

前四项的变量类型是有理数。`Pt`、`u_tx`、`a_x` 等只是变量名，并非形式化定义的导数。尤其第 4 项仅是代数重排，没有证明微分乘积法则。第 6 项有实际的辅助价值，但未连接到真实能量或 PDE 解。

### V6：十个定理陈述

`results/v6_tex/NonlocalMemoryStrictPML.lean` 的十个陈述涵盖：Schur 完成平方与吸收不等式、非局部代理的展开与余项、两种修正的代数余项、二元二次型正定性、导纳相等推出零反射，以及局部交叉项展开。

代码第 3–6 行明确声明：

> No PDE theorem is claimed here: the scalar variables encode the indicated finite-dimensional proxy blocks of the report.

两个容易误读的例子：

- 第 41–50 行 `nonlocal_derivative_residual` 中，`ut`、`lt` 是任意实数。代码检查已经写出的表达式，而没有证明这些量是实际函数的导数。
- 第 104–108 行 `admittance_equality_implies_zero_reflection` 直接假设 `Yp = Y0`。它没有证明 PML 两侧导纳相等，只证明在此前提下反射公式的分子为零。

这些文件没有定义 PDE 解、实际的 E_B(t)、空间积分或边界通量，也没有沿解的导数或时间单调性定理。问题在于形式化命题的覆盖范围；证明代码短或使用自动代数策略本身不是缺点。

## 三种“验证通过”需要区分

1. **Lean 检查通过**：证明文件里实际写出的那些命题成立。没有 `sorry` 或自定义公理，也不会自动扩大命题的范围。
2. **SymPy 检查通过**：检查指定代数表达式和测试例；不等于完整 PDE 定理的 Lean 形式化。
3. **Iteris agent 审查通过**：另一个 agent 审阅报告、证明说明、历史事实与运行结果后给出的判断。`verified`、`goal_success`、`gaps: []` 属于该工作流的审查结论，不是完整 PDE 定理的 Lean 证明项。

V6 TeX 第 405–407 行与 `results/v6_tex/verification_outputs.md:92` 比较准确地列出了辅助代数范围。V6 报告第 192 行“所有符号均由 Lean/SymPy 的展开回归覆盖”不宜被理解为整个能量恒等式已经形式化；核心 PDE 推导仍未进入 Lean。

## 已确认的运行状态

此前本对话中已在项目的 Lake/Mathlib 环境直接复跑：

- `lake env lean PMLVerification/VariableCoefficientBaffet.lean`：退出码 0。
- `lake env lean ../results/v6_tex/NonlocalMemoryStrictPML.lean`：退出码 0。
- `lake env lean ../verification/algebra/NewEnergyFunctional.lean`：退出码 1，首先在第 17 行出现类型类声明问题，继而出现除法等实例缺失和未关闭目标。

本次逐项对照没有重复编译，也没有修改原证明文件。

## 与用户目标相符的后续形式化验收标准

可以先固定 V6 已声明的角域、光滑相容解、正吸收和小梯度条件，不必一开始解决任意剖面的全部开放问题。至少应完成：

1. 在 Lean 中定义模型、空间变系数、边界条件和实际能量。
2. 从这些方程推出完整能量恒等式，而非把该恒等式直接当作假设。
3. 对真实向量余项和耗散证明积分吸收估计，得出 E_B'(t)+theta D_0(t)≤0。
4. 推出任意 t1≤t2 时 E_B(t2)≤E_B(t1)。
5. 如宣称能量控制解，再证明在所声明状态空间的统一范数上下界。

若只把能量导数非正或完整能量恒等式作为输入，再证明时间单调性，应明确标为条件性接口引理；它仍未核验核心 PDE 推导。
