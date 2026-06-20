#!/usr/bin/env bash
set -euo pipefail

PROJECT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$PROJECT_DIR"

for required_dir in sources references results; do
  if [ ! -d "$required_dir" ]; then
    echo "Error: expected $required_dir/ directory in $PROJECT_DIR" >&2
    exit 1
  fi
done

mkdir -p tex verification/algebra

GOAL_FILE="$(mktemp)"
trap 'rm -f "$GOAL_FILE"' EXIT

cat > "$GOAL_FILE" <<'EOF'
请读取并分析当前项目目录中的全部相关材料。

本任务的目标不是简单验证现有的能量泛函，而是重新设计一种适用于二维
Maxwell--Debye--PML 系统的新能量泛函，使其满足下列性质之一：
\[
\frac{\mathrm d}{\mathrm dt}\mathcal E(t)\le 0,
\]
或者更强的衰减估计
\[
\frac{\mathrm d}{\mathrm dt}\mathcal E(t)+\mathcal D(t)\le 0,
\qquad \mathcal D(t)\ge 0,
\]
并在条件允许时进一步得到
\[
\mathcal E(t)\le \mathcal E(0)e^{-\gamma t},\qquad \gamma>0,
\]
或者其他明确的多项式衰减、积分衰减或有界稳定性结论。

重要要求：
1. 不要只验证已有能量泛函。
2. 不要只生成研究提纲。
3. 必须给出实质性的数学推导、候选能量比较、正定性检查和能量恒等式。
4. 允许对当前 PML 模型进行合理修改，但必须说明是否仍然 perfect matching。
5. 先处理 alpha=1 的 Debye 情形，再讨论 0<alpha<1 的 Cole--Cole 推广。
6. 如果某处无法证明，必须明确写出公式层面的原因，不能用模糊语言带过。

必须读取的项目材料：
- sources/energy_functional_problem.tex
- sources/energy_ansatz_notes.tex
- results/energy_functional_report.md
- results/energy_functional_report_verified.md
- results/energy_design_v2_report.md
- results/energy_design_v2_report_verified.md
- 若存在，读取 results/energy_design_v3_perfect_matching_report.md
- references/references.bib
- references/ 目录中的相关 PDF，尤其是 Joly、Baffet、Becache、Huang、
  Berenger/CFS/MPML/ADE-PML、用户手稿 main.pdf、Super.pdf、Thesis.pdf。

对参考文献的要求：
- 必须在最终 TeX 文档中列出“文献阅读记录表”。
- 对每篇实际引用的文献，记录作者、题目、年份、阅读的页码/章节/公式、
  以及它对本问题的具体作用。
- 不得虚构 DOI、定理编号、页码或结论。
- 若 PDF 无法解析或某结论尚未核实，必须标记“待核实”。

一、整理现有模型

首先从项目材料中提取当前使用的二维 PML 模型，准确列出：
- 原始 Maxwell 方程；
- Debye 或 Cole--Cole 极化方程；
- PML 引入的辅助变量；
- 各方向阻尼系数；
- 初始条件和边界条件；
- 当前能量泛函；
- 当前证明中不能得到单调性或衰减性的关键原因。

所有符号必须尽量沿用原稿中的记号。若不同文件中的记号不一致，请统一记号，
并制作符号对照表。必须区分：
- 用户原始模型；
- Iteris 第二轮提出的 covariantly damped Maxwell--Debye absorbing layer；
- 本轮重新设计或修正的 PML 模型。

二、先研究 alpha=1 的 Debye 模型

先将分数阶参数取为
\[
\alpha=1,
\]
把 Cole--Cole 模型退化为 Debye 模型。明确写出极化变量满足的常微分方程，
例如
\[
\tau_0 P_t+P
=
\epsilon_0(\epsilon_{r,s}-\epsilon_{r,\infty})E.
\]

在此基础上研究二维 Maxwell--Debye--PML 系统。

允许对当前 PML 模型进行合理修改，不必局限于原稿中的 PML 形式。可以考虑：
- split-field PML；
- unsplit PML；
- convolutional PML；
- ADE-PML；
- 对称双曲形式的 PML；
- 通过附加记忆变量构造的被动型 PML；
- 在两个坐标方向使用不同阻尼系数的 PML；
- 为便于能量分析而设计的等价扩展系统。

选择模型时，应优先考虑以下性质：
1. PML 系统是适定的；
2. 所有阻尼项具有明确的耗散意义；
3. 能量泛函正定或与系统自然范数等价；
4. 能量导数中的交叉项能够严格抵消或被吸收；
5. 能够证明单调递减、指数衰减或积分意义下的衰减；
6. 与 Maxwell--Debye 方程具有合理的一致性；
7. 当阻尼系数取零时能够退化回原始物理系统；
8. 必须验证是否具有 perfect matching 性质；若无法证明，必须明确说明，并且不能把该模型称为严格 PML。

三、验证 perfect matching 性质

在构造或选择新能量泛函之前，必须先对候选 PML 模型进行 perfect matching
验证。该验证不能只用文字说明，必须包含公式层面的反射系数或阻抗匹配计算。

请至少完成以下检查：

1. 平面界面设置：
   - 物理区域取 \(\sigma_x=\sigma_y=0\) 或 \(\rho_x=\rho_y=0\)；
   - PML 区域先取常系数，例如 \(x>0\) 中 \(\sigma_x>0,\sigma_y=0\)；
   - 再说明变系数情形是否只能通过局部冻结系数或渐近论证处理。

2. Laplace--Fourier 模态：
   取
   \[
   U(x,y,t)=\widehat U e^{st+i k_y y+i k_x x},
   \qquad \Re s>0,
   \]
   或等价的 time-harmonic 模态，推导物理区域和 PML 区域的代数系统。

3. 色散关系与法向波数：
   - 写出物理 Maxwell--Debye 系统的色散关系；
   - 写出 PML 系统的拉伸坐标或辅助变量对应的色散关系；
   - 验证 PML 法向波数是否等于物理法向波数经过复坐标拉伸后的结果。

4. 阻抗/导纳匹配：
   - 计算界面处切向场比值，例如 \(E_z/H_y\) 或等价导纳；
   - 写出入射波、反射波、透射波的界面条件；
   - 求反射系数 \(R\)，并判断是否对所有入射角、频率和 Debye 参数都有 \(R=0\)。

5. 对 Iteris 第二轮提出的 covariantly damped Maxwell--Debye absorbing layer
   必须单独测试：
   \[
   P+\tau(\partial_t+\rho)P=\chi E
   \]
   是否改变 Maxwell--Debye 材料响应和界面阻抗。若改变，必须给出失配公式，
   并说明该模型应称为 stable absorbing layer 而不是 perfectly matched layer。

6. 若最终选择的模型无法严格证明 perfect matching，TeX 文档必须明确写出：
   - 已证明的是能量稳定/耗散，而不是完美匹配；
   - 失配来源于哪一项；
   - 是否存在修改模型以恢复 perfect matching 的可行路线。

四、构造新的能量泛函

不要预先假定能量泛函只能是各变量 L^2 范数平方的简单求和。请系统考察包含
交叉项和加权项的候选泛函，甚至可以包含对应变量的导数项，可参考 Baffet
文章中通过时间积分变量和增广量构造能量的方法。例如
\[
\mathcal E(t)
=
\frac12
\left(
a_E\|E\|^2
+a_H\|H\|^2
+a_P\|P\|^2
+\sum_j a_j\|\Psi_j\|^2
\right)
+\sum_j b_j(E,\Psi_j)
+\sum_j c_j(P,\Psi_j),
\]
其中 \(\Psi_j\) 表示 PML 或 Debye 辅助变量。

还应考虑 Lyapunov 型修正项，例如
\[
\mathcal L(t)
=
\mathcal E_0(t)
+\eta_1(E,\Psi_1)
+\eta_2(H,\Psi_2)
+\eta_3(E,P),
\]
并通过选择参数 \(\eta_i\) 消除或控制能量导数中的非定号交叉项。

请至少给出三类候选能量泛函，并逐一分析：
- 正定性；
- 与自然 L^2 范数的等价性；
- 时间导数；
- 交叉项结构；
- 对阻尼系数和物理参数的要求；
- 是否能得到严格耗散；
- 该候选方案失败或成功的原因。

候选类型建议至少包括：
1. 自然电磁能量 + Debye 极化能量 + PML 辅助变量能量；
2. 含 \(E\)--P、\(E\)--PML 变量、\(H\)--PML 变量交叉项的 Lyapunov 泛函；
3. Baffet 型或时间积分变量型增广能量；
4. 若合适，可加入一阶导数项或 curl/div 型补偿项。

最终选出一个最有希望的能量泛函，给出完整推导。

五、完整推导能量恒等式

对选定的模型和能量泛函，逐方程乘以适当的测试函数并积分，详细写出：
1. 每个方程乘以哪个变量或线性组合；
2. 每个积分分部步骤；
3. 边界通量项；
4. PEC、周期或吸收边界条件下边界项如何处理；
5. Debye 极化项如何产生耗散；
6. PML 辅助变量如何产生耗散；
7. 交叉项如何精确抵消；
8. 不能精确抵消的项如何利用 Young 不等式、Schur 补或矩阵正定性吸收；
9. 最终的能量恒等式或能量不等式。

目标形式优先为
\[
\frac{\mathrm d}{\mathrm dt}\mathcal E(t)
=
-\mathcal D(t),
\qquad
\mathcal D(t)\ge 0.
\]

若无法得到该形式，则尝试证明
\[
\frac{\mathrm d}{\mathrm dt}\mathcal E(t)
\le
-c_1\mathcal E(t)+c_2\mathcal R(t),
\]
并明确说明余项 \(\mathcal R(t)\) 的来源以及在什么条件下可以消失或被控制。

六、用矩阵方法检验正定性

将候选能量在每个空间点写为二次型
\[
\mathcal E_{\mathrm{loc}}
=
\frac12 U^{\mathsf T}MU,
\]
其中 \(U\) 包含电场、磁场、极化变量和 PML 辅助变量。

同时将耗散项写为
\[
\mathcal D_{\mathrm{loc}}
=
U^{\mathsf T}QU.
\]

请计算并分析矩阵 \(M\) 和 \(Q\)，通过以下方式验证：
- Sylvester 判据；
- Schur 补；
- 特征值分析；
- 完成平方；
- 参数区间分析。

需要明确给出保证
\[
M>0,\qquad Q\ge 0
\]
所需的参数条件。

不要只写“显然正定”或“容易验证”，必须给出可复查的计算过程。

七、符号计算和形式化验证

请创建独立的验证文件，对核心代数恒等式进行机器辅助检查。至少创建：
- verification/algebra/new_energy_functional_sympy.py
- verification/algebra/NewEnergyFunctional.lean

SymPy 验证至少应检查：
- 能量二次型矩阵 \(M\) 的主子式；
- 耗散矩阵 \(Q\) 的半正定条件；
- 完成平方恒等式；
- 关键交叉项抵消；
- 参数条件下的二阶或三阶矩阵 Schur 补。

Lean 验证至少应尝试覆盖：
- 能量二次型的代数展开；
- 完成平方恒等式；
- 参数为正时某些二次型非负；
- 由
  \[
  a>0,\quad c>0,\quad ac-b^2>0
  \]
  推出二阶对称矩阵
  \[
  \begin{pmatrix}
  a&b\\
  b&c
  \end{pmatrix}
  \]
  正定；
- 能量导数中关键交叉项的抵消。

运行所有能够运行的验证程序，并在 TeX 文档中记录实际输出。若 Lean 环境不可用，
必须记录尝试命令和失败原因；但 SymPy 验证应尽量运行成功。

八、衰减结论

在得到
\[
\mathcal E'(t)+\mathcal D(t)\le 0
\]
后，继续分析 \(\mathcal D(t)\) 是否能够控制 \(\mathcal E(t)\)。

区分讨论：
1. 仅有单调性：
   \[
   \mathcal E(t)\le \mathcal E(0);
   \]
2. 积分耗散：
   \[
   \mathcal E(t)+\int_0^t\mathcal D(s)\,\mathrm ds
   \le
   \mathcal E(0);
   \]
3. 指数衰减：
   \[
   \mathcal E(t)\le C e^{-\gamma t}\mathcal E(0);
   \]
4. 只有部分变量受阻尼时，是否需要：
   - Poincare 不等式；
   - Maxwell 型 Poincare 不等式；
   - 几何控制条件；
   - 阻尼系数严格正；
   - 边界条件排除零频模；
   - 额外的补偿泛函或乘子方法。

必须区分“能量单调递减”和“能量严格指数衰减”，不能把二者混为一谈。

九、与原模型比较

将新构造的 PML 模型和能量泛函与用户原模型进行比较，至少说明：
- 原模型为何难以得到单调能量；
- 新模型增加、删除或重新定义了哪些辅助变量；
- 新能量泛函相比原能量增加了哪些权重或交叉项；
- 新模型是否仍具有完美匹配性质；
- 若不能严格证明完美匹配，应明确说明；
- 新模型对后续 DG 离散和数值稳定性分析是否更友好；
- 新模型是否容易推广到 \(0<\alpha<1\) 的 Cole--Cole 情形。

十、输出文件要求

请在当前项目中创建一个独立、完整、可编译的中文 LaTeX 文档：
tex/new_energy_functional_2d_debye_pml.tex

同时编译生成：
tex/new_energy_functional_2d_debye_pml.pdf

并保存编译日志：
tex/new_energy_functional_2d_debye_pml_build.log

同时生成一份简短 Markdown 摘要：
results/new_energy_functional_2d_debye_pml_report.md

TeX 文档建议包含以下结构：
1. 引言与研究目标；
2. 原二维 PML 模型及现有困难；
3. 二维 Maxwell--Debye 模型；
4. perfect matching 判据与候选模型验证；
5. 新 PML 模型的设计；
6. 候选能量泛函的比较；
7. 新能量泛函的构造；
8. 正定性证明；
9. 能量恒等式；
10. 单调性与衰减性定理；
11. 机器辅助代数验证；
12. 与原模型的比较；
13. 结论与尚未解决的问题。

文档中必须包含：
- 清晰的定义、引理、定理和证明；
- 完整公式推导；
- 所有参数条件；
- 不能证明之处的明确说明；
- SymPy 或 Lean 验证结果摘要；
- 与当前论文符号一致的记号；
- 必要的参考文献条目；
- 文献阅读记录表。

LaTeX 编译要求：
- 使用 ctexart 或等价中文文档类；
- 优先用 xelatex 编译；
- 若使用 bibtex/biber，需要相应运行；
- 修复所有导致编译失败的错误；
- 尽量消除未定义引用和严重 overfull box；
- 在 Markdown 摘要中记录实际编译命令和结果。

最终判断必须保守：
- 如果找到单调耗散能量，给出定理、条件和完整证明；
- 如果只能得到积分耗散或有界稳定性，明确写出为什么不能得到更强结论；
- 如果 perfect matching 无法证明，必须把模型定位为 absorbing layer 或 stable layer，
  不要称为严格 PML；
- 不得把参考文献中的结论误写成用户已经完成的结论。
EOF

iteris run . \
  --goal "$(cat "$GOAL_FILE")" \
  --target-artifact tex/new_energy_functional_2d_debye_pml.tex \
  --foreground \
  --new-session
