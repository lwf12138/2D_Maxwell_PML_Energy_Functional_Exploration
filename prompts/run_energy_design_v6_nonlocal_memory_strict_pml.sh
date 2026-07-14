#!/usr/bin/env bash
set -euo pipefail

PROJECT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$PROJECT_DIR"

export PATH="$HOME/.elan/bin:$PATH"

OUT_DIR="results/v6_tex"
REFERENCE_PDF="references/nonlocal_memory_energy_strict_pml.pdf"
LEAN_PROJECT="lean_verification"

for required_dir in sources references results prompts verification "$LEAN_PROJECT"; do
  if [ ! -d "$required_dir" ]; then
    echo "Error: expected $required_dir/ in $PROJECT_DIR" >&2
    exit 1
  fi
done

if [ ! -f "$REFERENCE_PDF" ]; then
  echo "Error: missing $REFERENCE_PDF" >&2
  exit 1
fi

if [ ! -f "$LEAN_PROJECT/lakefile.toml" ]; then
  echo "Error: missing $LEAN_PROJECT/lakefile.toml; the Mathlib project is required." >&2
  exit 1
fi

mkdir -p "$OUT_DIR"

GOAL_FILE="$(mktemp)"
trap 'rm -f "$GOAL_FILE"' EXIT

cat > "$GOAL_FILE" <<'EOF'
第六阶段任务：审查并推进“二维变系数严格 PML 的非局部记忆能量”。

本轮的最终目标仍然是：对于连续情形下的二维 Maxwell--Debye 系统，在

\[
\sigma_x=\sigma_x(x),\qquad \sigma_y=\sigma_y(y),\qquad
\sigma_x,\sigma_y\ge 0
\]

所定义的严格 stretched-coordinate PML 中，构造一个正定、与自然状态范数等价的能量泛函
\(\mathcal E(t)\)，并严格证明

\[
\frac{d}{dt}\mathcal E(t)+\mathcal D(t)\le 0,
\qquad \mathcal D(t)\ge 0.
\]

“严格 PML”与“有耗散的吸收层”必须分开判断。本轮不能用前一轮已经证伪为斜入射不匹配的
port layer 替代最终模型。若无条件单调性仍无法证明，必须给出最强的条件性定理、明确失败项，
或者给出经过验证的障碍；不能把 Gronwall 有界性写成单调下降。

所有本轮交付物必须放在：

results/v6_tex/

不得把新的终端交付物写到 tex/、results/v5-tex/ 或其他旧结果目录，也不得覆盖旧文件。

一、必须读取并建立可追溯资料表

至少完整阅读并实际使用下列材料中的模型、公式、定理假设和证明思路：

1. references/nonlocal_memory_energy_strict_pml.pdf
2. references/variable_coefficient_baffet_energy.pdf
3. results/v5_variable_coefficient_baffet/variable_coefficient_baffet_next_step_report.md
4. results/v5-tex/variable_coefficient_baffet_energy_analysis.tex
5. references/Baffet 等 - 2019 - Energy Decay and Stability of a Perfectly Matched Layer For the Wave Equation.pdf
6. references/Joly - 2012 - An elementary introduction to the construction and the analysis of perfectly matched layers for time.pdf
7. references/Bécache 等 - 2023 - Convergence analysis of time-domain PMLS for 2D electromagnetic wave propagation in dispersive waveg.pdf
8. references/Bécache 等 - 2021 - On a surprising instability result of Perfectly Matched Layers for Maxwell’s equations in 3D media w.pdf
9. sources/energy_functional_problem.tex
10. sources/energy_ansatz_notes.tex
11. verification/algebra/VariableCoefficientBaffet.lean
12. verification/algebra/variable_coefficient_baffet_sympy.py
13. lean_verification/PMLVerification/VariableCoefficientBaffet.lean

报告中建立“来源--公式/结论--页码或公式号--本轮用途”表。新加入的
nonlocal_memory_energy_strict_pml.pdf 是待审查的研究材料，不是已经同行评审的外部文献；
其中任何引理、非局部能量或 Gramian 论证都必须重新推导，不能因 PDF 中已经写出便视为成立。

若引用正式文献中的结果，必须给出作者、题名、年份、期刊信息和可核实的 DOI 或原始网页；
无法核实的内容标记“待核实”，不得编造。

二、固定最终研究对象：严格坐标拉伸 Maxwell--Debye PML

先统一记号：

\[
\epsilon E_t+P_t=\partial_xH_y-\partial_yH_x,
\]
\[
\mu H_{x,t}=-\partial_yE,\qquad
\mu H_{y,t}=\partial_xE,
\]
\[
\tau P_t+P=\kappa E,
\qquad \epsilon,\mu,\tau,\kappa>0.
\]

在 Laplace 域使用

\[
S_i(s,x_i)=1+\frac{\sigma_i(x_i)}{s},
\qquad \partial_i\mapsto S_i^{-1}\partial_i,
\]

写出严格 stretched-coordinate Maxwell--Debye PML，并将其无歧义地逆变换为时域 ADE、
split-field 或 Baffet primitive 系统。必须说明：

1. 时域未知量及其初值兼容条件；
2. PML 内边界、物理区/PML 界面、外边界的条件；
3. \(\sigma_i\) 的非负性、正则性、支集和界面条件；
4. 当 \(\sigma_x=\sigma_y=0\) 时如何退化回 Maxwell--Debye；
5. Baffet primitive 变量 \(u,q,\lambda,\phi\) 与物理变量 \(E,H,P\) 的精确关系；
6. 时域扩展系统是否与 Laplace 域 strict PML 完全等价，而不是只在某些模态上相似。

三、先独立验证 perfect matching

对平直的 x-PML 界面执行完整的 Laplace--Fourier 匹配计算：

1. 取 \(\operatorname{Re}s>0\) 和任意切向频率 \(k_y\)；
2. 写出物理侧和 PML 侧色散关系；
3. 固定衰减分支，不能只比较导纳平方而忽略平方根分支；
4. 推导界面导纳 \(Y_0\) 与 \(Y_+\)；
5. 写出传输条件、反射系数 \(R\)，证明 \(R=0\)；
6. 说明结论对任意法向变系数 \(\sigma_x(x)\) 是否成立；
7. 区分“内界面无反射”与“有限厚 PML 外边界截断后完全无反射”；
8. 检查角区 \(\sigma_x\sigma_y>0\) 以及所谓 multi-axial/cross damping 是否仍保持匹配。

任何后续候选模型若改变了 stretched-coordinate 的符号，必须重新执行上述测试。
只有 \(R(s,k_y)\equiv0\) 才能称为 perfectly matched。

四、精确复核现有 Baffet 余项

令

\[
a=\sigma_x+\sigma_y,qquad b=\sigma_x\sigma_y,
\qquad W=u_t+a u.
\]

逐行重新推导

\[
\nabla W=\nabla u_t+a\nabla u+u\nabla a
\]

以及

\[
\frac{d}{dt}\mathcal E_B(t)
=-\mathcal D_0(t)+R_\sigma(t)+\mathcal B(t),
\qquad
R_\sigma(t)=-\int_\Omega u\,\nabla a\cdot\lambda\,dxdy.
\]

必须列出 \(\mathcal E_B\)、\(\mathcal D_0\)、\(\mathcal B\) 的全部项，检查所有系数、
符号、积分分部和边界项。然后给出：

1. \(\mathcal E_B\) 正定及与自然范数等价的精确参数条件；
2. \(\mathcal D_0\ge0\) 的精确条件；
3. \(R_\sigma\) 无固定符号的可复查反例；
4. 小梯度 Schur 吸收条件的点态矩阵形式和积分形式；
5. 小梯度结论究竟给出 \(\mathcal E_B'\le0\)，还是只给出带常数的估计；
6. 在物理区 \(a=0\) 时，包含 \(a^{-1}\) 的表达式如何定义、分区或取极限。

五、本轮核心：严格审查非局部椭圆修正

新 PDF 提出候选算子和修正项

\[
\mathcal L v=-\nabla\cdot(C_\lambda\nabla v)+c_u v,
\qquad
z=\mathcal L^{-1}\nabla\cdot(u\nabla a),
\]

以及类似

\[
\mathcal E_{\mathrm{nl}}
=\mathcal E_B
+\eta\int_{\Omega_+}\lambda\cdot\nabla z\,dxdy
+\frac{\eta}{2}\int_{\Omega_+}
\left(C_\lambda\nabla z\cdot\nabla z+c_u z^2\right)dxdy.
\]

这目前只是候选，不是已经证明的单调能量。必须完成以下计算：

1. 明确 \(\Omega_+\)、\(\mathcal L\) 的定义域、边界条件、核空间及可逆性；
2. 说明 \(C_\lambda\)、\(c_u\) 是标量还是矩阵，并给出一致的椭圆性条件；
3. 推导弱形式
   \[
   (C_\lambda\nabla z,\nabla v)+(c_u z,v)
   =-(u\nabla a,\nabla v)
   \]
   的符号和边界项；
4. 由于 \(a\) 与时间无关，严格计算
   \[
   z_t=\mathcal L^{-1}\nabla\cdot(u_t\nabla a);
   \]
5. 完整展开
   \[
   \frac{d}{dt}(\lambda,\nabla z),\qquad
   \frac{d}{dt}\frac12(\mathcal Lz,z),
   \]
   包括 \(\lambda_t\)、\(z_t\) 和所有边界项；
6. 判断这些项是否精确抵消 \(R_\sigma\)，还是产生新的
   \(u_t\)、\(\lambda_t\)、\nabla a\) 余项；
7. 用 Schur 补证明或否定 \(\mathcal E_{\mathrm{nl}}>0\)；
8. 证明或否定 \(\mathcal E_{\mathrm{nl}}\) 与目标状态空间自然范数等价；
9. 若原候选失败，修改交叉项或引入第二个椭圆变量，至少尝试两种可计算的修正；
10. 给出最终导数恒等式，不能用“可以类似得到”“形式上抵消”跳过。

若该路线成功，给出完整的定义--引理--定理--证明。若失败，必须展示未消失的具体公式，
并说明是系数选择问题、导数损失、边界问题，还是结构性障碍。

六、比较三条能量构造路线

除上面的椭圆非局部修正外，至少比较并实际计算以下路线：

A. 局部加权/交叉项路线

允许

\[
\mathcal E_{\mathrm{loc}}
=\mathcal E_B+(c_1(x)u,\lambda_x)+(c_2(y)u,\lambda_y)
+\text{其他必要交叉项}.
\]

推导系数 \(c_i\) 为消除 \(\nabla a\) 项所需满足的 ODE、Riccati 方程或矩阵微分不等式，
并检查正定性、界面兼容性和是否破坏 perfect matching。

B. 椭圆非局部修正路线

以第五部分的完整时间导数为依据判断，不得只做静态 Schur 补。

C. 半群 Gramian/时域记忆路线

对

\[
\mathcal E_G(U)=\int_0^\infty\|C e^{tA_\sigma}U\|^2\,dt,
\qquad
A_\sigma^*G+GA_\sigma=-C^*C
\]

必须说明：

1. \(A_\sigma\) 的状态空间、定义域、边界条件及生成性；
2. 上式收敛需要何种预先稳定性；
3. 若用 Gramian 来证明稳定性，是否形成循环论证；
4. \(G\) 是否正定，是否与自然能量范数等价；
5. 若只有强稳定而无指数稳定，应使用有限时域 Gramian、加权 Gramian还是 resolvent 方法；
6. 能否从 positive-real/passivity 或 KYP 思路得到可实现的记忆变量；
7. ratio kernel
   \[
   \frac{s+\sigma_j}{s+\sigma_i}
   =1+\frac{\sigma_j-\sigma_i}{s+\sigma_i}
   \]
   的时域核可能变号时，怎样验证整体矩阵核的正定性。

每条路线至少给出一个明确候选和完整到可判断成功/失败的导数计算。最终按照：
perfect matching 保持性、能量正定性、单调性、参数条件、可推广到 Cole--Cole、可用于 DG
六项进行比较，并选出下一篇论文最值得继续的路线。

七、先做低维和冻结系数的必要性检验

在声称 PDE 能量成立前，执行下列反例搜索或必要条件测试：

1. \(k_y=0\) 的一维法向模态；
2. 任意 \(k_y\ne0\) 的冻结 Fourier 模态；
3. 常系数边层和角层；
4. \(\nabla a\ne0\) 的局部冻结/缓变模型；
5. 高梯度阻尼剖面；
6. 物理区--PML 界面附近 \(a\to0\)；
7. 零频或静态模态。

对每个候选二次型写出矩阵 \(M\) 与耗散矩阵 \(Q\)，检查

\[
M>0,\qquad Q\ge0
\]

所需条件。使用 Sylvester 判据、Schur 补、完成平方或特征值分析；不得写“显然正定”。

八、Lean 与 SymPy 必须实际运行

在 results/v6_tex/ 创建：

1. NonlocalMemoryStrictPML.lean
2. nonlocal_memory_strict_pml_sympy.py
3. verification_outputs.md

Lean 至少形式化验证：

1. v5 已使用的二次型 Schur 吸收判据；
2. 新非局部修正的有限维代理模型中，能量展开与导数交叉项抵消；
3. 若出现新的余项，验证其精确代数表达式；
4. 一个 \(2\times2\) 或 \(3\times3\) 候选能量矩阵正定的充分条件；
5. perfect-matching 导纳代数中 \(Y_+=Y_0\Rightarrow R=0\) 的代数步骤；
6. 不得用 sorry、admit 或未声明公理绕过证明。

必须使用已经存在的 Lake/Mathlib 环境运行：

cd lean_verification
lake env lean ../results/v6_tex/NonlocalMemoryStrictPML.lean

不要再直接运行裸命令

lean results/v6_tex/NonlocalMemoryStrictPML.lean

因为它可能找不到 Mathlib。运行前记录：

command -v lake
lake --version
lake env lean --version

SymPy 至少验证：

1. strict PML 色散与导纳匹配；
2. Baffet 余项的乘积法则来源；
3. 非局部修正有限维代理的完整导数；
4. 所有完成平方和 Schur 补恒等式；
5. 局部交叉项路线留下的余项；
6. 选定候选在随机正参数和边界参数上的数值特征值抽查。

运行：

python3 results/v6_tex/nonlocal_memory_strict_pml_sympy.py

把命令、退出码和完整关键输出记录到
results/v6_tex/verification_outputs.md。失败必须如实保留并解释，修复后重新运行。

九、结论分级

最终只允许使用下列分级之一：

Level A：已证明无条件单调能量

\[
\mathcal E'(t)+\mathcal D(t)\le0
\]

对所声明的全部变系数类成立，且 \(\mathcal E\) 正定、等价，模型严格 perfect matching。

Level B：已证明条件性单调能量

明确列出例如小 \(\|\nabla a\|_\infty\)、椭圆 Schur、剖面结构或几何条件，给出可写入论文的精确定理。

Level C：只得到非局部/Gramian 条件定理

必须列出半群稳定性、可观测性或 resolvent 假设，并说明这些假设是否已经独立证明。

Level D：候选失败但得到结构性障碍

给出明确余项、反例或矩阵不可行性证据，并提出下一条最小可执行路线。

不能把 Level B/C/D 写成 Level A，也不能把“界面 perfect matching”与“外边界截断误差为零”混为一谈。

十、交付物与编译

必须生成并只在 results/v6_tex/ 放置本轮终端交付物：

1. nonlocal_memory_strict_pml_report.md
2. nonlocal_memory_strict_pml_analysis.tex
3. nonlocal_memory_strict_pml_analysis.pdf
4. nonlocal_memory_strict_pml_analysis_build.log
5. NonlocalMemoryStrictPML.lean
6. nonlocal_memory_strict_pml_sympy.py
7. verification_outputs.md
8. claims_and_open_problems.md

中文 TeX 使用 ctexart 和 XeLaTeX。建议在 results/v6_tex/ 中运行：

xelatex -interaction=nonstopmode -halt-on-error nonlocal_memory_strict_pml_analysis.tex
xelatex -interaction=nonstopmode -halt-on-error nonlocal_memory_strict_pml_analysis.tex

把两次编译输出写入 nonlocal_memory_strict_pml_analysis_build.log。修复所有编译错误、未定义引用、
缺失文献和严重 overfull box。报告必须包含定义、引理、定理、证明、失败路线的公式、
Lean/SymPy 实际输出摘要以及明确的下一步建议，不能只给研究提纲。

Iteris 最终验证必须针对
results/v6_tex/nonlocal_memory_strict_pml_report.md
及其对应 TeX/PDF、Lean、SymPy 证据。只有在“严格 PML + 能量结论 + 机器验证”的量词范围
与本任务一致时才能声明完成；否则采用诚实的条件性结论或 principled stop。
EOF

iteris run . \
  --goal "$(<"$GOAL_FILE")" \
  --target-artifact "$OUT_DIR/nonlocal_memory_strict_pml_report.md" \
  --foreground \
  --new-session
