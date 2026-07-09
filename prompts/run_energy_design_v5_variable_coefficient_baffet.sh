#!/usr/bin/env bash
set -euo pipefail

PROJECT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$PROJECT_DIR"

for required_dir in sources references results verification/algebra; do
  if [ ! -d "$required_dir" ]; then
    echo "Error: expected $required_dir/ directory in $PROJECT_DIR" >&2
    exit 1
  fi
done

if [ ! -f references/variable_coefficient_baffet_energy.pdf ]; then
  echo "Error: missing references/variable_coefficient_baffet_energy.pdf" >&2
  exit 1
fi

mkdir -p tex results/v5_variable_coefficient_baffet verification/algebra

GOAL_FILE="$(mktemp)"
trap 'rm -f "$GOAL_FILE"' EXIT

cat > "$GOAL_FILE" <<'EOF'
第五阶段目标：基于新加入的
references/variable_coefficient_baffet_energy.pdf
继续推进二维 Maxwell--Debye--PML 的单调下降能量泛函构造。

请牢记最终目标：
构造一个适用于二维 PML 系统的正定能量泛函，使其满足
\[
\frac{d}{dt}\mathcal E(t)\le 0
\]
或更强的
\[
\frac{d}{dt}\mathcal E(t)+\mathcal D(t)\le 0,\qquad \mathcal D(t)\ge0.
\]
如果只能得到 Gronwall 有界性、局部小梯度条件下的耗散，或某个替代模型的端口耗散，
必须明确说明它和最终目标之间的差距。

本轮不是重新泛泛设计模型，而是围绕新 PDF 的变量系数 Baffet 能量结果做严格审查、
修正和形式化验证。

必须读取的材料：
1. references/variable_coefficient_baffet_energy.pdf
2. results/energy_design_v3_perfect_matching_report.md
3. results/new_energy_functional_2d_debye_pml_report.md
4. tex/new_energy_functional_2d_debye_pml.tex，如果存在；
5. results/v3_v4_tex/new_energy_functional_2d_debye_pml.tex，如果存在；
6. verification/algebra/NewEnergyFunctional.lean
7. verification/algebra/new_energy_functional_sympy.py
8. references/Baffet 等 - 2019 - Energy Decay and Stability of a Perfectly Matched Layer For the Wave Equation.pdf
9. references/Joly - 2012 - An elementary introduction to the construction and the analysis of perfectly matched layers for time.pdf
10. references/Bécache 等 - 2023 - Convergence analysis of time-domain PMLS for 2D electromagnetic wave propagation in dispersive waveg.pdf

核心背景：
第三、四阶段已经得到：
- v2 covariantly damped Maxwell--Debye layer 有单调能量，但不是 perfectly matched；
- 标准 stretched-coordinate Maxwell--Debye PML 保持 perfect matching；
- 常系数 Baffet--Debye primitive 模型有非增耗散能量；
- 全域严格指数衰减存在零空间障碍，不能轻易声称。

新 PDF 似乎给出以下变量系数结论，请核实而不是直接相信：
1. 令
   \[
   a(x,y)=\sigma_x(x)+\sigma_y(y),\qquad
   b(x,y)=\sigma_x(x)\sigma_y(y),
   \]
   \[
   \Gamma_1=\operatorname{diag}(\sigma_x,\sigma_y),\qquad
   \Gamma_2=\operatorname{diag}(\sigma_y-\sigma_x,\sigma_x-\sigma_y).
   \]
2. Baffet primitive 变量满足
   \[
   E=u_t,\qquad q_t=P,\qquad q+\tau P=\kappa u,
   \]
   \[
   \lambda=\nabla u+\phi,\qquad
   \phi_t+\Gamma_1\phi=\Gamma_2\nabla u.
   \]
3. 变量系数 Baffet 能量导数中出现余项
   \[
   R_\sigma(t)
   =
   -\int_{\Omega_+}u\,\nabla a\cdot\lambda\,dxdy
   =
   -\int_{\Omega_+}u(\sigma_x'(x)\lambda_x+\sigma_y'(y)\lambda_y)\,dxdy.
   \]
4. 因为 \(\lambda\) 的符号不受 \(\nabla a\) 控制，单调性一般不能从
   \(\sigma_i'\ge0\) 推出。
5. 若 \(D_0\) 能同时控制 \(\|u\|\) 与 \(\|\lambda\|\)，且
   \(\|\nabla a\|_\infty\) 足够小，可能得到
   \[
   \frac{d}{dt}\mathcal E_B(t)+\theta D_0(t)\le0.
   \]
6. 新 PDF 还提出一个 port/weighted field 模型：
   \[
   \epsilon E_t+P_t+\epsilon\sigma_E E=\partial_x W_y-\partial_y W_x,
   \]
   \[
   \mu W_{x,t}+\mu\sigma_y W_x=-\partial_y E,\qquad
   \mu W_{y,t}+\mu\sigma_x W_y=\partial_x E,
   \]
   \[
   \tau P_t+P=\kappa E,
   \]
   其自然能量
   \[
   \mathcal E_{\rm port}(t)
   =
   \frac12\int_\Omega
   \left(\epsilon E^2+\mu W_x^2+\mu W_y^2+\kappa^{-1}P^2\right)\,dxdy
   \]
   满足
   \[
   \frac{d}{dt}\mathcal E_{\rm port}(t)
   +
   \int_\Omega
   \left(\epsilon\sigma_EE^2+\mu\sigma_yW_x^2+\mu\sigma_xW_y^2
   +\frac{\tau}{\kappa}P_t^2\right)\,dxdy
   =
   \int_{\partial\Omega}E(W_y n_x-W_x n_y)\,ds.
   \]

本轮必须完成的判断：

A. 先判断新 PDF 是否已经“足够好”
请给出明确结论：
- 是否已经构造出原目标所需的单调下降能量泛函？
- 这个单调能量对应的是严格 stretched-coordinate PML，还是一个稳定 absorbing/port layer？
- 如果是 port layer，它是否 perfect matching？请做 Laplace--Fourier 平面界面阻抗测试。
- 如果不是 perfect matching，是否可以作为数值稳定性工具使用，但不能作为最终 PML 定理？
- 变量系数 Baffet 能量的 \(R_\sigma\) 是否可以通过额外条件吸收？条件是否合理？

B. 变量系数 Baffet 能量的公式核查
必须逐式重推：
1. \(W=u_t+a u\)；
2. \(\nabla W=\nabla u_t+a\nabla u+u\nabla a\)；
3. Baffet 通量恒等式；
4. Debye primitive 乘积恒等式；
5. 变量系数余项
   \[
   R_\sigma=-\int u\nabla a\cdot\lambda;
   \]
6. \(D_0\ge0\) 的条件；
7. \(R_\sigma\) 不能由 \(\sigma_i'\ge0\) 保证非正的反例或代数说明；
8. 小梯度吸收条件，例如
   \[
   \|\nabla a\|_{L^\infty}^2<4m_um_\lambda
   \]
   的精确来源。

C. Port 模型的匹配性与能量性分开验证
对 port 模型必须分别回答：
1. 它是否在 \(\sigma_i=0\) 时退化为 Maxwell--Debye？
2. 它是否在平面界面上 perfect matching？
3. 若取 \(x\)-PML，\(\sigma_x>0,\sigma_y=0\)，请写出 Laplace--Fourier 代数系统；
4. 计算 \(E/W_y\) 或 \(W_y/E\) 的界面导纳；
5. 求反射系数 \(R\)，判断是否恒为零；
6. 若 \(\sigma_E\) 需要特殊选择才能匹配，请给出选择；
7. 若无法匹配，则报告必须称它为 stable absorbing layer，而不是 strict PML。

D. Lean 与 SymPy 形式化验证
本轮必须创建或更新以下文件：
- verification/algebra/VariableCoefficientBaffet.lean
- verification/algebra/variable_coefficient_baffet_sympy.py

Lean 验证至少覆盖：
1. Debye primitive 乘积恒等式：
   \[
   (P_t+aP+bq)(\tau P_t+(1+a\tau)P+a q)
   \]
   展开后等于能量导数项加
   \[
   \tau P_t^2+\tau(a^2-b)P^2+abq^2.
   \]
2. \(P,q\) 二次型行列式：
   \[
   \alpha\gamma-\beta^2
   =
   b+ab\tau+2a^3\tau+b(2a^2-b)\tau^2.
   \]
3. \(2a^2-b\ge0\) 在 \(a=\sigma_x+\sigma_y,b=\sigma_x\sigma_y,\sigma_x,\sigma_y\ge0\) 下成立的代数展开。
4. 变量系数余项来源：
   \[
   \nabla(u_t+a u)=\nabla u_t+a\nabla u+u\nabla a.
   \]
   Lean 可以验证一维或抽象代数版本，例如
   \[
   (u_t+a u)_x=u_{tx}+a u_x+u a_x.
   \]
5. 二维二次型吸收判据：
   对
   \[
   -m_u u^2-m_\lambda \lambda^2+g u\lambda
   \]
   证明当 \(g^2\le4m_um_\lambda\) 时其非正。

SymPy 验证至少覆盖：
- 所有 Lean 中的代数恒等式；
- port 模型能量导数中的 Maxwell 交叉项抵消；
- port 模型 Laplace--Fourier admittance/mismatch 公式；
- 小梯度吸收条件的 Schur 补。

必须实际运行：
- python3 verification/algebra/variable_coefficient_baffet_sympy.py
- lean verification/algebra/VariableCoefficientBaffet.lean

如果 Lean 因 Mathlib、toolchain 或证明复杂度失败，不要装作成功；请记录命令、输出和失败原因。
如果 Lean 成功，请在报告中给出成功输出摘要。

E. 输出要求
请生成以下文件：
1. results/v5_variable_coefficient_baffet/variable_coefficient_baffet_next_step_report.md
2. tex/variable_coefficient_baffet_energy_analysis.tex
3. tex/variable_coefficient_baffet_energy_analysis.pdf
4. tex/variable_coefficient_baffet_energy_analysis_build.log
5. verification/algebra/VariableCoefficientBaffet.lean
6. verification/algebra/variable_coefficient_baffet_sympy.py
7. results/v5_variable_coefficient_baffet/verification_outputs.md

中文 TeX 文档必须包含：
- 对新 PDF 的结论审查；
- 变量系数 Baffet 能量的完整推导；
- \(R_\sigma\) 的来源和失败机制；
- 小梯度吸收定理；
- port 模型的能量恒等式；
- port 模型是否 perfect matching 的独立判断；
- Lean/SymPy 验证结果；
- 下一步论文 theorem 的推荐形式。

最终报告必须给出清晰结论：
1. 如果新 PDF 已经足够接近最终目标，请说明还需要补哪些 Lean/SymPy 与文字证明即可进入论文。
2. 如果新 PDF 的 port 模型单调但不 perfect matching，请明确建议：它可作为稳定 absorbing layer，而 final PML 主线仍应采用 stretched-coordinate/Baffet primitive，并处理 \(R_\sigma\)。
3. 如果变量系数 stretched-coordinate Baffet 能量只能在小 \(\|\nabla a\|_\infty\) 下单调，请给出可写成 theorem 的精确假设。
4. 不得把“Gronwall 有界”误写成“单调下降”。
EOF

iteris run . \
  --goal "$(cat "$GOAL_FILE")" \
  --target-artifact results/v5_variable_coefficient_baffet/variable_coefficient_baffet_next_step_report.md \
  --foreground \
  --new-session
