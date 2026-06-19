# Iteris Input Guide

给 iteris 分析时，建议优先提供 `sources/energy_functional_problem.tex`。这个文件是自洽的问题说明，包含模型、目标、候选变量和交付要求。

## 必须提供

- `sources/energy_functional_problem.tex`
- `sources/macros.tex`
- `references/references.bib`

## 建议同时提供

- `sources/energy_ansatz_notes.tex`
- `references/Baffet 等 - 2019 - Energy Decay and Stability of a Perfectly Matched Layer For the Wave Equation.pdf`
- `references/Huang 等 - 2023 - Developing and analyzing an explicit unconditionally stable finite element scheme for an equivalent.pdf`
- `references/Thesis.pdf`

## 推荐给 iteris 的目标文本

```text
Analyze sources/energy_functional_problem.tex. The model is the displayed 2D Maxwell--PML system with P, P_{z,1}, P_{z,2}, Q_x, Q_y and PEC boundary condition. Start with the alpha = 1 case of P + tau^alpha partial_t^alpha P = chi E; do not remove P from the model. Search first for a monotone decreasing energy functional in two dimensions. If no monotone energy can be found, derive the strongest bounded-energy/no-abnormal-growth estimate possible, in the spirit of MPML long-time stability, or identify a verified obstruction for natural quadratic energies. Only after the alpha = 1 model is understood, examine whether the fractional case 0 < alpha < 1 can be added as a positive memory energy. Write the final result to results/energy_functional_report.md.
```

## 给 iteris 前最好明确的选择

1. 是否先只研究常系数 `sigma_x, sigma_y`。
2. 是否允许 `sigma_x=sigma_x(x), sigma_y=sigma_y(y)`，还是直接挑战 `sigma_x(x,y), sigma_y(x,y)`。
3. 边界条件选 periodic、PEC、还是外边界零通量。
4. 能量泛函是否允许包含时间积分变量，例如 `int_0^t Q_x`.
5. 能量泛函是否允许包含空间导数或非局部项。
6. 是否只研究 `alpha=1`，还是在第二阶段继续处理 `0<alpha<1` 的分数阶记忆。

## 不建议一开始让 iteris 做的事

- 不要一开始就要求完整二维变系数 + 分数阶 `0<alpha<1` + DG 离散 + 超收敛。
- 不要把“找到单调能量”写成唯一成功标准；若它能证明自然二次型不可能单调，也很有价值。
- 不要让它直接依赖综述报告里的叙述，应以 `energy_functional_problem.tex` 的模型和假设为准。
