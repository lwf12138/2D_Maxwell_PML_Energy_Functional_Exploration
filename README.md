# 2D Maxwell--PML Energy Functional Exploration

这个文件夹用于准备后续交给 iteris 分析的数学问题：探索图中二维 Maxwell--PML 系统是否存在单调递减的能量泛函；若找不到，则寻找能排除 PML 层异常增长的有界能量泛函。非分数阶情形按 `alpha=1` 处理，分数阶 `0<alpha<1` 放在第二阶段。

## 主要文件

- `sources/energy_functional_problem.tex`：建议交给 iteris 的主问题文件。
- `sources/energy_ansatz_notes.tex`：候选能量结构和试探思路，不是证明。
- `sources/macros.tex`：LaTeX 宏包和命令。
- `references/references.bib`：从研究现状报告复制来的 BibTeX 文献库。
- `ITERIS_INPUT_GUIDE.md`：给 iteris 前应该提供哪些文件、怎样写目标。
- `PROJECT.md`、`ROADMAP.md`：轻量项目说明。
- `references/`：当前重点参考资料副本。

## 建议研究顺序

1. 先验证 `energy_functional_problem.tex` 中图示 Maxwell--PML 模型的代数，包括 `P, P_{z,1}, P_{z,2}, Q_x, Q_y`。
2. 先研究 `alpha=1` 情形下常系数吸收参数的单调能量。
3. 使用 shifted variables 或时间积分辅助变量寻找 Baffet 型能量。
4. 推广到 `sigma_x(x), sigma_y(y)`，记录出现的系数梯度项。
5. 若不能得到单调能量，尝试证明有界能量或无异常增长估计，并明确写出障碍项。
6. 再考虑 `0<alpha<1` 的分数阶记忆与 diffusive representation。

## 编译

```bash
cd sources
xelatex energy_functional_problem.tex
bibtex energy_functional_problem
xelatex energy_functional_problem.tex
xelatex energy_functional_problem.tex
```

也可以编译候选笔记：

```bash
cd sources
xelatex energy_ansatz_notes.tex
```
