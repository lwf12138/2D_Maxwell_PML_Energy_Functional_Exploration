# V7：二维 Maxwell–Debye PML 全域能量研究

本包对应 2026-09-24 的研究交付。建议先读 `V7_global_energy.pdf`：主定理为定理 6.1（第 10 页），完整求导、正定性与耗散闭合见第 7–9 节（第 10–14 页），实际二维剖面见第 10 节（第 15 页）。

## 结论

对原八变量系统、常材料、Debye 极化、整个矩形域的 PEC 边界，以及从零连续起步的非负分离吸收系数，本文证明一个**显式小幅度条件下的全域单调能量先验定理**。能量由常数移位乘子、辅助变量加权项和一阶时间导数层构成。它与文中指定的加权图范数等价，控制原电场、磁场、极化和全部四个 PML 辅助变量。

条件不要求吸收系数有正下界，不要求吸收梯度小，允许物理区、边层和角层同时存在。但它要求正文定义 5.1 的兼容初值与有限加权图范数，不覆盖任意八变量初值。

**任意幅度的一般非负分离变系数下，全域单调能量尚未证明。** 没有声称完整适定性、最优参数范围、无极化极限、分数阶或离散定理，也未声称该结果的文献首创性。

## 文件

| 文件 | 内容 |
|---|---|
| `V7_global_energy.pdf` | 18 页独立可读研究文稿；已用 XeLaTeX 编译并渲染检查 |
| `V7_global_energy.tex` | 可编辑的 LaTeX 正文，与 PDF 对应 |
| `V7_global_energy.md` | 正文 Markdown 版；公式与定理编号与 PDF 一致，数学渲染需要 MathJax/KaTeX |
| `proof_audit.md` | 主定理假设使用位置、证明链和结论边界检查 |
| `verify_v7.py` | 已运行的 SymPy 恒等式与示例参数核验 |
| `verification_output.txt` | 本次实际运行输出 |
| `source_manifest.json` | 核对输入路径、SHA-256 和原始论文核对范围 |

上传原文件未修改。没有重新分发大压缩包、第三方论文全文、字体文件或其依赖目录。

## 重现

PDF 源码使用 XeLaTeX、ctex、amsmath 等常见宏包，并指定系统已安装的 DejaVu Serif 与 Noto CJK 字体。请在本机安装合适字体，或修改 TeX 开头的字体名称；本包不含字体文件。

```bash
xelatex -interaction=nonstopmode -halt-on-error V7_global_energy.tex
xelatex -interaction=nonstopmode -halt-on-error V7_global_energy.tex
python verify_v7.py
```

Python 核验需要 `sympy`。脚本不进行 PDE 数值求解，也不是 Lean 形式化证明。空间积分、零吸收区、PEC、图范数控制和关键耗散吸收的证明在正文中，不能用脚本输出代替。
