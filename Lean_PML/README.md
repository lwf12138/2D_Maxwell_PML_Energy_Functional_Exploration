# LeanPML：系数条件、零吸收分支和精确小量条件

用途：作为 v0.2.1 的工程入口，说明实际证明范围、阅读顺序和复现方法。详细的“论文公式 → Lean 命题 → 证明步骤”见 [中文阅读指南](docs/v0.2.1_reading_guide.md)，验证记录见 [PROGRESS.md](PROGRESS.md)。

本阶段代码已通过默认构建与独立公理审计。这里只处理固定空间点的系数代数；$p,r$ 可以是变系数场在该点的取值，未要求它们在整个空间恒定。$C_P>0$ 是给定参数，本阶段没有证明矩形 Poincaré 不等式。

## 论文公式与已实现内容

本阶段新增 12 个定义、32 条定理：系数模块 5 个定义、17 条定理；权重模块 7 个定义、15 条定理。名称位于 `LeanPML.PML`。

| V7 来源 | 定义与主要结果 | 文件 |
|---|---|---|
| 第 1 节、(5.2) | $a=p+r,b=pr,A=\epsilon+2\kappa,K=8\mu AC_P^2$；$A,K,c_*>0$ | [Coefficients.lean](LeanPML/PML/Coefficients.lean) |
| (5.2)–(5.3) | `threshold` 定义精确 $c_*$；`le_threshold_iff_explicit` 证明双向等价 | 同上 |
| (5.4) 及其后说明 | $a,b\ge0$，$a=0\iff p=r=0$，$a\le c/2$，$b\le a^2/4$、$b\le c^2/16$、$ac-b\ge0$，$c\tau$ 界及 $KS^2\le1/16$ | 同上 |
| (5.5) | `energyWeightX/Y`：零区为 0，正区下界为 $3/2$ | [Weights.lean](LeanPML/PML/Weights.lean) |
| (7.2) 的分式系数 | `dissipationPlus/Minus` 非负且有显式上界，不依赖吸收正下界 | 同上 |
| §9.2、(9.2) 前 | `thetaX/Y`：零区各取 $1/2$，全物理范围 $0\le\theta_i\le1$、和为 1 | 同上 |
| 由 (5.5) 后“可能无界”说明构造 | 趋零族 `vanishingAbsorption`、精确权重计算及 `energyWeights_unbounded` | 同上 |

正参数及 $c>0$ 下，已经证明

$$
c\le c_* \quad\Longleftrightarrow\quad
c^2K\le1\ \land\ 8cAK\le\kappa\tau\ \land\ 8cA\tau\le\kappa,
$$

其中

$$
c_*=\min\left\{\frac1{\sqrt K},\frac{\kappa\tau}{8AK},
                       \frac{\kappa}{8A\tau}\right\}.
$$

后续代数可以使用右侧显式不等式，再通过已证等价连接论文条件。没有把这些待证结论放进参数结构。每条局部引理列出实际需要的假设；例如先由幅度条件得到 $a\le c/2$，再把这个已证结论传给 $ac-b\ge0$ 的引理。

## 三类权重为什么分开

设 $s,t\ge0$、$a=s+t>0$。由适当的幅度条件，已证明

$$
0\le\frac{s(c+s)}{s+t}\le c+S\le\frac{5c}{4},\qquad
0\le\frac{s(c-s)}{s+t}\le c.
$$

前式用于 (7.2) 的 $\sigma_i$ 系数，后式取 $s=\sigma_j,t=\sigma_i$。它们有分子中的吸收因子抵消小分母影响。能量权重则不同：固定 $c>0$，取

$$
p_n=\frac{c}{n+4},\quad r_n=0,\quad S=\frac c4,
$$

Lean 证明了 $0<p_n\le c/4$、趋零的 $\delta$–$N$ 命题，以及

$$
w_x=n+4,\qquad w_y=n+3,\qquad
\forall M\in\mathbb R,\ \exists n\in\mathbb N:\ M<w_x\ \land\ M<w_y.
$$

所以这个合乎幅度条件的族没有统一有限能量权重上界。这不表示每个吸收场都无界。若另固定满足材料条件的正 $c$，同一族仍成立。

零区 $a=0$ 必须单独处理：

- $w_x=w_y=0$ 是能量辅助权重的延拓，不能套用正区 $3/2$ 下界。
- $\theta_x=\theta_y=1/2$ 保持分配和为 1，与 $w$ 和 V6 零延拓比值不同。
- V7 (7.2) 在零区仍有 $c|\nabla v|^2$；分式在零处分配任何总函数值，都不能替代或删除这一独立项。本阶段尚未证明完整空间耗散恒等式。

四种吸收分支均有调用一般定理的正式实例。权重实例取 $c=4,S=1$，$(p,r)$ 为 $(0,0),(1,0),(0,1),(1,1)$；它们只验证相应幅度与权重性质。材料证书另取 $\epsilon=\kappa=\tau=\mu=C_P=1,c=1/576$，调用双向等价定理精确验证小量条件，不宣称 $C_P=1$ 已连接某个矩形域。

## 从哪三个声明开始读

1. `absorptionSum_eq_zero_iff`：从非负假设理解为什么“和为零”推出两个吸收都为零。
2. `energyWeights_lower_bound`：看幅度估计、正分母证据和除法不等式怎样配合。
3. `le_threshold_iff_explicit`：先回看辅助引理 `le_inv_sqrt_iff`，再看三项最小值如何保留双向逻辑。

对应中文推导、每项假设的用途和关键 mathlib 源码位置都在 [阅读指南](docs/v0.2.1_reading_guide.md)。随后读 `theta_partition`、耗散界、四分支实例及无界族，最后查看 [正式入口](LeanPML.lean)、[Audit](Audit.lean) 和进度记录。

在 VS Code 打开整个工程，用 `Cmd+Shift+P` 运行 `Lean 4: InfoView: Display Goal`。把光标移到 `by_cases`、`have`、`rw`、`apply`、`calc` 前后，查看上下文和 `⊢` 后的目标；悬停看类型，F12 查看定义。证明代码均有中文批注，指南引用实际声明，不要求插入无法编译的示意证明。

## 固定环境与复现

| 项目 | 固定值 |
|---|---|
| Lean | `leanprover/lean4:v4.31.0`，提交 `68218e876d2a38b1985b8590fff244a83c321783` |
| Lake | `5.0.0-src+68218e8` |
| mathlib | `v4.31.0`，提交 `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` |
| 配置 | [lean-toolchain](lean-toolchain)、[lakefile.toml](lakefile.toml)、[lake-manifest.json](lake-manifest.json) |

本轮未更新依赖、全局默认工具链或 Lake 包元数据版本 `0.0.3`。该包版本与研究阶段 v0.2.1 分开记录。

~~~sh
cd '/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML'
python3 scripts/run_logged.py --stage v0.2.1 lake_build lake build
python3 scripts/run_logged.py --stage v0.2.1 axioms_audit lake env lean Audit.lean
~~~

记录器在 `logs/v0.2.1/` 按新时间戳保留完整输出及包含命令、工作目录、退出码的 JSON，不覆盖历史。也可直接执行 `lake build`、`lake env lean Audit.lean`。

实际 [最终默认构建](logs/v0.2.1/20261010T164214_705177_lake_build_final.log) 和 [独立公理审计](logs/v0.2.1/20261010T164229_853015_axioms_audit.log) 均退出 0。默认目标 `LeanPML`、`Audit` 覆盖全部 8 个正式模块；旧 59 条与新增 32 条定理合计 91 条全部审计。公理输出只有 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx` 或自定义占位公理。失败及修复过程保存在本阶段日志和 PROGRESS 中。

新增正式文件时，接入 `LeanPML.lean` 的导入链，并在 `Audit.lean` 增加 `#print axioms 完整定理名`，然后实际构建、审计、记录。Lean 检查的是声明中准确写出的命题，仍需结合来源、假设和范围阅读。

## 阶段边界与下一步

[T09](docs/theorem_inventory.md) 的点态参数代数已实现，$C_P$ 的空间解释仍由后续 T08 兑现。[T10](docs/theorem_inventory.md) 只完成分支权重及系数代数，没有整体标记完成：可测性、加权空间、等价类、完备性和 $L_w^2\hookrightarrow L^2$ 嵌入尚未实现。

同样没有新增 PDE 能量恒等式、Green/PEC、一般解的存在唯一性或完整二维 PML 定理。既有模型合同、路线图、旧证明和历史日志均保留；v0.1.3 学习内容见 [上一阶段 README 原文](logs/v0.2.1/before_README.md)。

下一阶段 **v0.2.2 尚未开始**：入口 `PML/LocalElectric.lean`、`PML/LocalDebye.lean`，对应 V7 (7.3)、(7.4)、(8.1)–(8.2)，分别完成电块与 Debye 块的代数恒等式、约束消元和真实时间路径求导。本轮没有创建这些模块。
