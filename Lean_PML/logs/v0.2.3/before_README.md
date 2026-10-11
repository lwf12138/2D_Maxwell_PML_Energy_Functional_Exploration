# LeanPML：电块与极化块的局部真实求导

用途：作为 v0.2.2 的工程入口，说明 Lean 实际检查了什么、假设从哪里来，以及如何阅读和复现。逐步推导见 [中文阅读指南](docs/v0.2.2_reading_guide.md)，完整阶段记录与历史见 [PROGRESS.md](PROGRESS.md)。

本轮实现 V7 (7.3)、(7.4) 的局部真实时间求导，以及 (8.1) 的约束消元和 (8.2) 的全部系数界。默认构建与独立公理审计均已实际通过。这里的 $a,b$ 是固定空间点的时间不变参数，可以来自空间变系数场；尚未证明空间积分能量或二维 PML 单调性。

## 论文公式与正式声明

两个新模块共 **9 个定义、18 条定理**，命名空间均为 `LeanPML.PML`。

| 来源 | 数学层次与主要声明 | 输入及作用 |
|---|---|---|
| (7.3) | [LocalElectric.lean](LeanPML/PML/LocalElectric.lean)：`electricEnergy`、`electricRemainder`、`electric_rate_identity` | 数值代数，参数可为任意实数；恒等式由真实求导定理调用 |
| (7.3) | `hasDerivAt_electricEnergyAlong` | `HasDerivAt v vDot t` 与 `HasDerivAt (deriv v) vDDot t`；分别绑定一阶和真实二阶导数 |
| (6.1)、(7.4) | [LocalDebye.lean](LeanPML/PML/LocalDebye.lean)：`polar_constraint_derivative`、`polar_shifted_constraint` | 三个函数的真实导数、$z'=R$，及邻域内 $z+\tau R=\kappa v$；推出两个导数约束 |
| (7.4) | `polar_rate_algebra`、`hasDerivAt_polarQuadratic`、`hasDerivAt_polarEnergy` | 先逐项求导 $Q$，再用约束和代数恒等式；只为消分母额外要求 $\kappa\ne0$ |
| (7.4) | `hasDerivAt_polarEnergy_on_Ioo` | 在 $t\in(0,T)$，兼容关系仅需在该开区间成立；不用端点双侧导数或区间外兼容 |
| (8.1) | `polarQuadratic_eq_reduced`、`polarEnergy_eq_reduced` | 单点约束即可代数消元；第二条调用第一条，保留 $1/(2\kappa)$ |
| (8.2) | `polar_coefficients_bounds_of_local_conditions` | 从列明的中间界推导四组系数上下界 |
| (5.2)–(5.4) → (8.2) | `polar_coefficients_bounds_of_threshold` | 从原材料正性、$0<c\le c_*$、$0\le p,r\le S\le c/4$，调用 v0.2.1 推出全部中间条件 |
| 正式实例 | `hasDerivAt_electricEnergyAlong_exampleU`、`hasDerivAt_example_polarEnergy` | 复用实际指数路径和导数证据，调用上述一般求导定理 |

对应的求导结论是

$$
F_e'=\epsilon(v_{tt}+av_t+bv)(v_t+cv)-D_e,\qquad
F_D'=(R_t+aR+bz)(v_t+cv)-D_D.
$$

$F_e$ 包含 $\epsilon/2$，$F_D=Q/(2\kappa)$；完整 (6.2) 中这两部分还须乘 $\mu$ 并作空间积分。$D_e,D_D$ 是恒等式余项，含 $a-c$ 等符号不定系数，本轮没有宣称各块非负或单调。

(8.2) 保留论文精确常数：

$$
\frac34\le A_R\le\frac54,\quad
0\le1-a\tau-b\tau^2\le1,\quad
0\le G\le\frac{37}{64}c^2,\quad
0\le b+ac\le\frac9{16}c^2.
$$

$A_R$ 与材料常数 $A=\epsilon+2\kappa$ 分开定义。汇总定理没有把这些界当作模型输入，也没有除以 $a,b$，因此保留零吸收、单向吸收与双向吸收。$C_P>0$ 仍是给定参数，矩形 Poincaré 不等式尚待证明。

## 阅读顺序与 InfoView

先读 [阅读指南](docs/v0.2.2_reading_guide.md)，再按顺序阅读这三个声明，并回看它们上方的定义和辅助引理：

1. `hasDerivAt_electricEnergyAlong`：看平方、交叉项、常数如何逐项求导，最后才调用代数恒等式。
2. `polar_constraint_derivative`：看为什么“邻域相等 + 真实求导 + 导数唯一性”才允许对兼容关系求导。
3. `polar_coefficients_bounds_of_threshold`：看原始假设如何经 v0.2.1 和局部系数引理得到 (8.2)。

接着读 `hasDerivAt_polarEnergy`、约束消元和两条路径实例，最后查看 [正式入口](LeanPML.lean)、[Audit](Audit.lean) 与 [进度记录](PROGRESS.md)。旧阶段说明保留在 [v0.2.1 指南](docs/v0.2.1_reading_guide.md) 和 [上一版 README](logs/v0.2.2/before_README.md)。

在 VS Code 中打开整个工程目录。打开 Lean 文件后，使用命令面板的 `Lean 4: InfoView: Display Goal`；将光标放到 `have`、`calc`、`apply` 或 `rw` 前后，比较上下文与 `⊢` 后的目标。悬停查看类型，F12 跳转定义。若新导入仍报旧错误，先在工程根目录运行 `lake build`，再用 `Lean 4: Server: Restart File` 重启当前文件的检查。无需更新依赖。

## 非零路径验证了什么

沿用 v0.1.3 的实际函数，取 $\kappa=\tau=1$：

$$
v(t)=\frac{1-e^{-2t}}2,\qquad R(t)=-e^{-2t},\qquad
z(t)=\frac{1+e^{-2t}}2.
$$

已有导数证据给出 $v_t=e^{-2t}$、$R_t=2e^{-2t}$、$z_t=R$。本轮证明整个导数函数 `deriv exampleU = Debye.exampleE`，据此再次求导；并证明邻域兼容，调用一般极化块定理。$R(0)=-1$ 的既有实例和本轮 $v_t(0)=1$ 排除了只验证零路径的情况。此例是局部时间路径，不是完整二维 PDE 解。

这里的 $F_D$ 与 v0.1.2 的教学能量 $(\epsilon E^2+P^2/\kappa)/2$ 不同；本轮没有输入教学方程 $\epsilon E'=-P'$。

## 固定环境与复现

| 项目 | 固定值 |
|---|---|
| Lean | `leanprover/lean4:v4.31.0`，提交 `68218e876d2a38b1985b8590fff244a83c321783` |
| Lake | `5.0.0-src+68218e8` |
| mathlib | `v4.31.0`，提交 `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` |
| 配置 | [lean-toolchain](lean-toolchain)、[lakefile.toml](lakefile.toml)、[lake-manifest.json](lake-manifest.json) |

本轮未更新依赖、全局工具链或 Lake 包元数据版本 `0.0.3`；研究阶段单独记录。

~~~sh
cd '/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML'
python3 scripts/run_logged.py --stage v0.2.2 lake_build lake build
python3 scripts/run_logged.py --stage v0.2.2 axioms_audit lake env lean Audit.lean
~~~

也可直接执行 `lake build` 和 `lake env lean Audit.lean`。记录器按新时间戳保存完整输出和含命令、工作目录、退出码的 JSON，不覆盖旧日志。

实际 [默认构建](logs/v0.2.2/20261010T185648_883655_lake_build.log) 与 [独立审计](logs/v0.2.2/20261010T185707_307274_axioms_audit.log) 均退出 0；构建覆盖全部 10 个正式模块及两个入口。审计保留旧 91 条并新增 18 条，共 109 条；输出仅含 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx`。这些分别是命题外延性、经典选择、商类型基础依赖，不是本项目自设的证明占位公理。真实失败及修复记录见 PROGRESS。

新增正式文件时，要接入 `LeanPML.lean` 的导入链，在 `Audit.lean` 增加 `#print axioms 完整定理名`，再实际构建并审计。仅把文件放进目录不等于完成验证。

## 当前范围与下一入口

本轮只完成 T13、T14 的固定空间点真实时间版本，以及 T19 的约束消元和系数界；不改历史清单的原记录。空间积分、加权空间、Green/PEC、图范数正定性、两层耗散闭合和原八变量与场层 primitive 对应仍待完成。

下一步仅为 **v0.2.3：空间块与退化区**，计划入口 `PML/LocalSpatial.lean`：核验 (7.1)–(7.2)，分开 $a>0$ 与 $a=0$，保留零区 $c|\nabla v|^2$ 和局部通量。实际时间—空间微分交换仍属后续空间接口。本轮没有创建该模块。
