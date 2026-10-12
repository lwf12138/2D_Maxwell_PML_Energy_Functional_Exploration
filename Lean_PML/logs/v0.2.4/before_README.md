# LeanPML：空间块与退化零区

用途：说明 v0.2.3 实际形式化的结论、阅读顺序、真实验证和 PDF 红勾的范围。详细推导见 [中文阅读指南](docs/v0.2.3_reading_guide.md)，阶段记录与原有历史见 [PROGRESS.md](PROGRESS.md)，逐项 PDF 证据见 [标注账本](docs/pdf_formalization_marks.md)。

本阶段完成 V7 (7.1) 正吸收与零吸收分支的**真实时间路径求导**，以及 (7.2) **点态耗散密度非负**。默认构建、独立公理审计、四区实例和非零路径均已通过。系数可以来自空间变系数场在某点的值，只在时间上固定；这里还没有实际空间梯度或完整二维 PDE 结论。

## 实现与假设

新增 [LocalSpatial.lean](LeanPML/PML/LocalSpatial.lean)，命名空间 `LeanPML.PML`，共 **6 个定义、25 条定理**。4 个核心定义描述单/双方向能量与分支耗散，2 个定义用于非零路径实例。

| 来源与层次 | 主要定理 | 输入与结论 |
|---|---|---|
| (7.1)，代数 | `spatial_weight_balance`、`spatial_rate_identity` | $a=\sigma_i+\sigma_j>0$；证明 $\sigma_j+aw_i=c$ 及展开恒等式，供真实求导调用 |
| §7.1，真实时间 | `hasDerivAt_spatialAuxiliary` | 从实际 $h'=V,l'=V+\sigma_jh-\sigma_i l$ 推出 $(l-h)'=\sigma_jh-\sigma_i l$ |
| (7.1)，正区求导 | `hasDerivAt_spatialEnergy_pos` | 同上两份 `HasDerivAt` 和 $a>0$；逐项平方求导后调用代数层 |
| §5.2 与零区兼容 | `zeroSpatial_compatibility_preserved` | 非负吸收、$a=0$、闭区间连续、内部真实演化、初始 $l(0)=h(0)$；推出全区间兼容，含 $T=0$ |
| (7.1) 后未编号公式 | `hasDerivAt_zeroSpatialComponent`、`hasDerivAt_zeroSpatial2D` | 实际 $h_i'=V_i$；保留 $c(h_x^2+h_y^2)$ |
| 两分支接合 | `hasDerivAt_spatialEnergy_zero`、`hasDerivAt_spatialEnergy` | 非负吸收；仅零区要求当前 $l=h$。零分支未对单点等式求导 |
| (7.2)，点态 | `spatialDissipation_nonneg`、`spatialDissipation2D_nonneg` | $c>0$、$0\le p,r\le S\le c/4$；复用已有系数界推出非负，无吸收正下界 |
| 二维时间版本 | `hasDerivAt_spatialEnergy2D` | 四份真实导数证据、非负吸收、条件化零区兼容；分别调用 $(p,r)$、$(r,p)$ |

完整保留的局部等式为

$$
F_{\mathrm{sp}}'
=(V_x+ch_x)l_x+(V_y+ch_y)l_y-D_{\mathrm{sp}}.
$$

正区的单方向密度为

$$
D_{\mathrm{sp},i}
=\frac{\sigma_i(c+\sigma_i)}a l_i^2
+\frac{\sigma_j(c-\sigma_j)}a h_i^2.
$$

零区独立取 $D_{\mathrm{sp},i}=ch_i^2$，没有把分式除零的值当成零区公式。$p=r=0$ 只使 $f=l-h$ 保持初值，必须另有初始兼容才能推出 $f=0$。耦合乘积仍在，所以点态耗散非负不表示这个空间块已经单调。

## 实例与两个方向

代码使用 $c=4,S=1$，实际调用一般非负定理，并核验四类区域：

| $(p,r)$ | 精确二维耗散 |
|---|---|
| $(0,0)$ | $4h_x^2+4h_y^2$ |
| $(1,0)$ | $5l_x^2+3h_y^2$ |
| $(0,1)$ | $3h_x^2+5l_y^2$ |
| $(1,1)$ | $\frac52(l_x^2+l_y^2)+\frac32(h_x^2+h_y^2)$ |

数值只验证局部幅度条件，不宣称对任意材料满足全部 $c_*$ 阈值。两种边层分别核对，避免对称实例掩盖方向错误。

真实正区路径 $h=0,l=e^{-t}$ 满足辅助演化；调用一般求导得 $F_{\mathrm{sp},i}'=-5e^{-2t}$，初始能量 $5/2$。零区两个方向取 $h_i=l_i=t+1$，调用一般二维定理得 $F_{\mathrm{sp}}'=2(t+1)$，初始能量为 1。这些是非零**局部时间路径**，不是完整二维 PDE 解或一般存在性定理。

## 建议阅读与 InfoView

先读 [指南](docs/v0.2.3_reading_guide.md)，再在 [正式代码](LeanPML/PML/LocalSpatial.lean) 中按顺序读：

1. `hasDerivAt_spatialEnergy_pos`：区分函数可导、导数值与代数整理。
2. `zeroSpatial_compatibility_preserved`：区分初值条件与整段时间结论。
3. `hasDerivAt_spatialEnergy2D`：检查方向交换、零区条件和保留下来的耦合项。

随后读四区实例与非零路径，最后看 [正式入口](LeanPML.lean)、[公理审计](Audit.lean) 和 [PDF 账本](docs/pdf_formalization_marks.md)。前一阶段内容见 [v0.2.2 指南](docs/v0.2.2_reading_guide.md)、[原 README 快照](logs/v0.2.3/before_README.md)。

在 VS Code 打开整个工程目录，使用 `Lean 4: InfoView: Display Goal`；把光标放在 `have`、`calc`、`apply`、`rw` 前后，查看上下文与 `⊢` 后的目标。悬停看类型，F12 跳到定义。新增导入未刷新时，先保存并构建，再用 `Lean 4: Server: Restart File`；无需更新依赖。

## 实际验证与复现

| 项目 | 固定值 |
|---|---|
| Lean | `leanprover/lean4:v4.31.0`；提交 `68218e876d2a38b1985b8590fff244a83c321783` |
| Lake | `5.0.0-src+68218e8` |
| mathlib | `v4.31.0`；提交 `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` |

未更新 [工具链](lean-toolchain)、[Lake 配置](lakefile.toml)、[依赖锁](lake-manifest.json) 或全局默认工具链。Lake 包元数据版本仍为 `0.0.3`，研究阶段另记。

~~~sh
cd '/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML'
python3 scripts/run_logged.py --stage v0.2.3 lake_build lake build
python3 scripts/run_logged.py --stage v0.2.3 axioms_audit lake env lean Audit.lean
~~~

也可直接运行 `lake build`、`lake env lean Audit.lean`。日志脚本保存命令、工程目录、退出码和完整 stdout/stderr，新时间戳不会覆盖旧记录。

本次 [默认构建](logs/v0.2.3/20261010T232910_472603_lake_build_retry.log) 与 [独立审计](logs/v0.2.3/20261010T232931_121820_axioms_audit_retry.log) 均退出 0，覆盖 **11 个正式模块、根入口和 Audit**；旧 109 条加新 25 条，共 **134 条定理**。依赖仅有 `propext`、`Classical.choice`、`Quot.sound`，分别是命题外延性、经典选择和商类型的标准基础依赖；没有 `sorryAx` 或本项目自设占位公理。真实失败与修复保留在 [PROGRESS](PROGRESS.md)。

增加正式文件后，要在 `LeanPML.lean` **顶部导入区域**接入模块，并在 `Audit.lean` 添加 `#print axioms 完整定理名`，重新实际构建和审计。文件仅仅存在于目录中不等于被检查。

## PDF 标注与阶段界限

目标副本仍为 18 页，原 PDF/MD/TEX 与旧批注保持不变。本轮另存带时间戳的备份、核对旧 16 处标记，并新增 4 勾：

- 第 8 页未编号零区保持句：“时间保持；须初值 f=0；空间接口待证”。
- 第 10 页 (7.1)：“局部时间版；空间接口待证；积分待完成”。
- 第 10 页后续零区公式：“局部时间版；零区须兼容；空间接口待证”。
- 第 11 页 (7.2) 被积子表达式：“点态非负；空间积分待完成”。

第 1 页增加图例，第 7、8 页说明 (5.3) 是输入、(5.5) 是定义；保留旧勾并限定其代数子结论。第 11 页给旧 (7.3)、(7.4) 旁注补“积分待完成”。页序号与印刷页码相同。所有修改页已渲染检查，公式和已有文字没有被遮挡；详见 [账本](docs/pdf_formalization_marks.md) 与 [视觉核验](logs/v0.2.3/pdf/verification.json)。

T15 只完成局部时间与点态部分。实际场、混合微分交换、可测可积、加权空间求导、空间积分、Green/PEC、Poincaré、图范数、两层闭合、两个磁不变量和原 PDE 对应均未完成；不能给 (6.7)–(6.10)、(7.5)–(7.8)、(9.5)–(9.7) 打整体完成勾。

下一阶段 **v0.2.4「单层能量不是终点」**：整理 (6.2)、(7.7) 的符号不定余项，核验 §11.1 的初始耗散计算，区分该计算与解的存在性，再记录第二层提供的控制。计划入口为 `PML/Obstructions/SingleLayer.lean`、`docs/single_layer_failure.md`；本轮未实现。
