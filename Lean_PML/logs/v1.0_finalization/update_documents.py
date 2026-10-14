from pathlib import Path
import json
root=Path.cwd();folder=root/'logs/v1.0_finalization'
head=r'''# 2026-10-14 v1.0 finalization：一般弱系数已接入 V7 主线

本轮补齐一般分离 W¹,∞ 的连续代表构造、原 (10.2) 幂次剖面全族及精确阈值最小分支。精确 π 常数、实际标量指数记忆核和 Cᵏ 入口直接复用前轮证明。**最终工程、语义与 PDF 验收以 [本轮记录](logs/v1.0_finalization/acceptance.json) 为准**；下方旧“缺口/完成”文字均保留其历史日期含义。

推荐入口是 [MainGeneralWeak.lean](LeanPML/PML/MainGeneralWeak.lean) 的 `main_energy_GeneralWeakCk`（T>0）及 `main_energy_GeneralWeakJet`（T≥0，T=0 初始导数图兼容单列）。它们从原八个实际 L² 场及内部原方程、整个矩形 PEC、原材料/区域弱系数与精确阈值、初始兼容和实际加权成员出发，在证明中构造连续代表和已证空间接口。输出 (6.7)–(6.10)；配套 `auxiliary_current_GeneralWeakCk/Jet` 与 `auxiliary_initial_GeneralWeakJet` 给输入原 Z/Q 和 u/q/φ 的 (8.4)–(8.8) 当前/初值控制。

没有独立的 p/r 连续性输入，没有 Green/Poincaré/目标能量假设；没有正吸收下界、磁法向/散度约束或域内分区边界条件。采用 $C_P^2=(\pi^2/L_x^2+\pi^2/L_y^2)^{-1}$。不是一般解存在唯一性、严格衰减或任意分布解理论。

建议先读三条声明：

1. [一维真实弱导数→积分原函数与代表](LeanPML/Analysis/WeakIntervalRepresentative.lean)：`exists_regional_lipschitz_representative`。
2. [二维分离系数→合法连续代表](LeanPML/PML/WeakAbsorptionRepresentative.lean)：`RawWeakRegionalAbsorption.representatives`。
3. [原系统主入口](LeanPML/PML/MainGeneralWeak.lean)：`OriginalInterval.main_energy_GeneralWeakCk`。

随后看 [原幂次剖面](LeanPML/Examples/OriginalPowerProfile.lean) 与 [新非零静态/四分支调用](LeanPML/Examples/GeneralWeakRegression.lean)。将光标放在 `have`、`calc` 后查看 InfoView 的当前目标；F12 查结构字段与 mathlib 依赖；导入陈旧时执行 **Lean 4: Restart Server**。

```bash
python3 scripts/run_logged.py --stage v1.0_finalization lake_build lake build
python3 scripts/run_logged.py --stage v1.0_finalization axioms_audit lake env lean Audit.lean
```

完整命题、(6.6)/T=0 语义、论文映射及学习说明见 [弱定理报告](reports/weak_theorem.md)；[语义审查](logs/v1.0_finalization/semantic_review.md) 与 [PDF 账本](docs/pdf_formalization_marks.md) 分别记录命题范围和标记。隔离复现不复制项目编译产物，复用固定精确依赖缓存，并非完全无缓存测试。

---

# 以下为此前验收记录（历史原文保留）

'''
p=root/'README.md';p.write_text(head+p.read_text().split('# 以下为此前验收记录（历史原文保留）\n\n',1)[-1])
report=r'''# 2026-10-14 最终入口：一般分离弱系数的 V7 全域先验能量定理

本节是最新范围；以下历次报告原文保留，旧缺口不代表当前状态。实际验收见 [acceptance.json](../logs/v1.0_finalization/acceptance.json)，完整结构审查见 [semantic_review.md](../logs/v1.0_finalization/semantic_review.md)。本轮没有修改旧光滑主定理或原论文/数学合同。

## 准确命题

给定非退化整个矩形 Ω、正材料 ε/κ/τ/μ，真实区域分离 W¹,∞ 系数 p(x)、r(y)，区域内 $0\le p,r\le S\le c/4$，$0<c\le c_*$。使用

$$C_P^2=(\pi^2/L_x^2+\pi^2/L_y^2)^{-1},\quad A=\varepsilon+2\kappa,\quad K=8\mu A C_P^2.$$

原八变量是 L² 商类，E 的 H₀¹ 图表示整个 PEC，$(\mu H_y,-\mu H_x)$ 是真实 H(div) 图；八条方程及 HasDerivAt 仅在 $(0,T)$，空间域是整个 Ω。初值只给五个不变量零、合法 u₀/q₀ 和实际加权辅助成员。原场、E 图、λ 图在闭区间连续。

对 T>0，`V7ClosedCkCore` 输入恰为所用真实空间路径的 $u\in C^2(H_0^1)\cap C^3(L^2)$、$P\in C^2(L^2)$、$\lambda\in C^1(H(\mathrm{div}))$。u 是 Bochner 历史；φ 的所需加权历史与导数从初值和演化构造，未将 OriginalJet 或能量律包成字段。$\lambda_{tt}$ 的 L² 证据由空间关系和实际辅助演化求导产生。`canonicalInterval` 内部规范端点 E/P 导数槽，保留全部原场。

`PML.Weak.OriginalInterval.main_energy_GeneralWeakCk` 证明：

$$\frac{N_0^2+KN_1^2}{4}\le E_7\le N_0^2+KN_1^2,$$
$$E_7'=-D_7,\qquad D_7\ge\frac{\mathcal S_0+K\mathcal S_1}{2}+\frac{\mu\tau}{4\kappa}(\|P_t\|_2^2+K\|P_{tt}\|_2^2)\ge0,$$
$$E_7(t_2)+\int_{t_1}^{t_2}D_7(s)\,ds=E_7(t_1),\quad E_7(t_2)\le E_7(t_1),\quad 0\le E_7(t)\le E_7(0),$$
$$\varepsilon\|E\|_2^2+\mu(\|H_x\|_2^2+\|H_y\|_2^2)+\kappa^{-1}\|P\|_2^2\le(4/\mu)E_7(t)\le(4/\mu)E_7(0).$$

导数/耗散结论在内部，图界、单调比较、实际积分平衡和原变量控制覆盖闭区间。积分可积性是证明结果，不是从单调性冒推。`auxiliary_current_GeneralWeakCk/Jet` 与 `auxiliary_initial_GeneralWeakJet` 给 (8.4)–(8.8)，其中 Z1/Z2/Qx/Qy 正是输入 `OriginalInterval.fields`，常数 8、4、16、8 及 S²/S⁴ 原样保持。

T=0 另用 `main_energy_GeneralWeakJet`：给定合法初始图状态及 `DegenerateJetCompatibility` 的三条初始导数层兼容，得到单点结论。不能从单点 ContDiffOn 或空内部方程决定任意 jet。本轮没有把该语义差别伪装成正则性等价，也不要求端点 PDE；这是实际解限制至单点的合法状态分支。T>0 入口不输入此独立兼容或端点 PDE。

## 本轮论文→声明→最终调用

名称公共前缀 `LeanPML.`，完整类型输出在本轮 `*_type_review.log`。

| 论文/数学步骤 | 声明与文件 | 调用/范围 |
|---|---|---|
| §1 分离 W¹,∞ 的代表 | `Analysis.exists_regional_lipschitz_representative`；`PML.separated_lipschitz_representative_x/y` | 弱测试积分→原函数→Lipschitz；张量测试/Fubini→一维；不输入连续性 |
| 区域幅度、原乘子/权重识别 | `RawWeakRegionalAbsorption.representatives/rawSpatial_ae/weighted_spaces_eq/energy_integral_original` | 构造旧入口，证明商类与积分不变；原剖面可在域外无界 |
| (5.1)、(5.2) | 复用 `Rectangle.weak_sharp_poincare`；新增 `ParameterCertificate.original_threshold_exact` | 精确常数用于 sharpEnergy/K/c*，旧保守实例不改 |
| (5.7)、(5.8) | 复用 `OriginalInterval.scalar_memory_both/scalar_memory_physical_x/y`、`auxiliary_weak_memory_bound` | 实际加权/L² 商类与 Bochner 积分；每个时刻 a.e.，不交换时间与零测集量词 |
| §5.3 | `historical_energy_independent_GeneralWeak`、`twoLayerEnergy_independent_GeneralWeak` | 一般弱系数的代表在证明内构造，已证合法提升唯一性给实际能量选择无关 |
| (6.6) | `V7ClosedCkCore.regularity`→`V7TimeRegularity.flux_second/toOriginalJet` | 输入是真实 Cᵏ；λ_tt 为推导；非解正则性自动传播定理 |
| (6.7)–(6.10) | `OriginalInterval.main_energy_GeneralWeakCk/Jet` | 同一原解的真实两层，内部构造弱 Green 和精确 Poincaré |
| (8.4)–(8.8) | `auxiliary_current_GeneralWeakCk/Jet`、`auxiliary_initial_GeneralWeakJet` | 当前能量及初值能量直接控制输入原变量 |
| (10.1) 最小分支 | `ParameterCertificate.original_threshold_min/original_threshold_exact` | $\min\{\pi/\sqrt{48},\pi^2/1152,1/24\}=\pi^2/1152$；复用 c=1/128,S=1/512 |
| (10.2) | `Examples.OriginalPower.absorption/absorption_branches/represented_profiles` | 全族 m≥2、0<ηx,ηy≤1/512；原剖面等于域内技术扩展，非 C∞ 伪装 |
| 非零与退化调用 | `Examples.GeneralWeak.static_main_call/static_ck_call/static_energy_positive/static_energy_constant/static_dissipation_zero`、`original_profile_main/four_branch_main` | 非零原八式静态解调用；全剖面零解入口证书与非零解存在性分开 |

## 输入表示、依赖与剩余范围

`RawWeakRegionalAbsorption` 采用区域有界可测代表及有界弱导数的测试函数定义，是实际 W¹,∞ 表示。普通系数乘子由有界性构造；能量权重不要求有界或正吸收下界。代表 a.e. 替换保持实际加权闭子空间，并通过等距映射保持恢复；零区没有被删掉。`original_profile_main` 在证明内选择代表并调用主定理；非恒定性由 `representative_nonconstant` 真正验证。

依赖顺序：真实弱导数→分布原函数→连续代表→原式/权重等价搬运→历史与兼容保持→同源路径→已证弱 Green/精确 Poincaré→已有能量代数/闭合→FTC/单调→原变量控制。没有 Green、Poincaré、全时段兼容或目标能量结果作为原解输入。

正反模型对应复用 `WeakPrimitiveSystem` 和 `primitive_to_original_WeakOn`：实际图空间、内部时间、真实导数、μ≠0 和正确极化关系。它不是任意分布解的无正则性等价理论。所有相等按商类/适当 a.e. 理解，不在任意点读取 L² 值。

当前不再保留独立系数连续性、保守常数或指数核识别差异。仍明确区分实际先验正则性与一般存在/传播：不证明一般解存在唯一性、严格/指数衰减、任意幅度或任意八变量初值稳定性。没有以“有限加权范数”代替 C²。T=0 的合法初始 jet 分支如上；不宣称单点函数值决定导数。可选 Laplace、V6 历史、R/D 分支不属于本轮。

## 阅读与复现

先读 `exists_regional_lipschitz_representative` → `RawWeakRegionalAbsorption.representatives` → `main_energy_GeneralWeakCk`。在 InfoView 中跟随具名 have/calc，F12 查结构字段，导入陈旧时 **Lean 4: Restart Server**。

在工程根目录运行：

```bash
python3 scripts/run_logged.py --stage v1.0_finalization lake_build lake build
python3 scripts/run_logged.py --stage v1.0_finalization axioms_audit lake env lean Audit.lean
```

最终核验及源码哈希：[本轮验收](../logs/v1.0_finalization/acceptance.json)；隔离工程复用固定依赖缓存、没有拷贝本项目编译产物：[隔离结果](../logs/v1.0_finalization/isolated_result.json)。真实失败和修复均保留；旧 acceptance/文档哈希不覆盖。PDF 的每个新标记另见 [证据账本](../docs/pdf_formalization_marks.md)。

---

# 以下为此前报告（历史原文保留）

'''
# 清除仅字符串书写中的控制字符；保留 Markdown 数学反斜线。
report=report.replace('\x0b\\lambda','\\lambda')
p=root/'reports/weak_theorem.md';p.write_text(report+p.read_text().split('# 以下为此前报告（历史原文保留）\n\n',1)[-1])
progress=r'''# 2026-10-14 v1.0_finalization 最新记录

本轮真正补齐：一维分布弱导数的积分原函数表示、二维分离弱系数的 Lipschitz 代表、原八式/乘子/加权空间/能量的换代表识别；新一般原系统 Cᵏ 与 jet 入口、当前/初值原辅助变量界及提升选择无关；原 (10.2) 全幂次剖面、阈值 min 精确相等、非恒定代表调用、非零静态主定理调用与四吸收分支。

精确 π Poincaré、标量指数核、(5.8)、λ_tt 推导及旧光滑/弱回归直接复用，没有重写。类型审查区分 T>0 Cᵏ 充分性与 T=0 合法初始 jet，不额外要求端点 PDE。

本轮 [验收总记录](logs/v1.0_finalization/acceptance.json)、[逐项语义检查](logs/v1.0_finalization/semantic_review.md)、[最新准确报告](reports/weak_theorem.md) 优先于下方历史。原源码基线及锁定配置/论文哈希已记录；失败和重试均保留。原阶段日志、论文、数学合同、路线图没有覆盖；没有提交或推送。

---

# 以下为历史进度（保持原文）

'''
p=root/'PROGRESS.md';p.write_text(progress+p.read_text().split('# 以下为历史进度（保持原文）\n\n',1)[-1])
entry=r'''

## 2026-10-14 v1.0_finalization 追加：一般原始弱系数连接闭合

本轮用真实分布弱导数证明积分原函数及 Lipschitz 代表，经二维张量测试/Fubini 接入 `RawWeakRegionalAbsorption`；新 `OriginalInterval.main_energy_GeneralWeakCk/Jet` 不再输入 p/r 连续性。乘子、加权空间、原式、实际能量积分 a.e. 一致由 `WeakCoefficientTransport`、`MainRepresentedWeak` 证明。T>0 的 (6.6) Cᵏ 入口及 T=0 合法初始 jet 分支分别保留语义；没有增加端点 PDE。

原 (10.2) 幂次剖面 m≥2 全族在 `Examples/OriginalPowerProfile.lean` 真实构造，`original_profile_main` 调用新入口；`representative_nonconstant` 验证非恒定代表。`original_threshold_exact` 验证 c*=π²/1152，复用原精确参数。非零静态实际原解在 `Examples/GeneralWeakRegression.lean` 调用新主定理，并有正恒定能量与零耗散。四分支、旧不兼容增长排除和指定单层失败仍进入默认构建。

(6.7)–(6.10)、(8.4)–(8.8)、§5.3 的具体声明及输入/调用表见 [最新报告](../reports/weak_theorem.md)，正式类型和全部证据见 [本轮语义审查](../logs/v1.0_finalization/semantic_review.md) / [总验收](../logs/v1.0_finalization/acceptance.json)。此前“连续代表/精确常数/核识别待实现”保留为对应日期历史，不覆盖旧验收。

不扩张为一般存在唯一性、严格衰减、任意幅度或任意八变量裸 L² 范数等价。ROADMAP 原复选框按用户要求不修改，逐项实际完成状态登记在本轮验收矩阵。
'''
for name in ['docs/theorem_inventory.md','docs/claim_ledger.md','docs/scope.md','docs/source_inventory.md']:
 p=root/name;p.write_text(p.read_text().split('\n\n## 2026-10-14 v1.0_finalization 追加：一般原始弱系数连接闭合',1)[0]+entry)
