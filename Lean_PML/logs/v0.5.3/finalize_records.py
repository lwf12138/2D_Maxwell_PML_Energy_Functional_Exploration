"""v0.5 交接记录。只追加历史/更新当前说明，不改数学源码或受保护文件。"""
from pathlib import Path
import hashlib
import json
from datetime import datetime

ROOT = Path(__file__).resolve().parents[2]
LOG = ROOT / 'logs/v0.5.3'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def write_json(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')

def append_once(path, title, content):
    old = path.read_text()
    if title not in old:
        path.write_text(old.rstrip() + '\n\n---\n\n' + title + '\n\n' + content.strip() + '\n')

stages = [json.loads((ROOT / f'logs/v0.5.{i}/acceptance.json').read_text()) for i in (1, 2, 3)]
assert all(s['status'] == 'passed' and s['build_exit_code'] == s['audit_exit_code'] == 0 for s in stages)
assert all(sha(ROOT / path) == digest for path, digest in stages[-1]['sources'].items())

# 八页已由主代理逐张打开 Poppler 渲染图检查；这里记录已实际观察的结果。
render = json.loads((LOG / 'pdf/render_record.json').read_text())
result = json.loads((LOG / 'pdf/annotation_result.json').read_text())
page_notes = {
    5: '增长场旁注位于页首空白，完整场与不兼容范围清楚；正文、旧标记未遮挡。',
    8: '数据子族旁注明确初始八式及非存在性；未把整个一般数据类标成完成。',
    10: '页首保守常数/强正则限定清晰；历史标记较多但本轮文本与原正文不相交。',
    11: '仅补具体 Green 使用说明，没有重复红勾；四边公式与旧批注保持。',
    12: '新两层能量律限定可见，原(7.6)–(7.8)及历史标记未遮挡。',
    14: '只追加(9.5)–(9.7)具体总装说明；历史待完成标记保留并限定，不重复打勾。',
    15: 'C∞替代剖面与保守参数说明清楚；原(10.1)/(10.2)未被冒充逐字核验。',
    16: '§11.3非零静态解说明明确，未误指§11.2编号(11.1)，没有遮挡公式。',
}
visual = {
    'status': 'passed', 'reviewer': 'root 主代理逐页查看实际渲染图',
    'time': datetime.now().astimezone().isoformat(), 'pages': [],
    'pdf_sha256': result['sha256_after'], 'dpi': render['dpi'],
    'checks': ['红勾可见', '中文无方框', '范围可读', '无裁切', '不遮挡正文或旧批注', '定位与证据账本一致'],
}
for page, file in zip(render['rendered_pages'], render['files']):
    visual['pages'].append({'page': page, 'printed_page': page, 'image': str(Path(file).relative_to(ROOT)),
                            'image_sha256': sha(Path(file)), 'observation': page_notes[page], 'status': 'passed'})
write_json(LOG / 'pdf/visual_review.json', visual)
result['visual_review'] = 'passed'
result['visual_review_record'] = 'logs/v0.5.3/pdf/visual_review.json'
write_json(LOG / 'pdf/annotation_result.json', result)

readme_intro = r'''# LeanPML：光滑兼容解类的全域先验能量定理

用途：从原八变量方程读到真实 L² 两层能量、耗散和有限区间单调性。**v0.5.1、v0.5.2、v0.5.3 已分别验收，整个 v0.5 完成。** 下方保留 v0.4 原说明作为历史；其中“本轮/下一阶段”指当时，不代表当前状态。准确命题和全部输入见 [光滑定理报告](reports/smooth_theorem.md)，历史见 [PROGRESS](PROGRESS.md)。本轮止于 v0.5，没有实施 v1.0。

## 先读三条声明

都在 [MainSmoothRectangle.lean](LeanPML/PML/MainSmoothRectangle.lean)，命名空间为 `LeanPML.PML.SmoothRectangle`。

1. `SmoothCompatibleSolution`：逐个展开输入字段。它接收原八变量、原方程、区域吸收界、PEC、初始兼容和明确的强正则性；不接收现成能量问题或目标估计。
2. `SmoothCompatibleSolution.energy_law_and_closure`：从实际原模型总装得到真实 `HasDerivAt` 和定量耗散下界。比较导数等式、耗散符号与剩余预算三个结论。
3. `main_energy_estimate_smoothRectangle`：把图范数平方界、闭区间单调性、实际 FTC 积分平衡和输入原 E/H/P 控制汇总为结论包。

接着读 [FullDomainProfile](LeanPML/Examples/FullDomainProfile.lean) → [CompatibleData](LeanPML/Examples/CompatibleData.lean) → [StaticMode](LeanPML/Examples/StaticMode.lean) → [UnrestrictedData](LeanPML/PML/Obstructions/UnrestrictedData.lean)。辅助 `SmoothBump`、`PathHelpers` 服务于真实光滑函数、普通/加权路径的成员与导数；`DegenerateBranches.four_branches_main` 检查四种吸收接口。

## 当前具体定理证明什么

在整个非退化矩形上，原方程只要求在 $(0,T)\times\Omega$ 成立；PEC、连续性和静态条件覆盖 $[0,T]$。区域系数入口只限制闭坐标区间内的原 $p,r$；内部截回代表与原系数域内及 a.e. 一致，能量/耗散已接回原系数的合法空间积分。

$$\frac{N_0^2+KN_1^2}{4}\le\mathcal E_7\le N_0^2+KN_1^2,\qquad
\mathcal E_7'=-\mathcal D_7,$$

$$\mathcal D_7\ge\frac{\mathcal S_0+K\mathcal S_1}{2}
+\frac{\mu\tau}{4\kappa}(\|P_t\|_2^2+K\|P_{tt}\|_2^2)\ge0.$$

由此得到 `AntitoneOn`、$0\le\mathcal E_7(t)\le\mathcal E_7(0)$，以及

$$\mathcal E_7(t_2)+\int_{t_1}^{t_2}\mathcal D_7(s)\,ds=\mathcal E_7(t_1)
\quad(0\le t_1\le t_2\le T).$$

(6.10) 控制的是输入原场的实际 L² 范数，代码用 `MemLp.toLp` 与实际历史/磁重构证明对应；不是仅给任意重构坐标一个名字。相同时刻、端点和 $T=0$ 均包含；退化时保留初始导数层兼容，不能从空的内部方程推出它。

这仍是给定解的先验估计。联合 C∞ 技术延拓、C(K) 一致范数路径和实际加权成员/可微性是强于 V7 (6.6) 的输入，不是由论文弱正则性自动推出。无界权重没有被当成普通 L² 有界乘子；零吸收区仍保留普通场与 $c|\nabla v|^2$。没有新增吸收正下界、磁场约束或内部边界条件。

## 参数与三个非平凡检验

采用已证明的 $C_P=2L_x$，不是论文最优 π 常数。实例在 $(-1,1)^2$ 上使用

$$\epsilon=\kappa=\tau=\mu=1,\quad C_P=4,\quad A=3,\quad K=384,
\quad c=1/16384,\quad S=1/65536.$$

参数调用 `ParameterCertificate` 的精确证书。$p(x)=S\,\mathrm{smoothTransition}(4x^2-1)$、$r(y)$ 同式是真正 C∞ 替代剖面：物理区为零，四边单向吸收、四角双向吸收，域内幅度界由构造证明；没有冒充原(10.2)分段幂函数。

- 非零物理区紧支初值证明五兼容、初始八式、真实一阶导数、迹及有限正图平方。方便计算的时间延拓只在 $t=0$ 核验方程，**不是该初值的区间解存在证明**。
- 静态例实际满足八式及全部输入，并调用最终定理；非零正能量恒定、耗散为零。加权有限性来自实例紧支落在 $p=S$ 平台，$w_y=3$，不是主定理新增全域下界。
- 任意八变量初值增长例是实际全未来场 $H=t\nabla\psi,Q=\mu\nabla\psi$；八式、PEC、可积性与磁 L² 的 $t^2$ 增长均已证。它违反磁辅助初始兼容；只否定固定正磁控制、有限初能量和全未来单调同时成立的能量，不否定所有能量。

## InfoView、F12 与复现

VS Code 打开整个工程文件夹，光标依次放在 `by`、具名 `have`、`calc`、`rw` 后查看 Lean InfoView 的假设和目标。F12 从主定理进入 `problem`，再进入 `originalRegionalFiniteIntervalProblem`，可看到 Green/Poincaré 和原方程兼容如何被真正填入。导入过期时先构建，再执行 **Lean 4: Restart File**。

固定依赖中的关键出处：`Real.smoothTransition` 在 `Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`；`expNegInvGlue` 同样在 `Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`；混合导数对称性在 `Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`；FTC `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` 在 `Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`。文件均位于 `.lake/packages/mathlib/` 下，F12 可查准确使用点。

```bash
cd '/Users/wcli/Desktop/资料/graduate_student/博五/further_PML/2D_Maxwell_PML_Energy_Functional_Exploration/Lean_PML'
lake build
lake env lean Audit.lean
```

分别保存阶段日志可运行：

```bash
for stage in v0.5.1 v0.5.2 v0.5.3; do
  python3 scripts/run_logged.py --stage "$stage" lake_build lake build
  python3 scripts/run_logged.py --stage "$stage" axioms_audit lake env lean Audit.lean
done
```

| 阶段 | 验收 | 本轮完整构建 / 独立审计 | 审计声明数（含历史） |
|---|---|---|---|
| v0.5.1 | 通过 | [构建](logs/v0.5.1/20261014T005346_311276_lake_build.log) / [审计](logs/v0.5.1/20261014T005434_779198_axioms_audit.log) | 619 |
| v0.5.2 | 通过 | [构建](logs/v0.5.2/20261014T011030_802569_lake_build.log) / [审计](logs/v0.5.2/20261014T011311_263210_axioms_audit.log) | 683 |
| v0.5.3 | 通过；覆盖前三阶段当前源码 | [构建](logs/v0.5.3/20261014T011533_485975_lake_build.log) / [审计](logs/v0.5.3/20261014T011752_801259_axioms_audit.log) | 740 |

审计只有 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx` 或自定义占位公理。结构字段另做语义检查，不能用公理审计代替范围检查。失败日志、命令、退出码和源码哈希保留。最终整体验收见 [overall_acceptance.json](logs/v0.5.3/overall_acceptance.json)。Lean v4.31.0 和 mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` 未变。

## PDF 与下一阶段

指定副本保留18页和200条旧批注；第5/8/10/12/15/16页新增6个带范围红勾，第11/14页只补说明。详见 [PDF账本](docs/pdf_formalization_marks.md)、[逐页视觉检查](logs/v0.5.3/pdf/visual_review.json)。原论文、模型合同、路线图和历史日志保持。路线图旧“待实现”是冻结文本，当前实现状态以源码和本轮证据为准。

下一步仅交接 **v1.0.1**：核验并构造真实弱导数/H₀¹/H(div) 与退化加权图空间，连接已完成的光滑版本；之后再做弱 Green、W¹,∞、(5.7)/(5.8) 加权传播和提升规范唯一性。精确 π 常数、一般解存在唯一性、严格/指数衰减均未被本轮证明。本轮不继续实施。

---

# 以下为 v0.4 及对齐修复时的完整 README 历史

以下“本轮/下一阶段/尚未实施”保持当时含义，当前状态见上文与本轮验收。

'''
old_readme = (ROOT / 'README.md').read_text()
if not old_readme.startswith('# LeanPML：光滑兼容解类的全域先验能量定理'):
    (ROOT / 'README.md').write_text(readme_intro + old_readme)

progress = r'''# 2026-10-14：v0.5.1–v0.5.3 分别通过，v0.5 整体完成

用途：记录当前可编译源码的实际数学范围、阶段验收与未覆盖事项。以下所有旧进度原样保留；旧“进行中/待实现”是阶段内历史。

| 子阶段 | 已验收内容 | 独立证据 |
|---|---|---|
| v0.5.1 | 区域原八式→实际历史/两层→具体光滑先验定理；(6.7)–(6.10)，真实原场 L² 控制、原p/r积分、FTC平衡 | [验收](logs/v0.5.1/acceptance.json)，619项审计 |
| v0.5.2 | 已有精确参数证书调用；实际C∞完整剖面、四边四角；非零紧支数据、五初始兼容、原式初始导数、迹、普通/加权成员与有限正图平方 | [验收](logs/v0.5.2/acceptance.json)，683项审计 |
| v0.5.3 | 四退化接口；非零兼容静态解调用主定理、E正恒定/D零；完整紧支增长场、八式/PEC/真实L²增长与全未来受限障碍；指定单层失败回归 | [验收](logs/v0.5.3/acceptance.json)，740项审计 |

最终全工程构建和审计重新覆盖三个阶段的当前源码；所有成功日志链接见 [README](README.md)。失败过程没有删除，旧模块证明没有无关重构。报告见 [smooth_theorem.md](reports/smooth_theorem.md)，最终保护/导入/哈希/PDF检查见 [整体验收](logs/v0.5.3/overall_acceptance.json)。

正式入口 `SmoothCompatibleSolution` 只接收原方程、参数/区域界、边界、初值和强正则性；`problem` 在证明体内构造。具体 Green、保守 Poincaré、混合交换、全时段兼容和能量输出没有隐藏为输入。原系数幅度只在闭坐标区间，PDE仅内部时空，零吸收区普通耗散保留。

当前 $C_P=2L_x$。单位矩形实例 $C_P=4,A=3,K=384,c=1/16384,S=1/65536$；C∞剖面是替代(10.2)，不是原精确π配置。一般主定理保留联合C∞、C(K)和实际加权路径作为强正则性输入；**具体数据、静态与增长实例所需的成员/导数则由构造证明**，没有再次假设其目标性质。

非零启动数据只证明初始可容许性，方便时间延拓不是一般区间解。静态与增长例是逐条核验的显式场；增长例不兼容，不适用兼容类主定理。非零静态例说明单调不增允许正的常值能量。单层回归只针对既有候选。

PDF第5/8/10/12/15/16页新增6个范围红勾，第11/14页补具体接口使用说明；200旧批注、页序、可选正文保持。新备份、定位、哈希、Poppler渲染与八页实际视觉验收见 [PDF账本](docs/pdf_formalization_marks.md)和[检查](logs/v0.5.3/pdf/visual_review.json)。

来源、合同、范围、路线图与锁定配置哈希未变。路线图冻结状态仍写“待实现”，本轮只在现有清单追加当前范围，不覆盖旧描述。下一阶段为 v1.0.1 的弱空间/退化加权范围接入；未实施 v1.0，没有提交、推送或依赖更新。精确π常数、传播、提升规范、一般存在唯一性仍未完成。

---

# 以下为阶段内及此前历史

'''
old_progress = (ROOT / 'PROGRESS.md').read_text()
if not old_progress.startswith('# 2026-10-14：v0.5.1–v0.5.3 分别通过'):
    (ROOT / 'PROGRESS.md').write_text(progress + old_progress)

report_path = ROOT / 'reports/smooth_theorem.md'
report = report_path.read_text()
report = report.replace('本文对应 v0.5.1；v0.5.2 的数据证书与 v0.5.3 的显式状态另在下方登记',
                        '本文对应已经分别验收的 v0.5.1–v0.5.3；数据证书与显式状态在下方登记')
report = report.replace('v0.5.2、v0.5.3的实际声明、实例调用和成功验证证据在完成后逐项登记。',
                        'v0.5.2、v0.5.3的实际声明、实例调用和成功验证证据已在下方逐项登记。')
report = report.replace('本文件的验证状态以 `logs/v0.5.1/acceptance.json` 为准；后续阶段的最终全工程构建须重新覆盖本模块，不能仅引用旧检查。',
                        '三个阶段分别保存 acceptance.json；最终 v0.5.3 全工程构建与审计已重新覆盖本模块及所有实例。整体验收以 [overall_acceptance.json](../logs/v0.5.3/overall_acceptance.json) 为准。')
report = report.replace('后续阶段尚未据此登记整体完成。',
                        '这是本阶段当时的证据；最终当前版本覆盖与后两个阶段的证据见文末。')
report = report.replace('`physical_data_certificate` 汇总实际数据、初始方程、兼容、迹与正图平方。',
                        '`physical_data_certificate` 汇总实际数据、初始方程、兼容、PEC与正图平方；`physical_initial_traces` 另明确列出 u₀/E₀/E_t₀ 三迹。')
report = report.replace('实际E/P时间连续，实际积分历史联合光滑', '八个原场沿时间连续、实际u积分历史联合光滑')
report = report.replace('的真实 L² 成员和加权路径连续可微', '的真实 L² 成员；前两层加权曲线连续可微')
report = report.replace('| `F`、`u0/q0` |', '| `T_nonneg` | 有限区间T≥0；含T=0与闭区间比较 | 原时间范围 |\n| `F`、`u0/q0` |')
report_path.write_text(report)
append_once(report_path, '## 三阶段最终验证与交接', r'''
| 阶段 | 验收 | 完整构建 / 独立审计 | 含历史声明数 |
|---|---|---|---|
| v0.5.1 | 通过 | [构建](../logs/v0.5.1/20261014T005346_311276_lake_build.log) / [审计](../logs/v0.5.1/20261014T005434_779198_axioms_audit.log) | 619 |
| v0.5.2 | 通过 | [构建](../logs/v0.5.2/20261014T011030_802569_lake_build.log) / [审计](../logs/v0.5.2/20261014T011311_263210_axioms_audit.log) | 683 |
| v0.5.3 | 通过；覆盖前两阶段当前源码 | [构建](../logs/v0.5.3/20261014T011533_485975_lake_build.log) / [审计](../logs/v0.5.3/20261014T011752_801259_axioms_audit.log) | 740 |

完整类型检查与独立语义审查检查了结构字段，而非仅看 theorem 表面参数。三阶段无 sorryAx，只有标准基础公理；全部历史审计保留。模板验收中的 regularity_inputs 列表描述一般主定理范围；[范围补充](../logs/v0.5.3/scope_supplement.json) 明确区分具体实例已经证明的正则性，不误称它们仍需外传输入。

18页PDF、200旧批注保持，新增6勾和2条说明的范围见[账本](../docs/pdf_formalization_marks.md)。[结构记录](../logs/v0.5.3/pdf/annotation_result.json)和[八页视觉验收](../logs/v0.5.3/pdf/visual_review.json)均通过；定义、输入条件与未证弱范围没有被打为证明完成。

下一步是路线图 v1.0.1：核验固定 mathlib 的真实弱空间及退化权重图空间，连接目前实际 WeightedL2 和光滑矩形版本。弱 Green、一般 W¹,∞、加权传播及提升规范唯一性属于后续阶段；本轮到此交接。
''')

append_once(ROOT / 'docs/source_inventory.md', '## 2026-10-14：v0.5 来源与当前验证追加（保留此前历史）', r'''
本轮入场将当前源码/配置/来源与 v0.4_alignment 记录逐个核对，未发现哈希差异。基线为 [baseline.json](../logs/v0.5.1/baseline.json)。原 V7 md/tex/pdf、proof_audit、合同、scope、路线图和三份锁定配置在三个阶段及最终检查中均未变；仅指定PDF副本加范围批注。

- 主命题：S2 第2/5节及(6.4)、(6.6)–(6.10)、第7–9节；正式实现 `MainSmoothRectangle.lean` 使用具体原模型区域入口，不将普通字段中的目标当假设。
- 参数：复用实际矩形与保守 $C_P=2L_x$ 的 `ParameterCertificate`。S2 (5.1)、§10 的精确π配置不是本轮通过的参数版本；保留旧c=1/128在新K下失败的正式对照。
- 剖面：S2 (10.2) 给有限阶分段幂剖面；本轮 `FullDomainProfile.profile` 用当前固定 mathlib `Real.smoothTransition` 生成 C∞替代实例，明确不同，不修改原文。
- 数据：S2 §5.2类的§11.1启动子族；实际平坦紧支函数由固定 `expNegInvGlue` 构造。普通/加权成员、初始原式和正图平方均已证，但不存在一般解声明。
- 回归：S2 命题2.2、§11.3 的具体显式场，§11.1指定单层候选。全部场方程、导数和实际积分分别验证；不混淆§11.1无编号式与§11.2的(11.1)。

新增分析 API 来自**当前锁定 mathlib**，不是联网教程：`Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`（`Real.smoothTransition`）；`Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`（`expNegInvGlue`）；`Mathlib/Analysis/Calculus/Deriv/Support.lean`（导数支撑）；`Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`（混合导数对称）。读取/补获取现有提交的模块缓存没有改变版本或锁文件。

路线图 v0.5 的状态文字/复选框仍为“待实现”，它是受保护的历史文本，本轮没有修改。当前实现以 [三阶段整体验收](../logs/v0.5.3/overall_acceptance.json)、源码及真实日志为依据；旧日志不充当新源码的证据。
''')

inventory_rows = r'''
本段逐项追加实际声明，原条目的计划名称和旧待实现状态保留历史意义。表中缩写 **M**=`LeanPML.PML.SmoothRectangle`，**S**=`M.SmoothCompatibleSolution`；**C**=`LeanPML.Examples.CompatibleData`，**F**=`LeanPML.Examples.FullDomain`，**O**=`LeanPML.PML.Obstructions`，**St**=`LeanPML.Examples.StaticMode`。完整名称可在正式审计、类型日志和PDF定位计划逐条找到。

| 条目 / 论文范围 | 当前已证明的声明与范围 | 仍未完成或不可扩大 |
|---|---|---|
| T30；(6.7)–(6.10) | `M.main_energy_estimate_smoothRectangle`；`S.energy_graph_bounds`、`energy_law_and_closure`、`energy_antitone`、`energy_integral_balance`；`S.physical_current_bound`、`physical_initial_bound` 控制输入原E/H/P的实际L² | 强光滑版本、保守CP；不是T31完整弱V7、存在唯一或严格衰减 |
| T10–T12、T17–T29 具体接入 | `S.problem` 从原八式/初始条件构造区域问题；`energy_eq_original_integrals` / `dissipation_eq_original_integrals` 及可积性回到原p/r；`second_R_continuous` 给真实P_tt积分正则性 | 一般主定理的普通/加权强正则性仍是输入；这些输入不含目标能量/兼容/Green/Poincaré |
| T32 参数与全域剖面 | `F.regional_threshold` 调用实际CP4证书；`profile_contDiff`、`profile_zero_iff`、`profile_bounds`、`four_sides_nonempty`、`four_corners_nonempty` | 新有理参数及C∞替代剖面，不是原(10.1)/(10.2)逐字验证或最优π证书 |
| T32 非零初始子族 | `C.physical_data_certificate`、`physical_initial_traces`、`initial_derivatives`、`regular`、`initialGraphSquare_formula`、`physical_initial_graph_pos` | 初始八式和图数据合法，不证明这些脉冲初值的区间PDE解存在；不覆盖§5.2所有一般族 |
| T35 非零静态场 | `St.concreteSolution`、`sideField_weighted`、`concrete_integral_balance`、`nonzero_static_regression`：实际八式/PEC/五兼容，非零实际L²，正的常值能量/D零；真实主定理调用 | 支撑上正吸收是实例事实，不是全域条件；未单独宣称原文静态能量标量积分简式已形式化 |
| T33 增长场与量词 | `O.fullProfile_unrestricted_classical`、`_norm_growth`、`_not_compatible`、`_unbounded`、`_no_coercive_antitone_energy`：实际全未来紧支场、8式/PEC、真实积分=t²G，G>0，任意初始历史不能修复磁兼容 | 排除固定正常数统一磁控制+有限初值+全未来单调的能量；不否定所有能量、不适用于兼容类、不是固定有限T反证 |
| T34 指定单层回归 | `O.singleLayer_candidate_failure_regression` 用本轮smallC调用既有负耗散证明 | 只针对指定单层候选；初值上局部/积分正率仍不证明经过启动数据的一般解存在 |
| 退化接口（T30范围） | `LeanPML.Examples.Degenerate.four_branches_main`：同一参数的全零/仅x/仅y/双向；`asymmetric_directions` 核对不对称方向 | 四分支接口使用零路径，不替代T35实际非零解；零区空间耗散未删除 |

T30 在**所选强光滑兼容类**完成；T31、T06传播完整范围、T07提升规范唯一性、T36/T37的Laplace/完美匹配均不升级。$C_P=2L_x$，不是T08原式精确π常数。$T=0$保留初始导数层条件，闭区间结论与内部真实求导分别列明。

三个阶段分别通过 [v0.5.1](../logs/v0.5.1/acceptance.json)、[v0.5.2](../logs/v0.5.2/acceptance.json)、[v0.5.3](../logs/v0.5.3/acceptance.json)；最后构建/740项审计覆盖全部当前模块。完整纸面对应与19输入字段审查见 [报告](../reports/smooth_theorem.md)，总体及保护检查见 [整体验收](../logs/v0.5.3/overall_acceptance.json)。
'''
append_once(ROOT / 'docs/theorem_inventory.md', '## 2026-10-14：v0.5 三阶段正式实现追加', inventory_rows)

append_once(ROOT / 'docs/claim_ledger.md', '## 2026-10-14：v0.5 结论范围升级（不覆盖历史）', inventory_rows + r'''

**假设审查。** `SmoothCompatibleSolution` 的19字段只包含真实对象、材料/区域条件、原方程、初值、边界、强正则性和历史识别。没有现成问题对象、Green/Poincaré、混合交换或全时段兼容作为输入；这些在`problem`构造链中由具体矩形与真实原演化证明。结构型结论包 `SmoothEnergyConclusions` 是输出，不是输入。公理审计之外，完整类型打印、root字段检查与独立审查分别存于 [semantic_review](../logs/v0.5.1/semantic_review.md)、[geometry review](../logs/v0.5.1/semantic_review_geometry.md)、[examples review](../logs/v0.5.3/semantic_review_examples.md)。

一般主定理仍输入联合C∞、C(K)及实际加权成员/路径可微性；静态例则由真实紧支平台证明这些条件，增长例属于不兼容的全未来类。数据证书仅在初始时刻验证原式，不把方便延拓叫PDE解。没有将加权自动传播、弱空间或一般适定性登记完成。
''')

plan = json.loads((LOG / 'pdf/annotation_plan.json').read_text())
pdf_lines = [
    '本轮只修改指定副本；18页与200条旧批注保持，新增8条批注（6个矢量红勾、2条范围说明），最终208条。实际页序与印刷页码均一致。每条标记通过当前正式导入、源码哈希、构建及审计核对后添加。',
    '',
    '| 页序 / 印刷页 | 公式或定位 / 类别 | Lean文件与完整声明 | 已证准确范围、输入及剩余接口 | 本轮旁注 |',
    '|---|---|---|---|---|',
]
for entry in plan['entries']:
    # 表格显示完整名字，不缩略为计划名；每条旁注只登记一次。
    names = '<br>'.join('`' + n + '`' for n in entry['theorems'])
    files = '<br>'.join(f'[{Path(m).name}](../{m})' for m in entry['modules'])
    kind = '✓ 已证结论（具体光滑范围）' if entry['kind'] == 'tick' else '接口使用范围说明；无新勾'
    text = '<br>'.join(entry['draw']['lines'])
    scope = entry['scope'].replace('|', r'\|')
    pdf_lines.append(f"| {entry['page']} / {entry['printed_page']} | {entry['formula']}<br>{kind} | {files}<br>{names} | {scope} | {text} |")
pdf_lines += [
    '',
    '每条均由 [v0.5.3最终完整构建](../logs/v0.5.3/20261014T011533_485975_lake_build.log) 与 [740项审计](../logs/v0.5.3/20261014T011752_801259_axioms_audit.log) 支持，包含前两阶段当前源码。各条源文件哈希和定位矩形见 [annotation_plan.json](../logs/v0.5.3/pdf/annotation_plan.json)。',
    '',
    '已有 v0.3 条件性和 v0.4 光滑标记原样保留。本轮在页首补充其具体接入范围，不删除历史“待完成”文字。定义(5.3)/(6.4)/(6.6)、原(5.1)精确π常数、(5.7)/(5.8)传播、弱范围、规范和存在唯一没有新完成勾；第10节只标“替代实例”。v0.5已完成不等于完整弱V7。单层§11.1既有范围勾保留，没有将指定候选扩大为所有单层能量不存在。',
    '',
    '修改前新备份及哈希：[backup.json](../logs/v0.5.3/pdf/backup.json)；脚本：[annotate_pdf.py](../logs/v0.5.3/pdf/annotate_pdf.py)；定位准备：[prepare_plan.py](../logs/v0.5.3/pdf/prepare_plan.py)；编辑结构记录：[annotation_result.json](../logs/v0.5.3/pdf/annotation_result.json)；渲染：[render_record.json](../logs/v0.5.3/pdf/render_record.json)；八页实际逐张视觉验收：[visual_review.json](../logs/v0.5.3/pdf/visual_review.json)。',
    '',
    f"修改前 SHA256 `{result['sha256_before']}`；最终 `{result['sha256_after']}`。原可选正文、四个页面框、页序和旧批注保持，无正文/批注重叠。标识`LeanPML.v0.5.*`避免再次运行叠加相同标记。",
]
append_once(ROOT / 'docs/pdf_formalization_marks.md', '## 2026-10-14：v0.5 光滑具体定理、数据与范围回归', '\n'.join(pdf_lines))

write_json(LOG / 'scope_supplement.json', {
    'purpose': '解释各阶段 acceptance.json 通用 regularity_inputs 模板，不覆盖真实历史记录',
    'v0.5.1': {'regularity': '一般主定理明确输入强光滑/C(K)/实际加权正则性；其余具体分析接口由已证矩形与原演化填入', 'result': '光滑兼容类给定解全域先验定理'},
    'v0.5.2': {'regularity': '构造证明剖面C∞、初始延拓普通/加权成员和真实导数；没有将这些实例事实假设进证书', 'result': '初始数据可容许性，不是区间解存在'},
    'v0.5.3': {'regularity': '静态实例由具体C∞紧支平台证明普通/加权全部路径条件；增长例证明其原场可导/可积，不属于兼容定理输入', 'result': '实际显式解及全未来限定反例'},
    'pending': ['完整弱空间范围', '精确π常数', '(5.7)/(5.8)加权传播', '提升规范唯一性', '一般存在唯一性'],
})
print('Updated README, PROGRESS, report and four existing ledgers; recorded eight-page visual acceptance.')
