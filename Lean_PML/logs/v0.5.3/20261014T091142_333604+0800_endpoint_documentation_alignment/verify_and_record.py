# -*- coding: utf-8 -*-
"""只核对文档修订与历史快照，不调用 Lean/Lake、不重写任何旧验收记录。"""
from pathlib import Path
from datetime import datetime
import difflib
import hashlib
import json
import sys

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[2]
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
before = json.loads((OUT / 'before.json').read_text())
accepted = json.loads((ROOT / 'logs/v0.5.3/overall_acceptance.json').read_text())

source_mismatches = [f for f, h in accepted['formal_sources'].items() if sha(ROOT / f) != h]
assert not source_mismatches, source_mismatches
assert all(sha(ROOT / f) == h for f, h in before['formal_sources_before'].items())
assert all(sha(ROOT / f) == h for f, h in before['protected_before'].items())
assert all(sha(ROOT / f) == h for f, h in before['referenced_acceptance_sha256'].items())
assert sha(Path(accepted['pdf']['target'])) == before['pdf_before'] == accepted['pdf']['sha256']

old_report = (OUT / 'before/reports/smooth_theorem.md').read_text()
new_report = (ROOT / 'reports/smooth_theorem.md').read_text()
old_sentence = '相同时刻与两个端点包含在结论中，不要求端点普通双侧导数。'
new_sentence = ('相同时刻与两个端点包含在结论中。闭区间比较与积分平衡的时间引理不额外要求端点处的 PDE 或能量导数公式；'
                '当前具体定理采用的光滑延拓本身仍包含端点普通双侧可导性：`SmoothTimeJet` 在全时间轴上要求联合光滑性及 `HasDerivAt` 证据。'
                '更弱的时间正则性入口尚未在该具体主定理中实现。\n\n')
assert new_report == old_report.replace(old_sentence, new_sentence, 1)
T0 = '$T=0$时保持单点比较与静态能量估计；其初始导数层兼容明确输入，不能从空的内部条件推出。'
assert T0 in old_report and T0 in new_report
old_progress = (OUT / 'before/PROGRESS.md').read_text()
new_progress = (ROOT / 'PROGRESS.md').read_text()
inserted_line = next(line for line in new_progress.splitlines() if line.startswith('文档对齐（2026-10-14）：'))
assert new_progress.replace('\n' + inserted_line + '\n', '', 1) == old_progress
assert sha(ROOT / 'README.md') == before['documents_before']['README.md']

modified = ['reports/smooth_theorem.md', 'PROGRESS.md']
unchanged_documentation = []
for f, digest in before['other_documentation_before'].items():
    if f in modified:
        continue
    assert sha(ROOT / f) == digest, f
    unchanged_documentation.append(f)

diff = ''.join(''.join(difflib.unified_diff((OUT / 'before' / f).read_text().splitlines(keepends=True),
                                           (ROOT / f).read_text().splitlines(keepends=True),
                                           fromfile='before/' + f, tofile='after/' + f)) for f in modified)
(OUT / 'changes.diff').write_text(diff)
lines = {f: [i for i, line in enumerate((ROOT / f).read_text().splitlines(), 1)
             if line.startswith('相同时刻与两个端点') or line.startswith('文档对齐（2026-10-14）：')]
         for f in modified}
docs = {f: {'before_sha256': before['documents_before'][f], 'after_sha256': sha(ROOT / f),
            'changed_lines_after': lines[f]} for f in modified}
sources_read = [
    'LeanPML/Rectangle/SmoothPaths.lean', 'LeanPML/Rectangle/StatePaths.lean',
    'LeanPML/PML/MainSmoothRectangle.lean', 'LeanPML/Rectangle/RegionalCoefficients.lean',
    'LeanPML/PML/MainAbstract.lean', 'LeanPML/PML/OriginalSystem.lean', 'LeanPML/Time/Monotonicity.lean',
    '.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean',
]
record = {
    'scope': 'v0.5 端点时间正则性说明对齐，仅文档修订',
    'status': 'passed', 'checked_at': datetime.now().astimezone().isoformat(),
    'command': [sys.executable, str(Path(__file__).resolve())], 'cwd': str(ROOT),
    'modified_documents': docs, 'old_sentence': old_sentence, 'new_sentence': new_sentence.rstrip(),
    'T0_sentence_preserved': T0, 'sources_read': {f: sha(ROOT / f) for f in sources_read},
    'formal_sources_checked': len(accepted['formal_sources']), 'source_mismatches': source_mismatches,
    'formal_sources_match_v0_5_3': True, 'protected_files_unchanged': True, 'pdf_unchanged': True,
    'README_unchanged': True, 'other_documentation_unchanged': unchanged_documentation,
    'prior_acceptance_records_unchanged': before['referenced_acceptance_sha256'],
    'verification_kind': '本轮只读源码/调用链、SHA256及文档diff；引用既有成功构建和审计，未重跑',
    'build_rerun': False, 'axioms_audit_rerun': False,
    'referenced_prior_success_records': accepted['commands'][-2:],
    'historical_document_hashes': accepted['documents'],
    'historical_document_hash_policy': '旧overall_acceptance中的文档哈希对应修订前历史版本；不更改旧哈希或旧验收状态',
    'theorem_hypotheses_changed': False, 'new_mathematical_claims': False, 'next_stage_implemented': False,
    'proof_repair_required': False, 'independent_review': 'endpoint_doc_review 子代理只读复核；root检查diff及源码快照',
}
(OUT / 'record.json').write_text(json.dumps(record, ensure_ascii=False, indent=2) + '\n')

md = '''# v0.5 端点时间正则性：文档对齐记录

用途：区分一般闭区间时间引理的最小输入与当前具体光滑解类采用的更强技术延拓。本轮只改报告和追加进度记录，不改证明、结构、参数或任何PDF。

## 核对结果与调用链

- `SmoothPaths.lean:24–31` 的 `SmoothTimeJet` 在全轴有联合 C∞，`deriv_value/deriv_first` 均为 `∀ t x, HasDerivAt ... t`，包括0和T。`UniformTimeJet` 全轴一致范数可微，以及 `StatePaths.lean:35–55` 的加权可微条件，进一步提供实际L²/加权导数。
- `MainSmoothRectangle.lean:26–47` 的 `SmoothCompatibleSolution` 输入这些真实路径与正则性，`problem` 调用 `RegionalAbsorption.originalRegionalFiniteIntervalProblem`；没有额外输入端点原方程或目标能量导数公式。
- `OriginalSystem.lean:73–75` 的 `OriginalOn` 只要求 `(0,T)×Ω`；技术延拓可导不意味着域外/端点PDE被要求。`energy_law_and_closure` 也仅以 `t∈Ioo 0 T` 交付。
- `SmoothCompatibleSolution.energy_antitone` → `MainAbstract.energy7_antitoneOn_Conditional`（333–341）→ `Time.antitoneOn_Icc_of_hasDerivAt_nonpos`（32起）：闭区间连续、内部导数及内部非正符号。
- `SmoothCompatibleSolution.energy_integral_balance` → `MainAbstract.energy7_integral_balance_Conditional`（248–268）→ `integral_balance_of_hasDerivAt`（120–127）→ mathlib `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`（1142起）：闭区间连续、内部导数和区间可积性，无端点导数输入。
- 所以闭区间结论含端点、一般推理不需要端点导数，与当前具体定理的技术输入已含端点双侧可导性可以同时成立。更弱的时间入口尚未在当前具体主定理中实现；这是范围说明，非新增证明结论。

## 必要修改及保留范围

'''
md += f'- `reports/smooth_theorem.md:{lines[modified[0]][0]}`：仅改原含混句；$T=0$原说明逐字保留（现第87行）。\n'
md += f'- `PROGRESS.md:{lines[modified[1]][0]}`：新增一段本轮说明，其余全文与历史逐字保留。\n'
md += '''- README当前段没有直接同类错误，所以未改；历史“时间延拓”行保留。
- `Time/Monotonicity.lean` 和 `MainAbstract.lean` 的一般引理说明正确，未作机械替换。旧PROGRESS、定理清单、结论账本、PDF账本及v0.2指南的相关句子属于正确的一般接口/历史范围，全部保留。
- 本轮没有需要修复证明的发现；数学定理、签名和正则性输入均未改变。

## 修改前后

修改前：

> ''' + old_sentence + '\n\n修改后：\n\n> ' + new_sentence.rstrip() + '\n\n'
md += '## 哈希、检查与既有证据\n\n'
for f, item in docs.items():
    md += f'- `{f}`\n  - 修改前：`{item["before_sha256"]}`\n  - 修改后：`{item["after_sha256"]}`\n'
md += f'''
核对 {len(accepted['formal_sources'])} 份正式Lean源码（含导入与审计入口），与v0.5.3快照全部一致。锁定配置、合同、路线图、原论文和指定PDF哈希未变。实际diff只有上述两项说明修订，见 [changes.diff](changes.diff)；细项与源码哈希见 [record.json](record.json)，修改前备份及核对基线保存在本目录。

**本轮没有运行 `lake build` 或公理审计。** 引用既有v0.5.3成功记录：

- [原整体验收](../overall_acceptance.json)；旧源码与文档哈希不改写。
- [既有完整构建](../20261014T011533_485975_lake_build.log)，退出0。
- [既有740项公理审计](../20261014T011752_801259_axioms_audit.log)，退出0。

旧验收中的报告/进度文档哈希现在是**此次修订前的历史版本**，不是新文档哈希；此次前后对应单独记在本目录，不覆盖旧acceptance。本轮只是文档对齐，不推进下一阶段、不更新依赖、不提交或推送。
'''
(OUT / 'record.md').write_text(md)
pointer = ROOT / 'logs/v0.5.3/CURRENT_ENDPOINT_ALIGNMENT.tmp'
if pointer.is_file() and pointer.read_text() == str(OUT):
    pointer.unlink()  # 本轮创建的临时定位文件；不是任何历史记录。
print(json.dumps({'status': 'passed', 'modified_documents': modified, 'formal_sources_checked': len(accepted['formal_sources']),
                  'mismatch': source_mismatches, 'build_rerun': False, 'audit_rerun': False,
                  'record': str(OUT / 'record.md'), 'diff': str(OUT / 'changes.diff')}, ensure_ascii=False, indent=2))
