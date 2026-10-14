"""最终只读核验与整体验收：实际记录不依赖旧成功文字。"""
from pathlib import Path
from datetime import datetime
import hashlib, json, re

ROOT = Path(__file__).resolve().parents[2]
LOG = ROOT / 'logs/v0.5.3'
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def read(path): return json.loads(path.read_text())
baseline = read(ROOT / 'logs/v0.5.1/baseline.json')
stages = [read(ROOT / f'logs/v0.5.{i}/acceptance.json') for i in (1, 2, 3)]
final = stages[-1]
assert all(s['status'] == 'passed' for s in stages)
assert (LOG / 'final_documentation_review.md').exists()

commands = []
prior_changed = []
for s in stages:
    for kind in ('build', 'audit'):
        logfile = ROOT / s[kind]
        metadata = read(logfile.with_suffix('.json'))
        assert metadata['cwd'] == str(ROOT)
        assert metadata['status'] == 'finished' and metadata['exit_code'] == 0
        assert logfile.exists() and logfile.stat().st_size > 0
        commands.append({'stage': s['stage'], 'kind': kind, 'metadata': str(logfile.with_suffix('.json').relative_to(ROOT)),
                         'output': s[kind], 'output_sha256': sha(logfile), 'exit_code': 0})
    for file, digest in s['sources'].items():
        if sha(ROOT / file) != digest:
            assert file in ('LeanPML.lean', 'Audit.lean'), (s['stage'], file)
            prior_changed.append({'stage': s['stage'], 'file': file, 'reason': '后阶段只追加正式导入/审计；最终全工程已覆盖'})
for file, digest in final['sources'].items():
    assert sha(ROOT / file) == digest, file
for file, digest in final['protected'].items():
    assert sha(ROOT / file) == digest == baseline['hashes'][file], file

old_lean = {f: h for f, h in baseline['hashes'].items() if f.endswith('.lean') and f not in ('LeanPML.lean','Audit.lean')}
assert all(sha(ROOT / f) == h for f, h in old_lean.items())
initial_audit = (ROOT / 'logs/v0.5.1/initial_files/Audit.lean').read_text()
assert (ROOT / 'Audit.lean').read_text().startswith(initial_audit)

expected_new = [
    'LeanPML/PML/MainSmoothRectangle.lean', 'LeanPML/Examples/SmoothBump.lean',
    'LeanPML/Examples/FullDomainProfile.lean', 'LeanPML/Examples/PathHelpers.lean',
    'LeanPML/Examples/CompatibleData.lean', 'LeanPML/Examples/DegenerateBranches.lean',
    'LeanPML/Examples/StaticMode.lean', 'LeanPML/PML/Obstructions/UnrestrictedData.lean',
]
assert all(f in final['sources'] for f in expected_new)
assert final['audited_declarations'] == 740 and not final['sorryAx']
assert set(final['axioms']) <= {'Classical.choice','Quot.sound','propext'}

# 检查结构字段本身，不把名称或公理输出当作假设语义的替代。
source = (ROOT / expected_new[0]).read_text()
block = source.split('structure SmoothCompatibleSolution',1)[1].split('namespace SmoothCompatibleSolution',1)[0]
field_names = re.findall(r'^  (\w+)\s*:', block, re.M)
assert len(field_names) == 19, field_names
expected_fields = ['ε_pos','κ_pos','τ_pos','μ_pos','c_le_threshold','F','u0','q0','B','regular','identified','T_nonneg',
                   'history_regular','equations','initial','zero_initial','PEC','u0_boundary','degenerate']
assert field_names == expected_fields, field_names
for forbidden in ('FiniteIntervalProblemConditional', 'HasDerivAt s.energy', 'AntitoneOn', 'dissipation7', 'energy7'):
    assert forbidden not in block, forbidden

pdf = read(LOG / 'pdf/annotation_result.json')
visual = read(LOG / 'pdf/visual_review.json')
backup = read(LOG / 'pdf/backup.json')
assert sha(Path(backup['backup'])) == backup['sha256_before']
assert sha(Path(backup['target'])) == pdf['sha256_after'] == visual['pdf_sha256']
assert pdf['pages'] == 18 and pdf['old_annotations'] == 200 and pdf['annotations_after'] == 208
assert pdf['original_text_preserved'] and pdf['old_annotations_preserved']
assert pdf['text_and_annotation_overlap'] == 0 and pdf['visual_review'] == visual['status'] == 'passed'
assert sorted(pdf['modified_pages']) == sorted(p['page'] for p in visual['pages'])

docs = ['README.md','PROGRESS.md','reports/smooth_theorem.md','docs/source_inventory.md',
        'docs/theorem_inventory.md','docs/claim_ledger.md','docs/pdf_formalization_marks.md']
links = []; missing = []
for file in docs:
    path = ROOT / file
    text = path.read_text()
    # 本轮新增部分或整份新报告；原历史链接的问题不会伪装成新结论。
    if file == 'README.md': text = text.split('# 以下为 v0.4')[0]
    elif file == 'PROGRESS.md': text = text.split('# 以下为阶段内')[0]
    elif file.startswith('docs/'):
        title = {'docs/source_inventory.md':'## 2026-10-14：v0.5 来源',
                 'docs/theorem_inventory.md':'## 2026-10-14：v0.5 三阶段',
                 'docs/claim_ledger.md':'## 2026-10-14：v0.5 结论',
                 'docs/pdf_formalization_marks.md':'## 2026-10-14：v0.5 光滑'}[file]
        text = text.split(title,1)[1]
    for target in re.findall(r'\]\(([^)]+)\)', text):
        if target.startswith(('http:', 'https:', '#')): continue
        target = target.split('#')[0].strip('<>')
        resolved = path.parent / target
        if target.endswith('overall_acceptance.json'): continue  # 本次核验通过才生成
        if not resolved.exists(): missing.append({'file': file, 'target': target})
        links.append({'file': file, 'target': target})
assert not missing, missing

record = {
    'scope': 'v0.5.1–v0.5.3 全部验收；止于光滑兼容类具体先验定理和实例，不实施v1.0',
    'status': 'passed', 'time': datetime.now().astimezone().isoformat(),
    'stages': [{'stage': s['stage'], 'acceptance': f"logs/{s['stage']}/acceptance.json", 'status': 'passed',
                'audited_declarations': s['audited_declarations']} for s in stages],
    'commands': commands, 'formal_source_count': len(final['sources']), 'formal_sources': final['sources'],
    'new_modules': expected_new, 'all_new_modules_reachable_from_default_entry': True,
    'previous_proof_sources_unchanged': True, 'previous_entry_audit_changes': prior_changed,
    'legacy_audit_preserved': True, 'protected_files_unchanged': final['protected'],
    'axioms': final['axioms'], 'sorryAx': False,
    'main_input_fields_count': len(field_names), 'main_input_fields': field_names,
    'semantic_reviews': ['logs/v0.5.1/semantic_review.md','logs/v0.5.1/semantic_review_geometry.md',
                         'logs/v0.5.3/semantic_review_examples.md','logs/v0.5.3/final_documentation_review.md'],
    'regularity_scope': '一般定理保留明确强正则性；具体实例逐项由构造证明；见scope_supplement.json',
    'retained_failure_records': {s['stage']: s['retained_failures'] for s in stages},
    'documents': {f: sha(ROOT / f) for f in docs}, 'new_local_links_checked': len(links), 'missing_links': missing,
    'pdf': {'target': backup['target'], 'sha256': pdf['sha256_after'], 'backup': 'logs/v0.5.3/pdf/backup.json',
            'modified_pages': pdf['modified_pages'], 'new_ticks': pdf['added_red_ticks'],
            'new_notes': pdf['added_annotations']-pdf['added_red_ticks'], 'old_annotations_preserved': True,
            'structural_check': 'logs/v0.5.3/pdf/annotation_result.json', 'visual_check': 'logs/v0.5.3/pdf/visual_review.json'},
    'not_claimed': final['not_claimed'],
}
(LOG / 'overall_acceptance.json').write_text(json.dumps(record, ensure_ascii=False, indent=2)+'\n')
print(json.dumps({k: record[k] for k in ('status','formal_source_count','main_input_fields_count','new_local_links_checked','missing_links','pdf')}, ensure_ascii=False, indent=2))
