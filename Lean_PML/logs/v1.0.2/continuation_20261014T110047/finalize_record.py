"""本轮当前源码、实际日志及 PDF 检查的只读汇总；不覆盖旧阶段 acceptance。"""
from pathlib import Path
import json,hashlib,datetime,re
r=Path.cwd();d=r/'logs/v1.0.2/continuation_20261014T110047';pdfdir=r/'logs/v1.0.3/pdf/continuation_20261014T110047';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
v=json.loads((d/'verification_before_pdf.json').read_text());base=json.loads((d/'baseline.json').read_text())
for f,h in v['sources'].items():assert sha(r/f)==h,f
for f,entry in v['protected_hash_comparison'].items():
 if f.endswith('V7_global_energy_副本.pdf'):continue
 assert sha(r/f)==entry['before'],f
for key,info in v['commands'].items():
 m=json.loads((r/info['metadata']).read_text());assert m['exit_code']==0
 assert sha(r/info['log'])==info['output_sha256']
for name in ['M1_M3_final_semantic_review.md','M2_final_semantic_review.md']:
 s=(d/name).read_text()
 for f,h in re.findall(r'`(LeanPML[^`]*\.lean)`[^\n]*?`([0-9a-f]{64})`',s):assert sha(r/f)==h,(name,f)
# 逐页视觉检查由本轮实际查看 page-08.png 后登记；不是由纯文本提取替代。
image=pdfdir/'page-08.png';assert image.exists()
visual={'reviewed_at':datetime.datetime.now().astimezone().isoformat(),'modified_pages':[8],'render':'logs/v1.0.3/20261014T113338_141083_continuation_pdf_render.log','image':str(image.relative_to(r)),'image_sha256':sha(image),'method':'最终 PDF 重新打开，Poppler 160 dpi 渲染全部修改页，由助手实际查看整页图片','checks':{'four_new_vector_ticks_visible':True,'all_chinese_labels_readable':True,'no_clipping':True,'no_body_formula_number_or_old_annotation_overlap':True,'scope_matches_verified_theorems':True},'old_pending_note':'页底旧(5.8)未完成是保留历史；本轮公式旁新限定勾及账本准确更新状态。','result':'passed'}
(pdfdir/'visual_review.json').write_text(json.dumps(visual,ensure_ascii=False,indent=2))
result=json.loads((pdfdir/'annotation_result.json').read_text());result['visual_review']='passed';(pdfdir/'annotation_result.json').write_text(json.dumps(result,ensure_ascii=False,indent=2))
inspection=json.loads((pdfdir/'inspection.json').read_text());assert sha(Path(inspection['target']))==result['after_sha256']
v['pdf']={'result':str((pdfdir/'annotation_result.json').relative_to(r)),'visual_review':str((pdfdir/'visual_review.json').relative_to(r)),'backup':json.loads((pdfdir/'backup.json').read_text()),'target':inspection['target'],'sha256':result['after_sha256'],'pages':18,'old_annotations':211,'new_annotations':215,'modified_pages':[8],'added_ticks':4,'scope':'M1图逼近、实际弱场(5.8)、导数加权界、初始成员传播；无§5.3唯一性或弱主定理勾'}
v['new_formal_sources']={f:h for f,h in v['sources'].items() if f not in base['files']}
v['source_line_counts']={f:len((r/f).read_text().splitlines()) for f in v['new_formal_sources']}
v['semantic_reviews']={str((d/n).relative_to(r)):sha(d/n) for n in ['M1_M3_final_semantic_review.md','M2_final_semantic_review.md']}
v['documents']={f:sha(r/f) for f in ['README.md','PROGRESS.md','reports/weak_theorem.md','docs/source_inventory.md','docs/theorem_inventory.md','docs/claim_ledger.md','docs/pdf_formalization_marks.md']}
v['finalized_at']=datetime.datetime.now().astimezone().isoformat()
v['acceptance']='verified mathematical subresults; M3/M4 remain incomplete; not whole v1.0 release'
v['first_missing_theorem']='For m : RegionalWeakCoefficient D and g : zeroBoundaryGraph D, weakCoefficientMul D m g belongs to zeroBoundaryGraph D.'
v['next_required_lemma']='Internal compact weak H1 product m*f admits internal compact smooth approximation in all three L2 graph coordinates; M1 only handles smooth representatives.'
v['M4_gap']='Weak original eight equations -> actual historical lift, five field invariants, H01/weighted same-source paths; no new weak original-system main theorem.'
(d/'acceptance.json').write_text(json.dumps(v,ensure_ascii=False,indent=2))
(r/'logs/v1.0.1/continuation_20261014T110047_M1_acceptance.json').write_text(json.dumps({'status':'M1 target completed; previously recorded general smooth zero-trace bridge resolved','history_not_overwritten':True,'sources':{f:h for f,h in v['sources'].items() if f=='LeanPML/Rectangle/SmoothWeakClosure.lean'},'current_full_validation':v['commands'],'semantic_review':'logs/v1.0.2/continuation_20261014T110047/M1_M3_final_semantic_review.md','full_current_snapshot':'logs/v1.0.2/continuation_20261014T110047/acceptance.json','not_claimed':['general weak trace-kernel characterization','gauge uniqueness','weak original PDE main theorem']},ensure_ascii=False,indent=2))
(r/'logs/v1.0.3/continuation_20261014T110047_status.json').write_text(json.dumps({'status':'not_mathematically_complete','weak_main_theorem':False,'current_engineering_record':'logs/v1.0.2/continuation_20261014T110047/acceptance.json','current_full_validation':v['commands'],'isolation_this_round':v['isolation_this_round'],'pdf':v['pdf']},ensure_ascii=False,indent=2))
print(json.dumps({'formal_files':len(v['sources']),'new_formal_modules':len(v['new_formal_sources']),'new_lean_lines':sum(v['source_line_counts'].values()),'audited':v['audit_count'],'new_audited':v['new_audit_count'],'source_hashes_still_match':True,'protected_files_unchanged':True,'pdf_review':'passed','M1':'complete','M2':'exact field propagation results proved','M3':'partial','M4':'not complete','acceptance':str((d/'acceptance.json').relative_to(r))},ensure_ascii=False,indent=2))
