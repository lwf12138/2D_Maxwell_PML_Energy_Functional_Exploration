from pathlib import Path
import json,hashlib,datetime
p=Path.cwd();v=json.loads((p/'logs/v1.0.3/verification_before_pdf.json').read_text());clean=json.loads((p/'logs/v1.0.3/clean_result.json').read_text());pdf=json.loads((p/'logs/v1.0.3/pdf/annotation_result.json').read_text());assert pdf['visual_review']=='passed' and clean['engineering_status']=='passed'
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
missing=['H1 graph approximation for all old smooth zero-trace fields','regional W1-infinity weak product rule and membership','weighted propagation (5.8), phi_t estimate and time regularity','lift gauge uniqueness and lift-independent energy','weak original-system assembly and final two-layer theorem','nonzero example calling the new weak main theorem (not yet constructed)']
docs=['reports/weak_theorem.md','README.md','PROGRESS.md','docs/source_inventory.md','docs/theorem_inventory.md','docs/claim_ledger.md','docs/pdf_formalization_marks.md']
for stage,status in [('v1.0.2','partial'),('v1.0.3','not_complete')]:
 failures=[]
 for f in (p/'logs'/stage).glob('*.json'):
  try:j=json.loads(f.read_text())
  except Exception:continue
  if isinstance(j,dict) and j.get('command') and j.get('exit_code') not in [None,0]:failures.append(str(f.relative_to(p)))
 r={'stage':stage,'created_at':datetime.datetime.now().isoformat(),'status':status,'engineering_checks_passed':True,'mathematical_stage_complete':False,'verified_subtasks':['weak Green and existing-interface construction','weak Poincare with CP=2Lx and interface','real graph-valued time derivatives projected to L2','pointwise real-time integral formula (5.7)','nonzero spatial and temporal calls'],'not_completed':missing,'stage_commands':v['commands'][stage],'sources':v['sources'],'audit_count':v['audit_count'],'axioms':v['axioms'],'checks':v['checks'],'semantic_review':'logs/v1.0.2/semantic_review.md','type_output':str(sorted((p/'logs/v1.0.2').glob('*_declaration_types.log'))[-1].relative_to(p)),'source_baseline':'logs/v1.0.2/baseline_comparison.json','documents':{f:sha(p/f) for f in docs},'failure_metadata':sorted(failures),'clean_reproduction':'logs/v1.0.3/clean_result.json','pdf':{'modified_pages':pdf['modified_pages'],'red_ticks_added':1,'notes_added':2,'sha256':pdf['after_sha256'],'visual_review':'logs/v1.0.3/pdf/visual_review.json','scope':'weak zero-trace Green; notes only for conservative Poincare and pointwise 5.7; no weak PDE main theorem marks'},'v101_previous_acceptance_preserved':'logs/v1.0.1/acceptance.json','v05_formal_proofs_unchanged':True}
 (p/'logs'/stage/'acceptance.json').write_text(json.dumps(r,ensure_ascii=False,indent=2))
print('v1.0.2: partial. v1.0.3: not_complete. Delivered-subtask engineering checks passed; three modified PDF pages visually checked.')
