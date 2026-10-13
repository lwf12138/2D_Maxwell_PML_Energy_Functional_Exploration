from pathlib import Path
from datetime import datetime
import json,hashlib,re
from urllib.parse import unquote
r=Path.cwd();d=r/'logs/v0.4_alignment';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
v=json.loads((d/'verification.json').read_text());base=json.loads((d/'baseline.json').read_text());pdf=json.loads((d/'pdf/annotation_result.json').read_text());plan=json.loads((d/'pdf/annotation_plan.json').read_text())
assert v['status']=='passed' and pdf['visual_review']=='passed'
for k,hashes in [('sources',v['sources']),('protected',v['protected'])]:
 for f,s in hashes.items():assert sha(r/f)==s,(k,f)
assert sha(Path(plan['target']))==pdf['sha256_after']
# 首个新审计块之前的文本应与入场Audit逐字节相同。
oldprefix=(r/'Audit.lean').read_text().split('\n-- v0.4 对齐：精确参数证书；')[0]
assert hashlib.sha256(oldprefix.encode()).hexdigest()==base['hashes']['Audit.lean']
errors=[]; docs=['README.md','PROGRESS.md','docs/source_inventory.md','docs/theorem_inventory.md','docs/claim_ledger.md','docs/pdf_formalization_marks.md','logs/v0.4_alignment/alignment_record.md']
# 仅检查本次新增段/新记录链接；旧历史包含当时环境链接，不擅自改写。
for name in docs:
 path=r/name;s=path.read_text()
 if name=='PROGRESS.md':s=s.split('\n---\n',1)[0]
 elif name.startswith('docs/'):
  pos=s.rfind('## 2026-10-14');s=s[pos:] if pos>=0 else ''
 for link in re.findall(r'\]\(([^)]+)\)',s):
  if link.startswith(('http','mailto','#')):continue
  target=unquote(link.strip('<>')).split('#')[0]
  if not target:continue
  f=(path.parent/target).resolve()
  if f.name=='acceptance.json' and f.parent==d:continue
  if not f.exists():errors.append((name,link))
assert not errors,errors
failures=[]
for f in sorted(d.glob('*.json')):
 m=json.loads(f.read_text())
 if isinstance(m,dict) and m.get('status')=='finished' and m.get('exit_code',0)!=0:
  failures.append({'metadata':str(f.relative_to(r)),'exit_code':m['exit_code'],'command':m.get('command_display')})
accept=dict(v);accept.update(status='passed',completed_at=datetime.now().astimezone().isoformat(),pdf='passed',pdf_report='logs/v0.4_alignment/pdf/annotation_result.json',pdf_visual='logs/v0.4_alignment/pdf/visual_review.json',pdf_sha256=pdf['sha256_after'],all_legacy_audit_text_preserved=True,retained_failures=failures,documents={name:sha(r/name) for name in docs},alignment_record='logs/v0.4_alignment/alignment_record.md',repairs={'parameter_certificate':'proved','regional_absorption_entry':'proved','classical_spatial_evidence_and_wrappers':'proved; old smooth highest-level evidence already existed','technical_regularity_wording':'corrected; stronger assumptions explicitly retained'},v04_scope={'proved':'specific smooth rectangle Green and conservative Poincare, history, five field invariants, bidirectional equations, concrete finite-interval construction; alignment supplements linked','regularity_inputs':['joint C-infinity technical extension','C(K) uniform path continuous/differentiable','actual weighted membership and path continuity/differentiability','OriginalLiftRegular and LiftIdentified','initial five compatibility, PEC, zero-region initial auxiliary fields','T=0 required initial first-graph compatibility'],'future':['exact pi constant','weak H1/Hdiv and general W1infty class','weighted propagation 5.7/5.8','lifting gauge uniqueness','existence and uniqueness','v0.5.1 named concrete energy theorem synthesis']},ready_for_v051='yes, for the explicitly selected strong smooth/weighted class; not the complete weak V7 range')
(d/'acceptance.json').write_text(json.dumps(accept,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':accept['status'],'audited_declarations':accept['audited_declarations'],'formal_sources_verified':len(v['sources']),'protected_files_unchanged':len(v['protected']),'all_legacy_audit_text_preserved':True,'document_links':'passed','pdf_pages':pdf['pages'],'pdf_old_annotations_preserved':pdf['old_annotations_preserved'],'pdf_new_annotations':pdf['added_annotations'],'retained_failure_count':len(failures),'ready_for_v051':accept['ready_for_v051']},ensure_ascii=False,indent=2))
