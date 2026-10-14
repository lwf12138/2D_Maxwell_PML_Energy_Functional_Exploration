from pathlib import Path
import json,hashlib,datetime,re
root=Path.cwd(); folder=root/'logs/v1.0_completion'; sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
base=json.loads((folder/'baseline_20261014T162626.json').read_text())['hashes']; sources=json.loads((folder/'source_snapshot.json').read_text());v=json.loads((folder/'verification_before_pdf.json').read_text());iso=json.loads((folder/'isolated_result.json').read_text())
assert all(sha(root/f)==h for f,h in sources.items())
assert iso['exit_code']==0 and iso['source_hashes']==sources
assert all(sha(root/f)==h for f,h in iso['source_hashes'].items())
protected={f:h for f,h in base.items() if not f.endswith('.lean') and not f.endswith('_副本.pdf')}
assert all(sha(root/f)==h for f,h in protected.items())
old_modules={f:h for f,h in base.items() if f.startswith('LeanPML/') and f.endswith('.lean')}
assert all(sha(root/f)==h for f,h in old_modules.items())
for k,command in v['commands'].items():
 assert json.loads((root/command['metadata']).read_text())['exit_code']==0
assert 'sorryAx' not in (root/v['commands']['audit']['log']).read_text()
for p in (folder/'isolated_logs').glob('*.json'):assert json.loads(p.read_text())['exit_code']==0
pdf=json.loads((folder/'pdf/annotation_result.json').read_text());vis=json.loads((folder/'pdf/visual_review.json').read_text());target=Path(json.loads((folder/'pdf/inspection.json').read_text())['target']);assert sha(target)==pdf['after_sha256'] and vis['passed']
new=v['new_files']; root_imports=(root/'LeanPML.lean').read_text()
assert all('import '+f[:-5].replace('/','.') in root_imports for f in new)
assert len(v['new_declarations'])==67 and v['audit_declarations']==997
append_only=['reports/weak_theorem.md','README.md','PROGRESS.md','docs/theorem_inventory.md','docs/claim_ledger.md','docs/scope.md','docs/source_inventory.md','docs/pdf_formalization_marks.md']
result={'time':datetime.datetime.now().isoformat(),'status':'verified_partial_completion','ROADMAP_v1_main_complete':False,'current_new_version_verified':True,
 'stages':{'v1.0.1':'空间已证成果保持；未据此声明全部原文对齐','v1.0.2':'精确Poincare和标量核完成；一般W1∞连续代表仍缺','v1.0.3':'精确常数/正长度Ck新入口及非零调用通过；一般原始弱系数入口未完成'},
 'mathematics':{'scalar_exponential_kernel':'proved and called for both original fields','sharp_rectangle_constant':'proved and connected to energy','original_numeric_threshold':'proved; c=1/128, S=1/512, K=48/pi²','actual_Ck_bridge':'proved for T>0 with canonical endpoint slots','original_auxiliary_bounds':'proved with sharp CP and initial energy','general_W1inf_continuous_representative':'not proved; independent continuity remains','T_zero':'existing sharp jet entry retains DegenerateJetCompatibility; not inferred from empty interior'},
 'commands':v['commands'],'audit_count':997,'new_audited_declarations':67,'sorryAx':False,
 'isolated_result':'logs/v1.0_completion/isolated_result.json','isolated_exit_code':0,'own_build_artifacts_copied':False,'dependency_cache_reused':True,
 'source_snapshot':'logs/v1.0_completion/source_snapshot.json','source_unchanged_after_build':True,'protected_hashes':protected,'old_modules_unchanged':True,
 'new_files':new,'type_review':'logs/v1.0_completion/20261014T170234_873529_type_review.log','semantic_review':'logs/v1.0_completion/semantic_review.md',
 'remaining_first_lemma':'一维分布弱导数为d的有界函数a.e.等于常数加d的积分原函数；随后构造闭区间Lipschitz代表并连接分离区域系数入口',
 'pdf':{k:val for k,val in pdf.items() if k!='entries'},'pdf_target':str(target),'pdf_ledger':'docs/pdf_formalization_marks.md',
 'document_hashes':{f:sha(root/f) for f in append_only},'not_claimed':['一般适定性','严格/指数衰减','全部W1∞原文入口','(10.2)任意m剖面全族','任意单点导数自动兼容'],'no_dependency_or_global_toolchain_change':True,'no_commit_or_push':True}
(folder/'acceptance.json').write_text(json.dumps(result,ensure_ascii=False,indent=2))
print(json.dumps({k:result[k] for k in ['status','ROADMAP_v1_main_complete','audit_count','new_audited_declarations','isolated_exit_code','source_unchanged_after_build','old_modules_unchanged']},ensure_ascii=False,indent=2))
