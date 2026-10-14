from pathlib import Path
import json,hashlib,re,datetime,subprocess
root=Path.cwd();folder=root/'logs/v1.0_finalization';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
v=json.loads((folder/'verification_before_pdf.json').read_text());sources=v['sources'];iso=json.loads((folder/'isolated_result.json').read_text())
assert iso['exit_code']==0 and iso['source_still_matches'] and iso['source_hashes']==sources
assert all(sha(root/f)==h for f,h in sources.items())
assert all(sha(root/f)==h for f,h in v['protected_hashes'].items())
for c in v['commands'].values():assert json.loads((root/c['metadata']).read_text())['exit_code']==0
for p in (folder/'isolated_logs').glob('*.json'):assert json.loads(p.read_text())['exit_code']==0
ia=sorted((folder/'isolated_logs').glob('*_isolated_axioms_audit.log'))[-1].read_text();assert 'sorryAx' not in ia
assert len(re.findall('depends on axioms',ia))==1058
assert subprocess.check_output(['git','-C','.lake/packages/mathlib','rev-parse','HEAD'],text=True).strip()=='fabf563a7c95a166b8d7b6efca11c8b4dc9d911f'
pdf=json.loads((folder/'pdf/annotation_result.json').read_text());vis=json.loads((folder/'pdf/visual_review.json').read_text());target=Path(json.loads((folder/'pdf/inspection.json').read_text())['target'])
assert vis['passed'] and sha(target)==pdf['after_sha256'] and pdf['original_text_preserved'] and pdf['old_annotations_preserved']
assert pdf['pages']==18 and pdf['old_annotations']==231 and pdf['new_annotations']==237
# 不能仅验证新文件；全部正式模块必须从默认入口可达。
seen=set()
def visit(f):
 if f in seen:return
 seen.add(f)
 for n in re.findall(r'^import\s+(LeanPML(?:\.[\w]+)*)\s*$',(root/f).read_text(),re.M):
  p=n.replace('.','/')+'.lean'
  if (root/p).exists():visit(p)
visit('LeanPML.lean')
assert {f for f in sources if f.startswith('LeanPML/') and f.endswith('.lean')}<=seen
# 保留源文件版验收：当前版本和原文主线对齐分开列，T=0 的数据语义单独说明。
result={'time':datetime.datetime.now().isoformat(),'status':'completed_verified','ROADMAP_v1_main_complete':True,'current_new_version_verified':True,'V7_main_alignment_complete':True,
 'stages':{'v1.0.1':'完成：真实弱图/H0闭包/加权空间及所需逼近与乘法','v1.0.2':'完成：弱Green、精确Poincare、一般弱系数代表、记忆/加权保持、提升唯一性','v1.0.3':'完成：一般原弱系数主入口、同源真实路径、原变量控制、非零回归、隔离/类型/PDF验收'},
 'main_theorems':['LeanPML.PML.Weak.OriginalInterval.main_energy_GeneralWeakCk','LeanPML.PML.Weak.OriginalInterval.main_energy_GeneralWeakJet'],
 'controls':['LeanPML.PML.Weak.OriginalInterval.auxiliary_current_GeneralWeakCk','LeanPML.PML.Weak.OriginalInterval.auxiliary_current_GeneralWeakJet','LeanPML.PML.Weak.OriginalInterval.auxiliary_initial_GeneralWeakJet'],
 'lift_independence':'LeanPML.PML.Weak.twoLayerEnergy_independent_GeneralWeak',
 'mathematics':{'general_weak_representative':'proved from actual regional weak derivatives, called inside final raw-original-system entrance','sharp_rectangle_constant':'CP²=(π²/Lx²+π²/Ly²)⁻¹, proved and used','original_threshold':'c*=π²/1152; c=1/128,S=1/512; exact arithmetic and rigorous π bounds','original_power_profile':'all natural m≥2, 0<ηx,ηy≤1/512; true weak derivatives, all branches, nonconstant representative, main call','scalar_memory':'previous proved scalar/operator exponential identification reused and applicable to same represented original path','time_regularity':'T>0 actual closed-interval Ck core → canonical slots → derived λtt; only interior PDE','T_zero':'explicit lawful initial jet compatibility; no implication from empty interior or singleton Ck','nonzero_solution':'static_main_call/static_ck_call, positive constant energy, interior D=0','formulas':['(2.3)–(2.6) in declared weak path class','(5.1)','(5.7)–(5.8)','§5.3','(6.7)–(6.10)','(8.4)–(8.8)','(9.5)–(9.7)','(10.1)–(10.2)']},
 'commands':v['commands'],'audit_count':1058,'unique_audited_declarations':1050,'new_audited_declarations':len(v['new_declarations']),'standard_axioms':v['standard_axioms'],'sorryAx':False,
 'formal_files':119,'all_formal_modules_reachable':True,'isolated_result':'logs/v1.0_finalization/isolated_result.json','isolated_directory':iso['directory'],'isolated_exit_code':0,'own_build_artifacts_copied':False,'dependency_cache_reused':True,'source_snapshot':'logs/v1.0_finalization/source_snapshot.json','source_unchanged_after_final_verification':True,'protected_hashes':v['protected_hashes'],'old_formal_modules_unchanged':True,
 'new_files':v['new_files'],'semantic_review':'logs/v1.0_finalization/semantic_review.md','remaining_v1_main_analysis_interfaces':[],
 'explicit_scope':['给定足够正则、初始兼容原解的先验定理','区域分离弱导数的有界代表表示；换代表a.e.一致已证明','T>0 Ck入口和T=0合法初始jet入口分开','商类/逐时刻a.e.；未交换为共同零测集全时间点态等式'],
 'not_claimed':['一般解存在唯一性','严格或指数衰减','任意幅度/任意八变量初值稳定性','单点Ck自动决定任意jet','可选Laplace/V6分析','R/D分支'],
 'pdf':{k:val for k,val in pdf.items() if k!='entries'},'pdf_target':str(target),'pdf_ledger':'docs/pdf_formalization_marks.md','no_dependency_or_global_toolchain_change':True,'no_commit_or_push':True}
# 数学和工程均完成后才在首页登记，不改写历史正文。
banner='> **最终验收通过（2026-10-14）：ROADMAP v1.0.1–v1.0.3 主线完成。** 119 个正式 Lean 文件进入默认构建；1058 次公理审计输出（1050 个不同声明），无 sorryAx；当前源码隔离构建及完整审计通过。范围为报告列明的 V7 足够正则弱图空间兼容类，T=0 合法初始 jet 语义单列。\n\n'
for n in ['README.md','PROGRESS.md','reports/weak_theorem.md']:
 p=root/n;s=p.read_text()
 if banner not in s:
  i=s.index('\n\n')+2;s=s[:i]+banner+s[i:];p.write_text(s)
final_note='''\n\n### v1.0_finalization 最终工程与 PDF 验收（2026-10-14）

当前119个正式 Lean 文件全部可达，默认构建3131 jobs通过；1058次审计输出覆盖1050个不同声明，本轮新增61个不同审计声明，无 sorryAx，仅标准 propext/Classical.choice/Quot.sound。当前源码隔离重编和完整审计通过，复用精确依赖缓存、不复制项目编译产物。源文件在最终验证后未改变。

PDF 实际/印刷第3、9、10、15页新增5勾及1条限定说明，18页和231条旧批注全部保留；最终237条批注。逐页渲染和碰撞检查通过，详见本轮 `pdf/annotation_result.json`、`pdf/visual_review.json`。旧第一次隔离结果保留为 `isolated_intermediate_*`：它之后曾补充当前辅助变量控制，因此不作为最终源码证据；最终隔离使用新目录重新从零构建。

最终依据为 [acceptance.json](../logs/v1.0_finalization/acceptance.json) 与 [source_snapshot.json](../logs/v1.0_finalization/source_snapshot.json)。主线没有尚未兑现的分析接口；T=0初始图状态条件及先验解正则性保留为明示的数学输入，不宣称适定性、严格衰减或任意分布解理论。
'''
for n in ['docs/theorem_inventory.md','docs/claim_ledger.md','docs/scope.md','docs/source_inventory.md','docs/pdf_formalization_marks.md']:
 p=root/n;s=p.read_text()
 if '### v1.0_finalization 最终工程与 PDF 验收（2026-10-14）' not in s:p.write_text(s+final_note)
docs=['README.md','PROGRESS.md','reports/weak_theorem.md','docs/theorem_inventory.md','docs/claim_ledger.md','docs/scope.md','docs/source_inventory.md','docs/pdf_formalization_marks.md']
result['document_hashes']={f:sha(root/f) for f in docs}
(folder/'acceptance.json').write_text(json.dumps(result,ensure_ascii=False,indent=2))
print(json.dumps({k:result[k] for k in ['status','ROADMAP_v1_main_complete','V7_main_alignment_complete','audit_count','unique_audited_declarations','new_audited_declarations','isolated_exit_code','source_unchanged_after_final_verification','remaining_v1_main_analysis_interfaces']},ensure_ascii=False,indent=2))
