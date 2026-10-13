"""最终审计通过后创建新备份及证明—位置计划，不修改 PDF。"""
from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import hashlib,json,re,shutil
from pypdf import PdfReader
root=Path.cwd();folder=root/'logs/v0.3.5/pdf'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
accepted={s:json.loads((root/'logs'/s/'acceptance.json').read_text()) for s in ['v0.3.4','v0.3.5']}
for a in accepted.values():
    for k in ['build','audit']:
        m=json.loads((root/a[k]).with_suffix('.json').read_text());assert m['exit_code']==0 and m['status']=='finished'
    for f,h in a['sources'].items():assert sha(root/f)==h,f
final=accepted['v0.3.5'];output=(root/final['audit']).read_text();assert 'sorryAx' not in output
names=set(re.findall(r"'([^']+)' depends on axioms",output))
assert len(names)==369
layout=json.loads((folder/'layout_draft.json').read_text())
# 每项只关联真实证明，不把 J 定义本身当成结论。
evidence={
 'main-dissipation':('DissipationClosure',['dissipation7_lower_Conditional','dissipation7_nonneg_Conditional'],'(6.8) 的精确剩余耗散下界与非负性；原层演化、同源真实路径和共同迹 Poincaré 下，时间在内部。'),
 'main-balance':('MainAbstract',['energy7_antitoneOn_Conditional','energy7_integral_balance_Conditional','main_energy_estimate_Conditional'],'(6.9) 有限闭区间单调不增与真实时间积分平衡；两层分量闭区间连续和静态兼容，内部真实演化；积分平衡另需 second.R=P_tt 连续。'),
 'preliminary':('DissipationClosure',['fieldDissipation_lower','debye_relations_Conditional','dissipation7_preliminary_Conditional'],'由实际场单层余项积分与真实兼容求导，得到 (9.1)，保留两项负项；未把单层耗散非负作为输入。'),
 'j-analysis':('GradientControl',['fieldJ_integrable','fieldJ_eq_integral','fieldJ_nonneg','fieldJDensity_zero_region'],'实际 L² 与有界 θ 系数下，J 密度可积、内积/积分相等且非负；零区密度为两个梯度表达分量平方和。红勾不表示定义本身是证明。'),
 'spatial-j':('GradientControl',['fieldSpatialDissipation_ge_J'],'(9.3) 的两个实际积分下界；非负吸收和幅度限制，空间表达 h=Λ−ψ，零区恢复 ψ=0。'),
 'gradient-evolution':('GradientControl',['gradient_evolution_Conditional'],'(9.4) 从原层辅助演化和同源真实导数推出；依赖受限梯度域、空间约束及沿路径时间交换接口。'),
 'gradient-control':('GradientControl',['field_gradient_control','gradient_control_Conditional'],'(9.5) 从 (9.4)、θ 的两种系数估计和三项平方估计，经合法实际 L² 积分得到；覆盖零区、双边层和角层。'),
 'spatial-absorption':('DissipationClosure',['scale_amplitude_chain','spatial_absorption_Conditional','spatial_absorption_half_Conditional'],'(9.6) 由共同迹核的 Poincaré、(9.3)、(9.5) 与原阈值推出；非空空间载体仅用于从0≤p≤S取得S≥0。'),
 'debye-absorption':('DissipationClosure',['debye_relations_Conditional','debye_absorption_split','debye_absorption_Conditional'],'(9.7) 由邻域兼容的两次真实求导得到 κ E_t=P_t+τP_tt，再从原阈值的两条材料条件分别吸收。'),
 'remainder-budget':('DissipationClosure',['dissipation7_lower_Conditional','dissipation7_nonneg_Conditional'],'同时扣除不同负项，保留空间耗散1/2与 μτ/(4κ) 的 Debye 平方预算；不是重复使用同一正项。')}
missing='具体矩形 Green、迹、精确 Poincaré 与时间/空间交换；完整原八变量 PDE 对应、提升唯一性与解存在唯一性。'
for e in layout['entries']:
    module,thms,scope=evidence[e['id']];stage='v0.3.4' if module=='GradientControl' else 'v0.3.5'
    e.update(module='LeanPML/PML/'+module+'.lean',theorems=['LeanPML.PML.'+t for t in thms],
       category='实际 L² 积分子结论' if e['id']=='j-analysis' else '条件性空间结论',
       scope=scope,missing=missing,new_tick=True,printed_page=e['page'],stage=stage,
       build_log=accepted[stage]['build'],audit_log=accepted[stage]['audit'])
    assert set(e['theorems'])<=names,e['id']
    e['source_sha256']=sha(root/e['module'])
old_entries=0
for stage in ['v0.2.3','v0.2.4','v0.3.1','v0.3.3']:
    plan=json.loads((root/'logs'/stage/'pdf/annotation_plan.json').read_text())
    for e in plan['entries']:
        assert set(e['theorems'])<=names,(stage,e['id'])
        old_entries+=1
protected=json.loads((root/'logs/v0.3.4/source_snapshot.json').read_text())['protected']
for f,h in protected.items():assert sha(root/f)==h,f
target=(root/'../results/V7_Maxwell_Debye_PML/V7_global_energy_副本.pdf').resolve()
assert sha(target)=='c9d5b114e9de7befb92e001ccc1486227acef27c8c0933fc688722eaf3ca44a3'
if (folder/'backup.json').exists():
    backup=json.loads((folder/'backup.json').read_text());assert sha(Path(backup['backup']))==sha(target)==backup['sha256_before']
else:
    name='before_v0.3.4-v0.3.5_'+datetime.now(ZoneInfo('Asia/Shanghai')).strftime('%Y%m%dT%H%M%S')+'.pdf'
    dest=folder/name;assert not dest.exists();shutil.copy2(target,dest)
    backup=dict(target=str(target),backup=str(dest),sha256_before=sha(target),bytes_before=target.stat().st_size)
    (folder/'backup.json').write_text(json.dumps(backup,ensure_ascii=False,indent=2)+'\n')
reader=PdfReader(target)
plan=dict(stage='v0.3.4–v0.3.5',page_count=len(reader.pages),backup=backup,
 build=Path(final['build']).stem,audit=Path(final['audit']).stem,
 evidence=accepted,entries=layout['entries'],notes=layout['notes'],font='/System/Library/Fonts/Supplemental/Arial Unicode.ttf',
 modified_pages=[10,12,13,14],protected_hashes={str((root/f).resolve()):h for f,h in protected.items()},
 source_hashes={f:h for a in accepted.values() for f,h in a['sources'].items()},
 current_audited_theorems=len(names),old_mark_entries_rechecked=old_entries,
 old_annotations_preserved_count=sum(len(p['/Annots']) if '/Annots' in p else 0 for p in reader.pages))
assert len(reader.pages)==18 and plan['old_annotations_preserved_count']==168
assert not(folder/'annotation_plan.json').exists(),'计划已存在；不覆盖已有计划'
(folder/'annotation_plan.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:plan[k] for k in ['page_count','modified_pages','current_audited_theorems','old_mark_entries_rechecked','old_annotations_preserved_count','backup']},ensure_ascii=False,indent=2))
