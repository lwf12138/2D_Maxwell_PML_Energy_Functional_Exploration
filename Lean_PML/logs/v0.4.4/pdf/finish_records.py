from pathlib import Path
import json,hashlib
root=Path.cwd();folder=root/'logs/v0.4.4/pdf';plan=json.loads((folder/'annotation_plan.json').read_text());result=json.loads((folder/'annotation_result.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(Path(plan['target']))==result['sha256_after']
visual={'method':'Poppler 150 dpi；主代理实际打开并逐页查看全部6张最终PNG，另有修改前独立人工定位审查','pages':{},'status':'passed'}
for n in result['modified_pages']:
 f=folder/f'after-{n}.png';assert f.exists()
 visual['pages'][str(n)]={'render':str(f.relative_to(root)),'sha256':sha(f),'review':'红勾及限定文字可见，位置对应公式，字体完整；无裁切、正文/编号遮挡或重复叠加；旧批注保留。'}
(folder/'visual_review.json').write_text(json.dumps(visual,ensure_ascii=False,indent=2)+'\n')
result['visual_review']='passed; see visual_review.json';(folder/'annotation_result.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
p=root/'docs/pdf_formalization_marks.md';s=p.read_text()
header=r'''

## v0.4：光滑矩形接口与完整场层映射的增量标注

本轮在最终全工程构建、公理审计与定理类型核验之后，只编辑指定副本。四子阶段分别完成；不是 v0.5 最终具体能量定理的发布。旧批注全部保留，旧“点态/待完成”作为历史范围，新标记明确覆盖本轮的所选光滑类。

- 实际页序与印刷页码均为 3、4、7、8、10、11；总页数保持18。
- 原183个批注/链接完整保留，新增8个矢量红勾及4条无勾说明，总195个批注；无原文文字、页序、MediaBox/CropBox变化。
- 本轮 C_P=2L_x 是已证保守常数，K=32μ(ε+2κ)L_x²，阈值同步该常数；原 (5.1) 的精确 π 常数不打完成勾。
- 技术全空间/全时间光滑延拓、C(K)一致范数和加权成员/路径正则性强于 V7 弱类；原PDE仍仅在(0,T)×Ω。未证明加权传播、弱Green、提升规范唯一性、解存在唯一性。

'''
header+=f"实际证据：[最终构建](../{plan['build']}) / [完整公理审计](../{plan['audit']})；另有[定理类型输出](../logs/v0.4.4/20261013T231145_231939_interface_types.log)与[独立语义检查](../logs/v0.4.4/semantic_review_geometry.md)。\n\n"
header+='| 实际页/印刷页 | 定位 | 类型与本轮标记 | Lean完整声明名和源码 | 已证范围及剩余接口 |\n|---|---|---|---|---|\n'
types=['真实光滑场方程对应','真实历史/时间及L²积分','真实场时间保持','初始兼容保持/场重构','光滑场双向对应','具体空间不等式；保守常数说明','真实原場时间保持','正则性输入；无勾说明','真实加权时间求导','具体光滑空间/边界结论']
for e,kind in zip(plan['entries'],types):
 mark=('✓ ' if e['kind']=='tick' else '无勾：')+'；'.join(e['draw']['lines'])
 code='<br>'.join('`'+n+'`' for n in e['theorems'])+'<br>'+' / '.join('['+Path(m).name+'](../'+m+')' for m in e['modules'])
 header+=f"| {e['page']}/{e['printed_page']} | {e['formula']} | {kind}；{mark} | {code} | {e['scope']} |\n"
header+=r'''
以上定理均在正式 LeanPML 导入链和最终 Audit 中；可从PDF红字范围区域打开批注，查看完整声明名及证据。仅作为方程/定义输入的 (2.1)、(2.2)、(2.3)、(6.6) 不因此得到无条件证明；(2.1) 勾只表示重构满足八式，(2.3) 勾只表示实际积分初值与求导。

旧范围核对：第4页原 CD/CZ1/CZ2 点态勾保留，由新“五个光滑场版”补全本轮范围；第8页原零区点态标记保留，新增原场保持。第11页旧“Green具体矩形证明待完成”保留，页顶新增“光滑矩形已接通，弱空间未完成”说明。第10页既有 (6.7)–(6.10) 仍为条件性结果；本轮只在(6.6)旁说明强正则性输入。第7页旧CP自由参数的历史系数标记保留，新注明确本轮CP实例化。未给 (5.7)/(5.8)、弱空间、规范唯一性、适定性、严格衰减或完美匹配增加勾。

两层迹的准确时间范围：u的闭区间迹来自u₀迹+真实历史+PEC；E是PEC输入；E_t在内部由真实求导得到。若另要求闭区间E_t迹，T>0通过连续延拓，T=0必须给初始导数迹条件。有限区间主框架仅需内部E_t迹，不能用空内部方程推出端点事实。

原场八槽往返恢复在闭区间；底层 primitive 八槽往返在开区间，历史u/q在闭区间。最高光滑原系统装配另已证明闭区间静态约束。固定初始原函数的历史构造不等于提升规范唯一性。

'''
header+=f"修改前SHA256：`{result['sha256_before']}`；最终SHA256：`{result['sha256_after']}`。\n\n"
header+='记录：[备份与哈希](../logs/v0.4.4/pdf/backup.json)、[定位/源码/定理计划](../logs/v0.4.4/pdf/annotation_plan.json)、[标注脚本](../logs/v0.4.4/pdf/annotate_pdf.py)、[结构检查](../logs/v0.4.4/pdf/annotation_result.json)、[逐页视觉验收](../logs/v0.4.4/pdf/visual_review.json)。稳定ID确保重跑不叠加；脚本校验输入哈希，不会覆盖别人的后续批注。\n'
assert '## v0.4：光滑矩形接口' not in s;p.write_text(s+header)
a=root/'logs/v0.4.4/acceptance.json';rec=json.loads(a.read_text());rec['pdf_status']='passed';rec['pdf_evidence']='logs/v0.4.4/pdf/annotation_result.json';rec['v0.4_status']='four sub-stages passed; stopped before v0.5';a.write_text(json.dumps(rec,ensure_ascii=False,indent=2)+'\n')
p=root/'PROGRESS.md';s=p.read_text();cut=s.index('\n---\n');before=s[:cut].replace('\\\\','\\');s=before+s[cut:];p.write_text(s)
print('PDF ledger, visible review and final phase acceptance recorded.')
