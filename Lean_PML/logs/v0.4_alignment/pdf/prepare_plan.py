from pathlib import Path
import json
r=Path.cwd();d=r/'logs/v0.4_alignment/pdf'
before=json.loads((d/'before_inspection.json').read_text())
C='LeanPML.PML.Concrete.';R='LeanPML.Rectangle.RegionalAbsorption.';P='LeanPML.Rectangle.ParameterCertificate.'
entries=[
 {'id':'classical-original','page':3,'printed_page':3,'formula':'(2.1)：旧光滑重构核验的接口限定','kind':'note','draw':{'x':68,'top':48,'font_size':6.5,'lines':['v0.4 对齐：古典包装显式给出 E、Hx、Hy 的空间可导证据；八方程输入本身不保证空间光滑。']},'theorems':[C+'originalClassicalOn_of_liftIdentified',C+'primitive_to_original_classical_rectangle'],'modules':['LeanPML/PML/ClassicalSystem.lean'],'scope':'原式定义不打新勾。旧高层的光滑代表原已成立，本次正式推出空间DifferentiableAt及坐标HasDerivAt，并给带PEC反向古典包装；不是认为底层fderiv等式自动可导。'},
 {'id':'classical-equivalence','page':4,'printed_page':4,'formula':'(2.6)、命题2.1：旧双向光滑标注补充','kind':'note','draw':{'x':68,'top':60,'font_size':6,'lines':['对齐补充：古典双向映射已显式携带真实空间可导；仅所选强光滑类，非完整弱解理论。']},'theorems':[C+'original_to_primitive_classical_rectangle',C+'primitive_to_original_classical_rectangle',R+'originalRegionalFiniteIntervalProblem'],'modules':['LeanPML/PML/ClassicalSystem.lean','LeanPML/Rectangle/RegionalCoefficients.lean'],'scope':'现有红勾保留。准确包装同时携带原E/H与primitive u/E/Λ可导；推荐入口由光滑识别及μ非零生成空间证据，域内改写原系数，实际调用古典链。初值、PEC、强正则性仍需声明；未发布v0.5主定理。'},
 {'id':'regional-amplitude','page':7,'printed_page':7,'formula':'(5.2)–(5.3)：物理幅度域范围','kind':'note','draw':{'x':4,'top':638,'font_size':6,'lines':['对齐：幅度界','仅闭坐标区间','域外截回代表','积分 a.e. 一致']},'theorems':[R+'coefficients_eq_closed',R+'coefficients_ae',R+'weighted_memLp_iff',R+'fieldEnergy_eq_regional_integral',R+'fieldDissipation_eq_regional_integral'],'modules':['LeanPML/Rectangle/RegionalCoefficients.lean'],'scope':'假设范围说明，不给假设打完成勾。原p/r非负/幅度仅Icc坐标区间；内部截回代表与原场在闭矩形和体积分a.e.一致，权重/成员/能量耗散可积积分正式连接。保留全零、边层、角层，原技术延拓不需域外物理幅度界。'},
 {'id':'conservative-parameter-certificate','page':15,'printed_page':15,'formula':'§10参数例旁的本轮替代证书（原文未单列）','kind':'tick','draw':{'x':68,'top':526,'font_size':7,'lines':['对齐证书：C_P=4，K=384；c=1/16384，S=1/65536（保守 C_P=2Lx）。']},'theorems':[P+'unitSquare_parameter_certificate',P+'unitSquare_explicit_smallness',P+'unitSquare_le_threshold'],'modules':['LeanPML/Rectangle/ParameterCertificate.lean'],'scope':'只对本轮实际(-1,1)^2及ε=κ=τ=μ=1参数证书打勾：CP4、A3、K384；三条显式界依次3/2097152、9/16、3/2048≤1，并调用阈值等价。不是原(10.1)/(10.2)配置完成勾，不含二维剖面、初值族或解存在。'},
 {'id':'old-example-not-transferable','page':15,'printed_page':15,'formula':'(10.1)旧例与保守常数的区别','kind':'note','draw':{'x':68,'top':538,'font_size':6.5,'lines':['原(10.1)未沿用：在 K=384 下，旧 c=1/128 使 8cAK=72>1；这不否定原精确π常数例。']},'theorems':[P+'oldC_material_condition_value',P+'oldC_not_le_threshold'],'modules':['LeanPML/Rectangle/ParameterCertificate.lean'],'scope':'正式反证说明旧c不能迁移至本轮保守CP。保留原论文配置与全部原批注；原(5.1)精确π常数仍未证明。'}]
plan={'target':before['target'],'input_sha256':before['sha256'],'pages':18,'annotations_before':before['annotations'],'coordinate_system':'PDF点，左上原点；实际页序与印刷页码相同','entries':entries,'notes':[]}
(d/'layout_suggestions.json').write_text(json.dumps(plan,ensure_ascii=False,indent=2)+'\n')
# 沿用旧阶段经过结构检查的矢量叠加流程；新计划与新稳定ID，不覆盖旧备份。
s=(r/'logs/v0.4.4/pdf/annotate_pdf.py').read_text()
s=s.replace('v0.4已核验范围','v0.4对齐已核验范围').replace("folder=root/'logs/v0.4.4/pdf'","folder=root/'logs/v0.4_alignment/pdf'")
s=s.replace("root/'logs/v0.4.4/acceptance.json'","root/'logs/v0.4_alignment/verification.json'")
a=s.index("plan['entries'][7]");b=s.index("plan['editable']=True")
s=s[:a]+'''audittext=(root/accept['audit']).read_text()
for e in plan['entries']:
 e['source_hashes']={f:sha(root/f) for f in e['modules']}
 e['build_log']=accept['build'];e['audit_log']=accept['audit']
 for n in e['theorems']: assert "'"+n+"'" in audittext,(e['id'],n)
'''+s[b:]
s=s.replace("'LeanPML.v0.4.'","'LeanPML.v0.4_alignment.'").replace('同一v0.4稳定ID','同一v0.4_alignment稳定ID')
s=s.replace("==183","==195").replace("'old_annotations':183","'old_annotations':195")
s=s.replace("before_v0.4_","before_v0.4_alignment_").replace("annotated_v0.4_candidate","annotated_v0.4_alignment_candidate")
s=s.replace('LeanPML v0.4 已验证范围','LeanPML v0.4 对齐已验证范围').replace('LeanPML v0.4 范围说明','LeanPML v0.4 对齐范围说明')
s=s.replace('/LeanPMLV04MarkPlanSHA256','/LeanPMLV04AlignmentMarkPlanSHA256').replace('/LeanPMLV04Evidence','/LeanPMLV04AlignmentEvidence')
(d/'annotate_pdf.py').write_text(s)
print('已准备5项标注，修改页面3/4/7/15；仅1个新增红勾，用于独立保守参数证书。')
