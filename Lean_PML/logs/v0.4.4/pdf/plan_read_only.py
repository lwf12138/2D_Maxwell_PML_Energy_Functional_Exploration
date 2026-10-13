from pathlib import Path
import json
import pdfplumber
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
p=Path.cwd();folder=p/'logs/v0.4.4/pdf'
source=json.loads((folder/'read_only_inspection.json').read_text())
def entry(id,page,formula,kind,x,top,lines,names,scope):
 return dict(id=id,page=page,printed_page=page,formula=formula,kind=kind,draw=dict(x=x,top=top,font_size=6,lines=lines),theorems=names,scope=scope,status='只读建议；最终构建和审计后由主代理决定是否采用')
ns='LeanPML.PML.Concrete.';nr='LeanPML.Rectangle.'
entries=[
entry('v04-original-recovery',3,'(2.1)','tick',535,610,['光滑 primitive','重构核验','八条方程'],[ns+'original_reconstruct_at',ns+'primitive_to_original_rectangle'],'八条方程为原解输入；勾仅表示从光滑 primitive 重构的满足性，非解存在。'),
entry('v04-historical-lift',4,'(2.3)','tick',535,126,['历史提升','初值与求导'],[ns+'integralLift_initial',ns+'hasDerivAt_integralLift',nr+'toL2_integralLift_on_Icc'],'真实点态时间积分初值、内部求导；C(K) 连续正则性下与 L² Bochner 历史积分相等。定义本身不计证明。'),
entry('v04-five-invariants',4,'(2.4)','tick',4,188,['五个时间','不变量','光滑场版'],[ns+'five_invariants_on_Icc',ns+'five_invariants_toLp_eq_of_continuous'],'从原八式、真实历史提升及混合微分推出任意初始不变量场的保持；实际 L² 表示一致。旧三个点态批注保留。'),
entry('v04-compatibility',4,'(2.5)','tick',4,409,['初始兼容','保持与重构','光滑场版'],[ns+'compatible_lift_on_Icc',ns+'reconstruct_lift_eqOn'],'仅初始五不变量为零作输入，推出全区间兼容及四辅助量重构；不是零解。'),
entry('v04-equivalence',4,'(2.6)、命题 2.1','tick',535,489,['双向八方程','光滑类','固定初始','原函数'],[ns+'original_to_primitive_rectangle',ns+'primitive_to_original_rectangle',ns+'lift_reconstruct_eqOn'],'所选光滑类，固定初始原函数；包含反向四辅助方程。无解存在唯一性或提升规范唯一性结论。'),
entry('v04-poincare-conservative',7,'(5.1)','note',535,594,['v0.4 保守版','C_P = 2Lx','非原精确值'],[nr+'poincare_estimate',nr+'scaleK_rectangle'],'已证明同一迹核上的 CP=2Lx，从而 K=32μ(ε+2κ)Lx²；未证明原文精确 π 常数，无完成勾。'),
entry('v04-zero-region',8,'§5.2 五不变量保持段后的零区保持（未编号）','tick',4,470,['原场零区','保持','须初始φ=0'],[ns+'original_zero_region_preserved'],'从原方程、历史提升、五初始兼容及零区 φ₀=0 推出 φ=0；保留一般空间区域，不声称(5.7)/(5.8)传播。'),
entry('v04-regularity-input',10,'(6.6)','note',4,121,['v0.4 输入','光滑/加权','正则性','非自动传播'],[nr+'hasDerivAt_L2_of_pointwise',nr+'hasDerivAt_weighted_smooth'],'选用 C∞ 空间延拓、C(K) 的统一时间正则性及实际加权路径可微作为强于 V7 弱类的条件；已证明到普通/加权路径导数的连接。假设不打勾。'),
entry('v04-weighted-recovery',11,'(7.2) 后加权链式法则说明（未编号）','tick',535,201,['加权路径','真实场恢复','需加权可导'],[nr+'weighted_smooth_recovery',nr+'hasDerivAt_weighted_smooth'],'实际加权坐标恢复为所选光滑辅助场，普通 L² 导数由真实 C(K) 路径识别；加权范数正则性仍是输入，非自动传播。'),
entry('v04-green',11,'(7.5)','tick',4,613,['矩形光滑','四边 Green','两层 PEC','边界消去'],[nr+'green_L2',nr+'greenDomain',nr+'boundary_multiplier_zero',nr+'twoLayer_zeroBoundary'],'真实全矩形四边公式，右−左+上−下；真实提升、PEC、初值零迹及 T=0 图迹兼容下两层边界消失。弱 H₀¹–H(div) Green 未证明。')]
notes=[dict(id='v04-history-note4',page=4,printed_page=4,kind='note',draw=dict(x=68,top=48,font_size=6,lines=['v0.4：光滑场层结果；旧点态批注保留历史范围。下列勾不表示解存在或完整弱空间结论。'])),dict(id='v04-history-note11',page=11,printed_page=11,kind='note',draw=dict(x=68,top=48,font_size=6,lines=['v0.4：矩形光滑 Green 与真实微分交换已接通；旧“待完成”批注保留历史，弱空间仍未完成。']))]
draft=dict(target=source['target'],input_sha256=source['sha256'],pages=18,annotations_before=183,editable=False,coordinate_system='PDF点，左上原点；page为1起始实际页序，本轮均等于印刷页码',entries=entries,notes=notes)
(folder/'layout_suggestions.json').write_text(json.dumps(draft,ensure_ascii=False,indent=2))
pdfmetrics.registerFont(TTFont('QAChinese','/System/Library/Fonts/Supplemental/Arial Unicode.ttf'))
boxes=[];errors=[]
with pdfplumber.open(source['target'])as pdf:
 for e in entries+notes:
  d=e['draw'];fs=d['font_size'];tick=e['kind']=='tick';tx=d['x']+(15 if tick else 0)
  width=max(pdfmetrics.stringWidth(s,'QAChinese',fs)for s in d['lines'])
  box=[d['x']-1,d['top']-2,tx+width+1,d['top']+fs+(len(d['lines'])-1)*(fs+2.2)+2]
  boxes.append(dict(id=e['id'],page=e['page'],rect_top=box));x0,y0,x1,y1=box
  if not(0<=x0<x1<595.28 and 0<=y0<y1<841.89):errors.append({'id':e['id'],'outside':box})
  chars=[c['text']for c in pdf.pages[e['page']-1].chars if c['text'].strip()and c['x0']<x1 and c['x1']>x0 and c['top']<y1 and c['bottom']>y0]
  if chars:errors.append(dict(id=e['id'],overlap=chars,box=box))
  for a in source['annotations']:
   if a['page']!=e['page']:continue
   ax0,ay0,ax1,ay1=json.loads(a['/Rect']);atop=841.89-ay1;abot=841.89-ay0
   if ax0<x1 and ax1>x0 and atop<y1 and abot>y0:errors.append(dict(id=e['id'],annotation=a['/NM'],existing_rect=a['/Rect']))
for i,a in enumerate(boxes):
 for b in boxes[i+1:]:
  if a['page']!=b['page']:continue
  x0,y0,x1,y1=a['rect_top'];u0,v0,u1,v1=b['rect_top']
  if x0<u1 and x1>u0 and y0<v1 and y1>v0:errors.append(dict(new_overlap=[a['id'],b['id']]))
(folder/'suggestion_preflight.json').write_text(json.dumps(dict(boxes=boxes,errors=errors),ensure_ascii=False,indent=2))
print(json.dumps(dict(errors=errors,entries=len(entries),notes=len(notes)),ensure_ascii=False,indent=2))
