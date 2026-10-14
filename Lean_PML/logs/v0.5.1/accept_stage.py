from pathlib import Path
from datetime import datetime
import sys,json,hashlib,re
root=Path.cwd();stage,build,audit,*extra=sys.argv[1:];out=root/'logs'/stage;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
baseline=json.loads((root/'logs/v0.5.1/baseline.json').read_text())
protected=['lean-toolchain','lakefile.toml','lake-manifest.json','ROADMAP_lean_PML_revised.md','docs/model_contract.md','docs/scope.md','../results/V7_Maxwell_Debye_PML/V7_global_energy.md','../results/V7_Maxwell_Debye_PML/V7_global_energy.tex','../results/V7_Maxwell_Debye_PML/V7_global_energy.pdf','../results/V7_Maxwell_Debye_PML/proof_audit.md']
for f in protected:assert sha(root/f)==baseline['hashes'][f],f
for f in [build,audit]+extra:
 m=json.loads((root/f).with_suffix('.json').read_text());assert m['status']=='finished' and m['exit_code']==0,f
sources={};pending=['LeanPML.lean','Audit.lean']
while pending:
 f=pending.pop()
 if f in sources:continue
 path=root/f;assert path.exists(),f;sources[f]=sha(path)
 for mod in re.findall(r'^import (LeanPML(?:\.[\w]+)*)\s*$',path.read_text(),re.M):pending.append(mod.replace('.','/')+'.lean')
def strip_comments(src):
 out=[];i=0;depth=0
 while i<len(src):
  if src[i:i+2]=='/-':depth+=1;i+=2
  elif depth and src[i:i+2]=='-/':depth-=1;i+=2
  elif depth:i+=1
  elif src[i:i+2]=='--':
   j=src.find('\n',i);i=len(src) if j<0 else j
  else:out.append(src[i]);i+=1
 return ''.join(out)
for f in sources:assert not re.search(r'\b(sorry|admit|axiom)\b',strip_comments((root/f).read_text())),f
text=(root/audit).read_text();assert 'sorryAx' not in text
axioms=sorted({x.strip() for a in re.findall(r'depends on axioms: \[(.*?)\]',text,re.S) for x in a.split(',')})
assert set(axioms)<={'propext','Classical.choice','Quot.sound'},axioms
old=(root/'logs/v0.5.1/initial_files/Audit.lean').read_text();assert (root/'Audit.lean').read_text().startswith(old)
failed=[]
for f in sorted(out.glob('*.json')):
 try:m=json.loads(f.read_text())
 except:continue
 if isinstance(m,dict) and m.get('status')=='finished' and m.get('exit_code',0)!=0:failed.append(str(f.relative_to(root)))
record={'stage':stage,'status':'passed','time':datetime.now().astimezone().isoformat(),'build':build,'audit':audit,'additional_checks':extra,'build_exit_code':0,'audit_exit_code':0,'sources':sources,'protected':{f:sha(root/f) for f in protected},'audited_declarations':len(re.findall(r"'[^']+' (?:depends on axioms:|does not depend on any axioms)",text)),'axioms':axioms,'sorryAx':False,'source_placeholder_scan':'passed','legacy_audit_preserved':True,'retained_failures':failed,'mathematical_scope':{'v0.5.1':'所选强光滑兼容类的具体原模型全域先验能量定理；保守CP=2Lx','v0.5.2':'精确参数、C∞全域吸收剖面及非零兼容初始数据；非一般解存在','v0.5.3':'全部退化分支、非零静态显式解、任意初值增长族及受限错误主张回归'}[stage],'regularity_inputs':['联合C∞技术延拓','C(K)一致范数时间连续可微','实际加权成员与路径连续可微','原历史识别','PEC、初始五兼容、初始零区和T=0图状态兼容'],'not_claimed':['完整V7弱空间范围','精确π常数','加权正则性自动传播','提升规范唯一性','一般解存在唯一性','一般严格/指数衰减']}
(out/'acceptance.json').write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k not in ['sources','protected']},ensure_ascii=False,indent=2))
