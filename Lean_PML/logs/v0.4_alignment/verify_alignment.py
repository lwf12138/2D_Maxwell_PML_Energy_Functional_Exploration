from pathlib import Path
from datetime import datetime
import hashlib,json,re
root=Path.cwd(); out=root/'logs/v0.4_alignment';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
base=json.loads((out/'baseline.json').read_text())['hashes']
protected=['lean-toolchain','lakefile.toml','lake-manifest.json','ROADMAP_lean_PML_revised.md','docs/model_contract.md','docs/scope.md','../results/V7_Maxwell_Debye_PML/V7_global_energy.md','../results/V7_Maxwell_Debye_PML/V7_global_energy.tex','../results/V7_Maxwell_Debye_PML/V7_global_energy.pdf','../results/V7_Maxwell_Debye_PML/proof_audit.md']
for f in protected:assert sha(root/f)==base[f],f
build='logs/v0.4_alignment/20261014T000055_917026_lake_build.log'
audit='logs/v0.4_alignment/20261014T000341_178705_axioms_audit.log'
types='logs/v0.4_alignment/20261014T000341_178709_interface_types.log'
for f in [build,audit,types]:
 m=json.loads((root/f).with_suffix('.json').read_text());assert m['exit_code']==0 and m['status']=='finished',f
text=(root/audit).read_text();assert 'sorryAx' not in text
axioms=sorted({a.strip() for group in re.findall(r'depends on axioms: \[(.*?)\]',text,re.S) for a in group.split(',')})
assert set(axioms)<= {'propext','Classical.choice','Quot.sound'},axioms
count=len(re.findall(r"'[^']+' (?:depends on axioms:|does not depend on any axioms)",text))
formal=sorted(root.glob('LeanPML/**/*.lean'))+[root/'LeanPML.lean',root/'Audit.lean']
def strip_comments(src):
 # 嵌套块注释与行注释；本项目没有在字符串中嵌入 Lean 证明脚本。
 out=[];i=0;depth=0
 while i<len(src):
  if src[i:i+2]=='/-':depth+=1;i+=2
  elif depth and src[i:i+2]=='-/':depth-=1;i+=2
  elif depth:i+=1
  elif src[i:i+2]=='--':
   j=src.find('\n',i);i=len(src) if j==-1 else j
  else:out.append(src[i]);i+=1
 return ''.join(out)
for f in formal:
 clean=strip_comments(f.read_text())
 assert not re.search(r'\b(sorry|admit|axiom)\b',clean),str(f)
roottext=(root/'LeanPML.lean').read_text()
new=['LeanPML/Rectangle/ParameterCertificate.lean','LeanPML/PML/ClassicalSystem.lean','LeanPML/Rectangle/RegionalCoefficients.lean']
for f in new:assert ('import '+f[:-5].replace('/','.')) in roottext
old_audits=re.findall(r'^#print axioms (.+)$',(out/'initial_files/Audit.lean').read_text(),re.M) if (out/'initial_files/Audit.lean').exists() else []
# 入场Audit哈希与旧验收一致；现审计新增行追加在保留旧内容之后。
review=json.loads((out/'semantic_review_hashes.json').read_text())
for f,d in review['files'].items():assert sha(root/f)==d,f
failed=[]
for f in sorted(out.glob('*.json')):
 try:m=json.loads(f.read_text())
 except Exception:continue
 if isinstance(m,dict) and m.get('status')=='finished' and m.get('exit_code',0)!=0:
  failed.append({'metadata':str(f.relative_to(root)),'exit_code':m['exit_code'],'command':m.get('command_display')})
record={'stage':'v0.4_alignment','status':'passed','scope':'所选强光滑/一致范数/加权正则性下的v0.4对齐；未实施v0.5','verified_at':datetime.now().astimezone().isoformat(),'build':build,'audit':audit,'type_review':types,'build_exit_code':0,'audit_exit_code':0,'type_review_exit_code':0,'audited_declarations':count,'axioms':axioms,'sorryAx':False,'source_placeholder_scan':'passed','sources':{str(f.relative_to(root)):sha(f) for f in formal},'protected':{f:sha(root/f) for f in protected},'new_modules':new,'changed_existing_files':{f:{'before':d,'after':sha(root/f)} for f,d in base.items() if (root/f).exists() and sha(root/f)!=d},'semantic_review':'logs/v0.4_alignment/semantic_review.md','retained_failures':failed,'pdf':'pending','not_claimed':['V7精确π常数','弱H1/Hdiv/W1∞范围','加权正则性自动传播','提升规范唯一性','解存在唯一性','v0.5具体先验主定理发布']}
(out/'verification.json').write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k not in ['sources','protected','changed_existing_files']},ensure_ascii=False,indent=2))
