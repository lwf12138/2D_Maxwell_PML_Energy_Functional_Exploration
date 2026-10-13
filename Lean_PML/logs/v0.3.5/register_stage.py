"""将已完成模块接入默认构建与审计；只用于本轮两个阶段。"""
from pathlib import Path
import re,json,sys
root=Path.cwd();stage=sys.argv[1]
files={'v0.3.4':['GradientControl'],'v0.3.5':['DissipationClosure','MainAbstract']}[stage]
entry=root/'LeanPML.lean';text=entry.read_text()
for name in files:
 imp='import LeanPML.PML.'+name
 if imp not in text:text=text.replace('\n/-!', '\n'+imp+'\n\n/-!',1)
entry.write_text(text)
audit=root/'Audit.lean';text=audit.read_text();entries=[]
for name in files:
 file=root/'LeanPML/PML'/(name+'.lean')
 for m in re.finditer(r'^(?:@\[[^\]]+\]\s*)?theorem\s+([\w.]+)',file.read_text(),re.M):
  fullname='LeanPML.PML.'+m.group(1)
  entries.append({'name':fullname,'file':str(file.relative_to(root)),'line':file.read_text()[:m.start()].count('\n')+1})
  line='#print axioms '+fullname
  if line not in text.splitlines():text+='\n'+line
text+='\n';audit.write_text(text)
(root/'logs'/stage/'new_theorems.json').write_text(json.dumps(entries,ensure_ascii=False,indent=2))
print(json.dumps({'stage':stage,'files':files,'new_theorems':len(entries)},ensure_ascii=False,indent=2))
