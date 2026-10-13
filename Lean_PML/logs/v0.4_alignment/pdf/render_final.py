from pathlib import Path
import json,subprocess
r=Path.cwd();d=r/'logs/v0.4_alignment/pdf'; plan=json.loads((d/'annotation_plan.json').read_text())
renderer='/Users/wcli/.cache/codex-runtimes/codex-primary-runtime/dependencies/bin/override/pdftoppm'
outputs=[]
for n in plan['modified_pages']:
 prefix=d/f'final-{n:02}'
 cmd=[renderer,'-f',str(n),'-l',str(n),'-r','144','-png','-singlefile',plan['target'],str(prefix)]
 print('RUN',cmd,flush=True);subprocess.run(cmd,check=True);outputs.append(str(prefix.with_suffix('.png')))
(d/'render_record.json').write_text(json.dumps({'rendered_pages':plan['modified_pages'],'dpi':144,'files':outputs},ensure_ascii=False,indent=2)+'\n')
print('全部修改页已从最终PDF重新打开并渲染。')
