from pathlib import Path
import json,subprocess,hashlib
p=Path.cwd();folder=p/'logs/v1.0.3/pdf';target=p.parent/'results/V7_Maxwell_Debye_PML/V7_global_energy_副本.pdf'
bin='/Users/wcli/.cache/codex-runtimes/codex-primary-runtime/dependencies/bin/override/pdftoppm'
records=[]
for n in [7,8,11]:
 prefix=folder/f'page_{n}'
 cmd=[bin,'-f',str(n),'-l',str(n),'-r','135','-png','-singlefile',str(target),str(prefix)]
 r=subprocess.run(cmd,capture_output=True,text=True);print(json.dumps({'command':cmd,'exit_code':r.returncode,'stdout':r.stdout,'stderr':r.stderr},ensure_ascii=False));assert r.returncode==0
 records.append({'page':n,'image':str(prefix.with_suffix('.png')),'command':cmd,'exit_code':r.returncode})
(folder/'render_record.json').write_text(json.dumps({'pdf_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'pages':records},ensure_ascii=False,indent=2))
