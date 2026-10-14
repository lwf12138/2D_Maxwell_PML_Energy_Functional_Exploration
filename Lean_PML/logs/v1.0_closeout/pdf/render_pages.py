from pathlib import Path
import subprocess,json
folder=Path('logs/v1.0_closeout/pdf');d=json.loads((folder/'annotation_result.json').read_text());p=Path(json.loads((folder/'inspection.json').read_text())['target'])
exe='/Users/wcli/.cache/codex-runtimes/codex-primary-runtime/dependencies/bin/override/pdftoppm'
records=[]
for page in d['modified_pages']:
 args=[exe,'-f',str(page),'-l',str(page),'-scale-to','1500','-png','-singlefile',str(p),str(folder/f'page_{page}_final')]
 r=subprocess.run(args,capture_output=True,text=True);records.append(dict(command=args,cwd=str(Path.cwd()),exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr));assert r.returncode==0
(folder/'render_log.json').write_text(json.dumps(records,ensure_ascii=False,indent=2))
