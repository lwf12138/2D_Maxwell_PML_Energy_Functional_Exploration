from pathlib import Path
import json,subprocess
from concurrent.futures import ThreadPoolExecutor
folder=Path(__file__).resolve().parent
info=json.loads((folder/'inspection.json').read_text());result=json.loads((folder/'annotation_result.json').read_text())
tool='/Users/wcli/.cache/codex-runtimes/codex-primary-runtime/dependencies/bin/override/pdftoppm'
commands=[]
def run(n):
 args=[tool,'-f',str(n),'-l',str(n),'-r','120','-png','-singlefile',info['target'],str(folder/f'final_page_{n:02}')]
 p=subprocess.run(args,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 return {'page':n,'command':args,'cwd':str(Path.cwd()),'exit_code':p.returncode,'output':p.stdout.decode()}
with ThreadPoolExecutor(max_workers=3) as pool:commands=list(pool.map(run,result['modified_pages']))
(folder/'render_commands.json').write_text(json.dumps(commands,ensure_ascii=False,indent=2))
assert all(c['exit_code']==0 for c in commands)
print('rendered',result['modified_pages'])
