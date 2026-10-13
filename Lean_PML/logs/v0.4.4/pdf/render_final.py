from pathlib import Path
import json,subprocess
root=Path.cwd();folder=root/'logs/v0.4.4/pdf'
plan=json.loads((folder/'annotation_plan.json').read_text())
for page in plan['modified_pages']:
    cmd=['/Users/wcli/.cache/codex-runtimes/codex-primary-runtime/dependencies/bin/override/pdftoppm','-f',str(page),'-l',str(page),'-r','150','-singlefile','-png',plan['backup']['target'],str(folder/f'after-{page}')]
    print(json.dumps({'cwd':str(root),'command':cmd},ensure_ascii=False),flush=True)
    result=subprocess.run(cmd,check=False)
    print('exit_code:',result.returncode,flush=True)
    result.check_returncode()
