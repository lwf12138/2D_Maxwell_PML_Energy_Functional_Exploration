from pathlib import Path
import json,hashlib,shutil,subprocess,datetime
p=Path.cwd();env=json.loads((p/'logs/v1.0.3/clean_environment.json').read_text());q=Path(env['root']);sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
checked={f:sha(p/f)==h==sha(q/f) for f,h in env['source_and_locks'].items()};assert all(checked.values()),checked
out=p/'logs/v1.0.3/clean';out.mkdir(exist_ok=True)
for f in (q/'logs/v1.0.3').iterdir():shutil.copy2(f,out/f.name)
for name in ['clean_build_console.txt','clean_audit_console.txt']:shutil.copy2(q/name,out/name)
commands=[]
for label in ['lake_build','axioms_audit','lean_version']:
 m=sorted(out.glob('*_'+label+'.json'))[-1];j=json.loads(m.read_text());assert j['exit_code']==0
 commands.append({'kind':label,'metadata':str(m.relative_to(p)),'log':str((out/j['output_file']).relative_to(p)),'actual_cwd':j['cwd'],'exit_code':j['exit_code'],'output_sha256':sha(out/j['output_file'])})
packages=[]
for pkg in env['dependencies']['packages']:
 path=p/'.lake/packages'/pkg['name'];head=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
 packages.append({'name':pkg['name'],'expected':pkg['rev'],'actual':head,'matches':head==pkg['rev']})
assert all(x['matches'] for x in packages)
audit=(p/commands[1]['log']).read_text();assert 'sorryAx' not in audit
r={'time':datetime.datetime.now().isoformat(),'engineering_status':'passed','mathematical_stages_complete':False,'root':str(q),'own_compilation_products_copied':False,'dependency_cache_reused':True,'not_a_cache_free_test':True,'source_and_lock_match':checked,'dependencies':packages,'commands':commands,'note':'完整 LeanPML/Audit 在隔离目录重建；当前未提交新文件均已复制，旧光滑回归仍参与。此通过不补足弱主定理缺口。'}
(p/'logs/v1.0.3/clean_result.json').write_text(json.dumps(r,ensure_ascii=False,indent=2));print(json.dumps({'status':'passed','files_matched':len(checked),'dependencies':len(packages),'commands':commands},ensure_ascii=False,indent=2))
