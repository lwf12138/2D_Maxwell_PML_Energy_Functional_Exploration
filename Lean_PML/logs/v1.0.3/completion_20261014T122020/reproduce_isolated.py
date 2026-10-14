from pathlib import Path
import subprocess,json,hashlib,datetime,shutil,tempfile
root=Path.cwd();stamp=datetime.datetime.now().strftime('%Y%m%dT%H%M%S');folder=root/'logs/v1.0.3'/('completion_'+stamp);folder.mkdir()
(root/'logs/v1.0.3/current_completion_path.txt').write_text(str(folder.relative_to(root))+'\n')
formal=list((root/'LeanPML').rglob('*.lean'))+[root/'LeanPML.lean',root/'Audit.lean']
configs=[root/n for n in ['lean-toolchain','lakefile.toml','lake-manifest.json']]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source={str(p.relative_to(root)):sha(p) for p in formal+configs if p.exists()}
(folder/'source_snapshot.json').write_text(json.dumps(source,ensure_ascii=False,indent=2))
commands=[]
for stage,label,args in [('v1.0.2','lake_build',['lake','build']),('v1.0.2','axioms_audit',['lake','env','lean','Audit.lean']),('v1.0.3','axioms_audit',['lake','env','lean','Audit.lean'])]:
 start=set((root/'logs'/stage).glob('*.json'))
 code=subprocess.call(['python3','scripts/run_logged.py','--stage',stage,label,*args],cwd=root)
 new=set((root/'logs'/stage).glob('*.json'))-start
 commands.append({'stage':stage,'label':label,'exit_code':code,'metadata':[str(p.relative_to(root)) for p in new]})
 (folder/'checks.json').write_text(json.dumps(commands,ensure_ascii=False,indent=2))
 if code:raise SystemExit(code)
# 隔离目录不拷贝本工程任何 .lake/build；只链接精确版本依赖缓存。
isolated=Path(tempfile.mkdtemp(prefix='LeanPML_v1_final_')); (isolated/'scripts').mkdir();(isolated/'.lake').mkdir()
for src in formal+configs+[root/'scripts/run_logged.py']:
 if not src.exists():continue
 dest=isolated/src.relative_to(root);dest.parent.mkdir(exist_ok=True,parents=True);shutil.copy2(src,dest)
(isolated/'.lake/packages').symlink_to((root/'.lake/packages').resolve(),target_is_directory=True)
assert not (isolated/'.lake/build').exists()
meta={'directory':str(isolated),'dependency_cache':str((root/'.lake/packages').resolve()),'own_build_artifacts_copied':False,'source_hashes':source,'cache_note':'复用原工程精确依赖缓存；本工程正式模块从零构建，并非完全无缓存测试。'}
(folder/'isolated_setup.json').write_text(json.dumps(meta,ensure_ascii=False,indent=2))
assert all(sha(isolated/f)==h for f,h in source.items())
for label,args in [('environment',['lake','env','lean','--version']),('lake_environment',['lake','--version']),('isolated_lake_build',['lake','build']),('isolated_axioms_audit',['lake','env','lean','Audit.lean'])]:
 code=subprocess.call(['python3','scripts/run_logged.py','--stage','v1.0.3',label,*args],cwd=isolated)
 shutil.copytree(isolated/'logs/v1.0.3',folder/'isolated_logs',dirs_exist_ok=True)
 if code:raise SystemExit(code)
meta.update(exit_code=0,source_still_matches=all(sha(root/f)==h for f,h in source.items()),finished_at=datetime.datetime.now().isoformat())
(folder/'isolated_result.json').write_text(json.dumps(meta,ensure_ascii=False,indent=2))
print('FINAL_EVIDENCE',folder)
