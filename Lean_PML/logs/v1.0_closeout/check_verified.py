from pathlib import Path
import json,hashlib,re,datetime
root=Path.cwd();folder=root/'logs/v1.0_closeout';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
commands={}
for label in ['lake_build','axioms_audit','type_review']:
 files=sorted(folder.glob('*_'+label+'.json'));meta=json.loads(files[-1].read_text());assert meta['exit_code']==0,(label,meta)
 commands[{'axioms_audit':'audit','lake_build':'build','type_review':'types'}[label]]={'metadata':str(files[-1].relative_to(root)),'log':str(files[-1].with_suffix('.log').relative_to(root)),'exit_code':0}
audit=(root/commands['audit']['log']).read_text();assert 'sorryAx' not in audit
new=json.loads((folder/'new_declarations.json').read_text());assert all("'"+n+"'" in audit for n in new)
sources=json.loads((folder/'source_snapshot.json').read_text());assert all(sha(root/f)==h for f,h in sources.items())
base=json.loads((folder/'baseline.json').read_text())
newfiles=[f for f in sources if f not in base['formal_hashes'] and f.endswith('.lean')]
for f in newfiles:
 text=(root/f).read_text();assert not re.search(r'\b(sorry|admit|axiom)\b',text),f
result={'engineering_checks_passed':True,'V7_full_alignment':False,'time':datetime.datetime.now().isoformat(),'sources':sources,'commands':commands,'new_declarations':new,'new_files':newfiles,'audit_declarations':len(re.findall(r"depends on axioms|does not depend on any axioms",audit)),'remaining':['W1∞ continuous representative','sharp Poincare constant','operator exponential to scalar pointwise multiplier']}
(folder/'verification_before_pdf.json').write_text(json.dumps(result,ensure_ascii=False,indent=2))
print(json.dumps({k:v for k,v in result.items() if k not in ['sources','new_declarations']},ensure_ascii=False,indent=2))
