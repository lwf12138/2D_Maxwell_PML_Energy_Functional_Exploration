from pathlib import Path
import json,hashlib,re,sys
root=Path.cwd();stage=sys.argv[1];folder=root/'logs'/stage
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def latest(label):
    found=[]
    for p in folder.glob('*_'+label+'.json'):
        m=json.loads(p.read_text())
        if m.get('exit_code')==0 and m.get('status')=='finished':found.append(p)
    assert found,label
    return sorted(found)[-1]
build=latest('lake_build');audit=latest('axioms_audit')
output=audit.with_suffix('.log').read_text()
assert 'sorryAx' not in output
names=re.findall(r"'([^']+)' depends on axioms",output)
axioms={x.strip() for s in re.findall(r'depends on axioms: \[([^\]]*)\]',output) for x in s.split(',') if x.strip()}
assert axioms<={'propext','Classical.choice','Quot.sound'}
new=json.loads((folder/'new_theorems.json').read_text())
assert {t['name'] for t in new}<=set(names)
files=sorted({t['file'] for t in new})
for f in files:
    src=(root/f).read_text()
    assert not re.search(r'\b(sorry|admit)\b|^\s*axiom\b',src,re.M),f
    assert 'import '+f.removesuffix('.lean').replace('/','.') in (root/'LeanPML.lean').read_text()
protected=json.loads((root/'logs/v0.3.4/source_snapshot.json').read_text())['protected']
for f,h in protected.items():assert sha(root/f)==h,f
report=dict(stage=stage,mathematics='passed within explicitly conditional spatial interfaces',
 build=str(build.with_suffix('.log').relative_to(root)),audit=str(audit.with_suffix('.log').relative_to(root)),
 build_exit_code=0,audit_exit_code=0,new_public_theorems=len(new),audited_declarations=len(names),
 axioms=sorted(axioms),sorryAx=False,sources={f:sha(root/f) for f in files},
 root_sha256=sha(root/'LeanPML.lean'),audit_sha256=sha(root/'Audit.lean'),protected_files_unchanged=True,
 remaining=['concrete rectangle Green, trace, Poincare, time-space commutation','original eight-variable PDE equivalence and lift uniqueness','existence and uniqueness; strict decay'],
 endpoint_scope='Derivative and quantitative dissipation bound on interior; static bounds, antitonicity and FTC balance on closed interval; T=0 permitted',
 assumption_review='No target gradient bound, dissipation sign, derivative sign, monotonicity or balance in input fields; explicit common-trace Poincare and original primitive/same-source conditions')
(folder/'acceptance.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(report,ensure_ascii=False,indent=2))
