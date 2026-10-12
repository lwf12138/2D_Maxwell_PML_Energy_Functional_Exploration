"""核对 v0.2.4 的固定来源、正式导入、公理审计与交付记录；不运行新的数学测试。"""
from pathlib import Path
import hashlib,json,re,subprocess
root=Path.cwd()
folder=root/'logs/v0.2.4'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
before=json.loads((folder/'before_hashes.json').read_text())
protected=['lean-toolchain','lakefile.toml','lake-manifest.json','ROADMAP_lean_PML_revised.md',
'docs/model_contract.md','docs/scope.md','docs/source_inventory.md']
protected += ['../results/V7_Maxwell_Debye_PML/V7_global_energy'+ext for ext in ['.md','.tex','.pdf']]
for n in protected:
    assert sha(root/n)==before[n],('protected file changed',n)
build='20261011T231924_138774_lake_build'
audit='20261011T231954_467990_axioms_audit'
for stem in [build,audit]:
    meta=json.loads((folder/(stem+'.json')).read_text())
    assert meta['exit_code']==0 and meta['status']=='finished'
    assert meta['cwd']==str(root)
    assert (folder/(stem+'.log')).exists()
out=(folder/(audit+'.log')).read_text()
axioms=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",out)
assert len(axioms)==154 and len({n for n,_ in axioms})==154
assert 'sorryAx' not in out
allowed={'propext','Classical.choice','Quot.sound'}
assert all(set(x.strip() for x in a.split(',') if x.strip())<=allowed for _,a in axioms)
module=root/'LeanPML/PML/Obstructions/SingleLayer.lean'
source=module.read_text()
decls=re.findall(r'^theorem (\w+)',source,re.M)
assert len(decls)==20
for name in decls:
    fullname='LeanPML.PML.Obstructions.'+name
    assert fullname in dict(axioms)
    assert fullname in (root/'docs/single_layer_failure.md').read_text()
entry=(root/'LeanPML.lean').read_text()
assert 'import LeanPML.PML.Obstructions.SingleLayer' in entry
imports=re.findall(r'^import (LeanPML\.\S+)',entry,re.M)
assert len(imports)==12
for path in (root/'LeanPML').rglob('*.lean'):
    code=re.sub(r'/\-.*?\-/', '',path.read_text(),flags=re.S)
    code=re.sub(r'--[^\n]*','',code)
    assert not re.search(r'\b(?:sorry|admit|axiom)\b',code),path
old_audit=(folder/'before_Audit.lean').read_text()
assert (root/'Audit.lean').read_text().startswith(old_audit)
assert not (root/'docs/v0.2.4_reading_guide.md').exists()
assert not (root/'LeanPML/PML/State.lean').exists()
assert not (root/'LeanPML/PML/Energy.lean').exists()
expected_mathlib='fabf563a7c95a166b8d7b6efca11c8b4dc9d911f'
commit=subprocess.check_output(['git','-C','.lake/packages/mathlib','rev-parse','HEAD'],text=True).strip()
assert commit==expected_mathlib
plan=json.loads((folder/'pdf/annotation_plan.json').read_text())
verification=json.loads((folder/'pdf/verification.json').read_text())
assert verification['page_count']==18 and verification['new_red_ticks']==4
assert verification['old_annotations']==135 and verification['total_annotations']==141
assert verification['old_annotations_preserved']
assert verification['visual_review']!='pending'
target=Path(plan['backup']['target'])
assert sha(target)==verification['sha256_after']
for e in plan['entries']:
    assert sha(root/e['module'])==e['source_sha256']
    assert all(n in dict(axioms) for n in e['theorems'])
# 文件链接检查；最后报告本身即将创建，允许文档预先链接该报告。
docs=['README.md','PROGRESS.md','docs/single_layer_failure.md','docs/theorem_inventory.md','docs/pdf_formalization_marks.md']
checked_links=0
for name in docs:
    path=root/name
    text=path.read_text()
    assert '最终构建/审计记录尚待补入' not in text
    # 数学 F[U](0) 不是 Markdown 链接；先去掉数学与行内代码再检查。
    prose=re.sub(r'\$\$.*?\$\$|\$[^$\n]*\$|`[^`\n]*`','',text,flags=re.S)
    for link in re.findall(r'\[[^\]\n]+\]\(([^)]+)\)',prose):
        link=link.strip('<>').split('#')[0]
        if not link or '://' in link or link.startswith('mailto:'): continue
        link=re.sub(r':\d+$','',link)  # 可点击源码链接允许末尾行号。
        candidate=(path.parent/link)
        if candidate.resolve()==(folder/'final_checks.json').resolve(): continue
        assert candidate.exists(),(name,link)
        checked_links+=1
result={'stage':'v0.2.4','status':'passed','protected_files':protected,
'new_definitions':len(re.findall(r'^noncomputable def ',source,re.M)),
'new_theorems':decls,'formal_modules':imports,'total_audited':154,
'axioms':sorted(allowed),'sorryAx':False,'mathlib_commit':commit,
'source_sha256':sha(module),'build':build,'audit':audit,
'pdf_sha256':sha(target),'pdf_pages':18,'new_red_ticks':4,'old_annotations_preserved':135,
'visual_review':verification['visual_review'],'checked_local_links':checked_links,
'no_v031_implementation':True}
(folder/'final_checks.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(result,ensure_ascii=False,indent=2))
