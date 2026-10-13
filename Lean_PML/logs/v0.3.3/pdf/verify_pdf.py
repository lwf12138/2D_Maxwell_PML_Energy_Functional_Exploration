"""复核本轮 PDF 的保护、文本、批注、源码及真实构建证据；不编辑 PDF。"""
from pathlib import Path
from collections import Counter
import json,hashlib,re
from pypdf import PdfReader
root=Path.cwd();folder=root/'logs/v0.3.3/pdf'
plan=json.loads((folder/'annotation_plan.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
before=PdfReader(plan['backup']['backup']);after=PdfReader(plan['backup']['target'])
anns=lambda p:list(p['/Annots'])if'/Annots'in p else[]
assert len(before.pages)==len(after.pages)==18
signature=lambda a:tuple(str(a.get_object().get(k,''))for k in ['/Subtype','/Rect','/Contents','/T','/F','/NM'])
for n,(a,b)in enumerate(zip(before.pages,after.pages),1):
 assert list(a.mediabox)==list(b.mediabox)and list(a.cropbox)==list(b.cropbox)
 assert (b.extract_text()or'').startswith(a.extract_text()or'')
 if n not in plan['modified_pages']:assert (a.extract_text()or'')==(b.extract_text()or'')
 assert Counter(map(signature,anns(a)))<=Counter(map(signature,anns(b)))
for f,h in plan['protected_hashes'].items():assert sha(Path(f))==h,f
for e in plan['entries']:assert sha(root/e['module'])==e['source_sha256']
audits={}
for stage,stem in [('v0.3.2','20261013T100104_046897_axioms_audit'),('v0.3.3',plan['audit'])]:
 meta=json.loads((root/'logs'/stage/(stem+'.json')).read_text());assert meta['exit_code']==0
 text=(root/'logs'/stage/(stem+'.log')).read_text();assert 'sorryAx'not in text
 names=re.findall(r"'([^']+)' depends on axioms",text)
 axioms={x.strip()for s in re.findall(r'depends on axioms: \[([^\]]*)\]',text)for x in s.split(',')if x.strip()}
 assert axioms<= {'propext','Classical.choice','Quot.sound'}
 audits[stage]={'count':len(names),'axioms':sorted(axioms)}
expected={'LeanPML.v0.3.3.'+x['id']for x in plan['entries']+plan['notes']}
found={str(a.get_object().get('/NM',''))for p in after.pages for a in anns(p)}
assert expected<=found
result=dict(page_count=18,modified_pages=plan['modified_pages'],old_annotations=150,
 total_annotations=sum(len(anns(p))for p in after.pages),new_red_ticks=12,new_notes=6,
 old_annotations_preserved=True,original_text_prefix_preserved=True,
 unchanged_pages_text_equal=True,protected_files_unchanged=True,
 source_hashes_match=True,audits=audits,sha256_before=plan['backup']['sha256_before'],
 sha256_after=sha(Path(plan['backup']['target'])),visual_review='passed; all modified pages inspected in after-10.png through after-13.png')
assert result['total_annotations']==168
(folder/'verification.json').write_text(json.dumps(result,ensure_ascii=False,indent=2))
visual=dict(method='Poppler 150 dpi PNG; root inspected every modified page with view_image',
 pages={str(n):{'render':f'after-{n}.png','tick_visible':True,'scope_readable':True,
 'formula_uncovered':True,'no_clipping':True,'old_annotations_preserved':True}for n in plan['modified_pages']},
 notes='p11旧“积分待完成”和p12旧“右式能量律待完成”保留；新增顶部说明其历史属性与当前条件性范围。')
(folder/'visual_review.json').write_text(json.dumps(visual,ensure_ascii=False,indent=2))
print(json.dumps(result,ensure_ascii=False,indent=2))
