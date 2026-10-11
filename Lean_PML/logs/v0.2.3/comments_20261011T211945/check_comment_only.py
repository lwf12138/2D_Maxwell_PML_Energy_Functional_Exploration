from pathlib import Path
import json,hashlib
root=Path.cwd();folder=root/"logs/v0.2.3/comments_20261011T211945"
def strip_comments(text):
    out=[];i=0;depth=0
    while i<len(text):
        if text[i:i+2]=="/-":depth+=1;i+=2
        elif depth and text[i:i+2]=="-/":depth-=1;i+=2
        elif depth:i+=1
        elif text[i:i+2]=="--":
            end=text.find("\n",i);i=len(text) if end<0 else end
        else:out.append(text[i]);i+=1
    assert depth==0
    return "".join(out)
before=(folder/"before_LocalSpatial.lean").read_text()
after=(root/"LeanPML/PML/LocalSpatial.lean").read_text()
assert strip_comments(before)==strip_comments(after)
data=dict(only_comments_changed=True,
    before_sha256=hashlib.sha256(before.encode()).hexdigest(),
    after_sha256=hashlib.sha256(after.encode()).hexdigest(),
    lean_code_sha256_excluding_comments=hashlib.sha256(strip_comments(after).encode()).hexdigest(),
    declarations_with_added_formulas=31)
for path,digest in json.loads((folder/"before_hashes.json").read_text()).items():
    if path.endswith("/LeanPML/PML/LocalSpatial.lean"):continue
    assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==digest,path
(folder/"comment_only_check.json").write_text(json.dumps(data,ensure_ascii=False,indent=2)+"\n")
print(json.dumps(data,ensure_ascii=False,indent=2))
print("PDF、MD、TEX、工具链及依赖配置未变；定义、假设、证明代码逐字不变。")
