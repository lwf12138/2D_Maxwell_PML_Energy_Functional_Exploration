"""复核 v0.3.1 标注的保留性、证据及渲染；须另做人工视觉验收。"""
from pathlib import Path
from collections import Counter
import hashlib, json, subprocess
from pypdf import PdfReader

root = Path.cwd()
folder = root / "logs/v0.3.1/pdf"
plan = json.loads((folder / "annotation_plan.json").read_text())
target, backup = Path(plan["backup"]["target"]), Path(plan["backup"]["backup"])
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
before, after = PdfReader(backup), PdfReader(target)
assert len(before.pages) == len(after.pages) == 18

def annotations(page):
    return list(page["/Annots"]) if "/Annots" in page else []

def signature(reference):
    annotation = reference.get_object()
    return tuple(str(annotation.get(k)) for k in
                 ("/Subtype", "/Rect", "/Contents", "/T", "/F", "/NM"))

all_new = []
for number, (old, final) in enumerate(zip(before.pages, after.pages), 1):
    assert list(old.mediabox) == list(final.mediabox)
    assert list(old.cropbox) == list(final.cropbox)
    old_text, final_text = old.extract_text() or "", final.extract_text() or ""
    assert final_text.startswith(old_text), ("正文变化", number)
    if number not in plan["modified_pages"]:
        assert old_text == final_text, ("非目标页正文变化", number)
    assert Counter(signature(a) for a in annotations(old)) <= Counter(
        signature(a) for a in annotations(final)), ("原批注丢失", number)
    for reference in annotations(final):
        annotation = reference.get_object()
        if str(annotation.get("/NM", "")).startswith("LeanPML.v0.3.1."):
            all_new.append({"page": number, "id": str(annotation["/NM"]),
                            "rect": list(map(float, annotation["/Rect"])),
                            "text": str(annotation["/Contents"])})
expected = {"LeanPML.v0.3.1." + e["id"] for e in plan["entries"] if e["new_tick"]}
expected |= {"LeanPML.v0.3.1." + n["id"] for n in plan["notes"]}
assert len(all_new) == len(expected) and {a["id"] for a in all_new} == expected
assert {a["page"] for a in all_new} == set(plan["modified_pages"])
assert (after.metadata or {})["/LeanPMLV031MarkPlanSHA256"] == sha(folder / "annotation_plan.json")
for entry in plan["entries"]:
    assert sha(root / entry["module"]) == entry["source_sha256"]
for path, digest in plan["protected_hashes"].items():
    assert sha(Path(path)) == digest, ("受保护文件变化", path)
for stem in (plan["build"], plan["audit"]):
    metadata = json.loads((root / "logs/v0.3.1" / (stem + ".json")).read_text())
    assert metadata["exit_code"] == 0 and metadata["status"] == "finished"
report = {
    "page_count": 18,
    "modified_pages": plan["modified_pages"],
    "old_annotations": sum(len(annotations(p)) for p in before.pages),
    "new_annotations": all_new,
    "new_red_ticks": sum(e["new_tick"] for e in plan["entries"]),
    "total_annotations": sum(len(annotations(p)) for p in after.pages),
    "unchanged_pages_text_equal": True,
    "original_text_prefix_preserved": True,
    "old_annotations_preserved": True,
    "protected_files_unchanged": True,
    "sha256_before": sha(backup),
    "sha256_after": sha(target),
    "plan_sha256": sha(folder / "annotation_plan.json"),
    "visual_review": "pending",
}
for number in plan["modified_pages"]:
    command = [
        "/Users/wcli/.cache/codex-runtimes/codex-primary-runtime/dependencies/bin/override/pdftoppm",
        "-f", str(number), "-l", str(number), "-scale-to", "1800", "-png", "-singlefile",
        str(target), str(folder / f"after-{number:02d}")
    ]
    print("渲染命令：", json.dumps(command, ensure_ascii=False), flush=True)
    subprocess.run(command, check=True)
    assert (folder / f"after-{number:02d}.png").exists()
(folder / "verification.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({k: v for k, v in report.items() if k != "new_annotations"},
                 ensure_ascii=False, indent=2))
