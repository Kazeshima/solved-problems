"""Run the normal Lake entry points, retain both streams and exit codes, audit all targets."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import time

root=Path(__file__).resolve().parents[1]
out=root/"classification"/"results"
allow={"propext","Classical.choice","Quot.sound"}

def run(label,cmd):
    executable=shutil.which(cmd[0])
    if not executable: raise RuntimeError("Missing "+cmd[0])
    t=time.monotonic()
    began=datetime.now(timezone.utc).isoformat()
    p=subprocess.run([executable,*cmd[1:]],cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    text=p.stdout.decode("utf-8","replace").replace("\r\n","\n")
    log="$ "+" ".join(cmd)+"\nUTC "+began+"\n"+text+f"\nexit={p.returncode} elapsed_seconds={time.monotonic()-t:.2f}\n"
    (out/(label+".log")).write_text(log,encoding="utf8")
    if p.returncode or re.search(r"PANIC|sorryAx|error:|declaration uses ',?sorry",text,re.I):
        raise RuntimeError("See "+label+".log")
    return text

def check_axioms(source,text):
    names={line.split()[-1] for line in (root/source).read_text(encoding="utf8").splitlines() if line.startswith("#print axioms ")}
    seen={}
    for name,deps in re.findall(r"'PottsBP\.([\w.]+)' (depends on axioms: \[[^\]]*\]|does not depend on any axioms)",text):
        axs=set(re.findall(r"[A-Za-z][A-Za-z.]+",deps.partition("[")[2]))
        if axs-allow: raise ValueError((name,axs))
        seen[name]=axs
    if set(seen)!=names:raise ValueError(("audit targets differ",names-set(seen),set(seen)-names))
    return len(seen)

def main():
    manifest=json.loads((root/"lake-manifest.json").read_text())
    for pkg in manifest["packages"]:
        actual=subprocess.check_output(["git","-C",str(root/".lake"/"packages"/pkg["name"]),"rev-parse","HEAD"],text=True).strip()
        assert actual==pkg["rev"],pkg["name"]
    ver=run("lean-version",["lake","env","lean","--version"]).strip()
    assert "4.19.0" in ver
    gh=run("lean-githash",["lake","env","lean","--githash"]).strip()
    run("lake-version",["lake","--version"])
    run("classification-build",["lake","build"])
    run("original-direct",["lake","env","lean","PottsBP.lean"])
    orig=check_axioms("Audit.lean",run("original-axioms",["lake","env","lean","--trust=0","Audit.lean"]))
    prior=run("original-replay",["lake","env","lean","Replay.lean"])
    run("classification-direct",["lake","env","lean","PottsClassification.lean"])
    current=check_axioms("ClassificationAudit.lean",run("classification-axioms",["lake","env","lean","--trust=0","ClassificationAudit.lean"]))
    replay=run("classification-replay",["lake","env","lean","ClassificationReplay.lean"])
    n=re.search(r"Kernel replay accepted (\d+) declarations above Lean Init",replay)
    targets=re.findall(r"Replayed target ([\w.]+)",replay)
    expected=set(re.findall(r"\x60\x60(PottsBP\.[\w.]+)",(root/"ClassificationReplay.lean").read_text(encoding="utf8")))
    assert n and set(targets)==expected and "Kernel replay accepted" in prior
    named={(p.stem,k) for p in root.glob("PottsClass*.lean") for k in
           re.findall(r"^(?:private )?(?:theorem|lemma) ([\w.]+)",p.read_text(encoding="utf8"),re.M)}
    covered=set(re.findall(r"^Covered theorem (\w+)/([\w.]+) with axioms",replay,re.M))
    if covered!=named: raise ValueError(("source/replay coverage differs",named-covered,covered-named))
    sources=sorted(root.glob("Potts*.lean"))
    for p in sources:
        if re.search(r"\b(sorry|admit|sorryAx|axiom|unsafe|native_decide|ofReduceBool)\b",p.read_text(encoding="utf8")):raise ValueError(p.name)
    head=subprocess.run(["git","rev-parse","HEAD"],cwd=root,text=True,capture_output=True)
    report={"status":"PASS","checkout_head_at_run":head.stdout.strip() if head.returncode==0 else None,
        "lean":ver,"lean_commit":gh,"packages":{p["name"]:p["rev"] for p in manifest["packages"]},
        "original_axiom_reports":orig,"combined_axiom_reports":current,"allowed_axioms":sorted(allow),
        "replayed_targets":targets,"new_named_theorems_covered":len(covered),"declarations_above_Init":int(n[1]),
        "source_sha256":{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}}
    (out/"formal-acceptance.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf8")
    print(f"PASS: {current} axiom reports, {len(targets)} replay targets, {n[1]} rechecked declarations above Init.")

if __name__=="__main__":main()
