"""Inspect dated versions and source-level matches at the review cutoff."""
import concurrent.futures as cf
import datetime
import hashlib
import json
import re
import subprocess
import urllib.parse
import urllib.request

CUT = "2026-11-25T22:13:34Z"
def read(url):
    req=urllib.request.Request(url,headers={"User-Agent":"ShellsortResearchReview/1.0"})
    with urllib.request.urlopen(req,timeout=25) as f: return f.read()

def get(url): return json.loads(read(url))
def entry(repo,path):
    api="https://api.github.com/repos/"+repo
    branch=get(api+"/commits?until="+CUT+"&per_page=1")[0]["sha"]
    recent=get(api+"/commits?"+urllib.parse.urlencode({"path":path,"until":CUT,"per_page":1}))
    if not recent: return dict(repo=repo,revision=branch,path=path,result="no path history at cutoff")
    url=f"https://raw.githubusercontent.com/{repo}/{branch}/{path}"
    raw=read(url)
    lines=raw.decode(errors="replace").splitlines()
    patterns=r"worst.case|Boolean|subset|threshold|smaller_before|shifts \+=|failures \+=|returns? W;|numerator =|average.case|平均|exact global|theorem verified"
    matches=[i+1 for i,s in enumerate(lines) if re.search(patterns,s,re.I)]
    return dict(repo=repo,revision=branch,path=path,sha256=hashlib.sha256(raw).hexdigest(),
                last_change=recent[0]["commit"]["committer"]["date"],link=f"https://github.com/{repo}/blob/{branch}/{path}",
                line_count=len(lines),matched_lines=matches[:15])
def tree(repo):
    api="https://api.github.com/repos/"+repo
    head=get(api+"/commits?until="+CUT+"&per_page=1")[0]["sha"]
    tree=get(api+f"/git/trees/{head}?recursive=1")
    files=[e["path"] for e in tree["tree"] if e["type"]=="blob"]
    related=[p for p in files if re.search("shellsort|shell.sort",p,re.I)]
    wanted=[p for p in related if re.search("optimum|worst|threshold|comparison",p,re.I)]
    return dict(repo=repo,revision=head,tree_truncated=tree["truncated"],files=len(files),shellsort_paths=len(related),
                selected_paths=wanted[:25],top_dirs=sorted({p.split("/")[0] for p in related})[:20])
def attempt(f,*args):
    try:return f(*args)
    except Exception as e:return {"args":args,"error":str(e)}

if __name__=="__main__":
    paths=[("mkdokken/ShellSort","worst_case_two_gap.c"),("mkdokken/ShellSort","README.md"),
           ("EternalYMZ/Project-S","research/2026-11-25/exact_shellsort_mean.py"),
           ("EternalYMZ/Project-S","research/2026-11-25/README.md"),
           ("LeanPool/lean-pool","LeanPool/ShellsortMean/VerifiedOptimum.lean"),
           ("Nannde/shellsort-three-pass-optimality","README.md"),("openai/math","README.md")]
    with cf.ThreadPoolExecutor(5) as ex:
        jobs=[ex.submit(attempt,entry,*p) for p in paths]+[ex.submit(attempt,tree,r) for r in ("LeanPool/lean-pool","openai/math")]
        for j in jobs: print(json.dumps(j.result(),ensure_ascii=True),flush=True)
    for q in ('"Shellsort" "minimax"', '"Shellsort" "threshold" "comparisons"',
              '"Shellsort" "Boolean lattice"', '"shellsort" "worst" repo:EternalYMZ/Project-S',
              '"shellsort" repo:openai/math'):
        command=["gh","api","-X","GET","search/code","-f","q="+q,"-f","per_page=5"]
        r=subprocess.run(command,capture_output=True,text=True,encoding="utf-8",errors="replace")
        if r.returncode: result=r.stderr.strip()[:300]
        else:
            obj=json.loads(r.stdout)
            result=dict(count=obj["total_count"],incomplete=obj["incomplete_results"],links=[x["html_url"] for x in obj["items"]])
        print(json.dumps({"GitHub code query":q,"result":result}),flush=True)
