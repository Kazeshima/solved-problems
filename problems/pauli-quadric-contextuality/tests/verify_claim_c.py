"""Build local Lean modules in dependency order, audit axioms, and replay the public targets."""
from argparse import ArgumentParser
from datetime import datetime,timezone
from hashlib import sha256
from pathlib import Path
import re,subprocess,sys

IMPORT=re.compile(r"^import\s+(Quadric(?:\.\w+)*)\s*$",re.MULTILINE)

def local_sources(project):
    source={"Quadric":project/"Quadric.lean"}
    for f in (project/"Quadric").rglob("*.lean"):
        source[".".join(f.relative_to(project).with_suffix("").parts)]=f
    return source

def waves(source):
    deps={};seen=set()
    def visit(m):
        if m in deps:return
        if m in seen:raise ValueError(f"cyclic local import {m}")
        seen.add(m)
        wanted=set(IMPORT.findall(source[m].read_text(encoding="utf8")))
        for d in sorted(wanted):
            if d not in source:raise ValueError(f"{m} imports missing module {d}")
            visit(d)
        seen.remove(m);deps[m]=wanted
    visit("Quadric")
    done=set()
    while len(done)<len(deps):
        ready=sorted(m for m,ds in deps.items() if m not in done and ds<=done)
        if not ready:raise ValueError("unresolved local import graph")
        yield ready
        done.update(ready)

def timestamp():return datetime.now(timezone.utc).isoformat()

def main():
    parser=ArgumentParser(description=__doc__)
    parser.add_argument("project",type=Path)
    parser.add_argument("--lake",default="lake")
    parser.add_argument("--jobs",type=int,default=2)
    parser.add_argument("--require-clean",action="store_true")
    args=parser.parse_args()
    root=args.project.resolve()
    if not (root/"lakefile.toml").is_file():parser.error("missing Lean project")
    if args.jobs<1:parser.error("--jobs must be positive")
    lib=root/'.lake/build/lib/lean'
    if args.require_clean and ((lib/'Quadric.olean').is_file() or any((lib/'Quadric').rglob('*.olean'))):
        parser.error('expected a source-only project with no previously built Quadric modules')
    files=local_sources(root);stages=list(waves(files))
    for mod in sorted(m for wave in stages for m in wave):
        print(sha256(files[mod].read_bytes()).hexdigest(),files[mod].relative_to(root),flush=True)
    for name in ('Audit.lean','Replay.lean','lean-toolchain','lakefile.toml','lake-manifest.json'):
        print(sha256((root/name).read_bytes()).hexdigest(),name,flush=True)
    def run(cmd):
        print(timestamp(),*cmd,flush=True)
        code=subprocess.run(cmd,cwd=root).returncode
        print(timestamp(),f"exit={code}",flush=True)
        if code:sys.exit(code)
    for wave in stages:
        for off in range(0,len(wave),args.jobs):
            run([args.lake,"build",*wave[off:off+args.jobs]])
    run([args.lake,"env","lean","--trust=0","Audit.lean"])
    run([args.lake,"env","lean","-j","1","-s","65536","Replay.lean"])
    return 0

if __name__=="__main__":raise SystemExit(main())
