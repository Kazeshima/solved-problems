"""Generate proof input from untrusted records. Lean's kernel checks every emitted claim."""
import argparse
from pathlib import Path
import re
import struct
import subprocess
import sys
import tempfile
sys.path.insert(0,str(Path(__file__).resolve().parent))
from oracle import gaps

HEADER = """import Certificates
open ShellMinimax ShellMinimax.Certificate
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
"""
def arr(values): return "["+", ".join(map(str,values))+"]"
def witness(n,H,U,p,name):
    return f"""
def {name} : List (Fin {n}) := {arr(p)}
theorem {name}_checked : validInput {name} = true ∧ cost (input {name}) {arr(H)} = {U} := by decide
theorem {name}_attains : ∃ P : Equiv.Perm (Fin {n}), cost P {arr(H)} = {U} := by
  obtain ⟨P,hP⟩ := input_perm {name}_checked.1
  exact ⟨P, hP ▸ {name}_checked.2⟩
"""
def winner_input(source):
    result = [HEADER,"namespace ShellMinimax.Witnesses\n"]
    for i,line in enumerate(Path(source).read_text().splitlines()):
        m=re.fullmatch(r"n=(\d+) gaps=([\d,]+) max=(\d+) witness=([\d,]+)",line)
        if m:
            n,U=int(m[1]),int(m[3]); H,p=([int(k) for k in v.split(",")] for v in (m[2],m[4]))
            result.append(witness(n,H,U,p,f"w{n}_{H[0]}"))
    if len(result)==2: raise ValueError("no witnesses")
    return "".join(result)+"\nend ShellMinimax.Witnesses\n"
def certificate(path,first,limit,full,mixed):
    with open(path) as f:
        tag,n,U=f.readline().split(); n,U=int(n),int(U)
        if tag!="N" or n<2: raise ValueError("header")
        total=1<<(n-2)
        end=min(total,first+limit) if limit is not None else total
        complete=first==0 and end==total
        if first<0 or first>=end: raise ValueError("empty interval")
        chunks=[HEADER,f"namespace ShellMinimax.Reflected{n}\n"]
        pool={}; rows=[]; used=set(); mask_count=0
        for line in f:
            tag,*args=line.split()
            if tag=="P":
                idx,*p=map(int,args)
                if idx in pool or sorted(p)!=list(range(n)): raise ValueError("P")
                pool[idx]=p
                continue
            if tag=="END":
                if int(args[0])!=total or mask_count!=total:raise ValueError("END")
                break
            m=int(args[0])
            if m!=mask_count:raise ValueError("mask")
            mask_count+=1
            if m<first:continue
            if m>=end:break
            H=gaps(n,m)
            if tag=="B": row=".baseline"
            elif tag=="X":
                idx=int(args[1])
                if idx not in used:
                    chunks.append(f"def p{idx} : List (Fin {n}) := {arr(pool[idx])}\n")
                    used.add(idx)
                row=f".witness p{idx}"
            elif tag=="O":
                if not full or not mixed: raise ValueError("winner needs both solvers")
                with tempfile.TemporaryDirectory() as td:
                    potential=Path(td)/"potential.bin"
                    subprocess.run([full,str(n),*map(str,H),"--save",str(potential)],check=True,stdout=subprocess.DEVNULL)
                    raw=potential.read_bytes()
                if len(raw)!=(2<<n):raise ValueError("potential size")
                v=[v[0] for v in struct.iter_unpack("<H",raw)]
                out=subprocess.check_output([mixed,str(n),"exact",*map(str,H)],text=True)
                p=[int(k) for k in out.split("witness=")[1].split(",")]
                chunks.append(f"def values{m} : Array Nat := #{arr(v)}\n")
                row=f".optimum {arr(p)} (fun s => values{m}[s.sum (fun i => 2^i.val)]?.getD 0)"
            else:raise ValueError(tag)
            rows.append((m,H,row))
        if len(rows)!=end-first:raise ValueError("missing rows")
        if complete:
            if mask_count!=total or tag!="END":raise ValueError("incomplete")
            chunks.append(f"def rows (t : Finset Nat) : Row {n} :=\n  match t.sum (fun h => 2^h) with\n")
            chunks.extend(f"  | {sum(1<<h for h in H)} => {row}\n" for _,H,row in rows)
            chunks.append("  | _ => .baseline\n")
            chunks.append(f"theorem checked : checkAll {n} {U} rows = true := by decide\n")
            win_tables = [H for _,H,row in rows if row.startswith(".optimum")]
            chunks.append("def minimizers : List (List Nat) := ["+", ".join(arr(H) for H in win_tables)+"]\n")
            chunks.append(f"""theorem names : ∀ t ∈ tables {n}, winner (rows t) = true ↔ tableGaps {n} t ∈ minimizers := by decide
theorem global :
    (∃ H, Legal {n} H ∧ thresholdMaximum {n} H = {U}) ∧
    ∀ H, Legal {n} H → {U} ≤ thresholdMaximum {n} H ∧
      (thresholdMaximum {n} H = {U} ↔ winner (rows H.toFinset) = true) :=
  certificate_sound checked
theorem exact_minimizers (H : List Nat) (hl : Legal {n} H) :
    thresholdMaximum {n} H = {U} ↔ H ∈ minimizers := by
  obtain ⟨ht,hH⟩ := enumeration.mp hl
  have hn := names H.toFinset ht
  rw [tableGaps_eq ht,hH] at hn
  exact (global.2 H hl).2.trans hn
""")
        else:
            # All masks in this interval have individual kernel equalities.
            for m,H,row in rows:
                chunks.append(f"theorem mask{m} : check (n := {n}) {U} {arr(H)} ({row}) = true := by decide\n")
        return "".join(chunks)+f"end ShellMinimax.Reflected{n}\n"

if __name__=="__main__":
    ap=argparse.ArgumentParser()
    src=ap.add_mutually_exclusive_group(required=True)
    src.add_argument("--certificate")
    src.add_argument("--witnesses")
    ap.add_argument("--first",type=int,default=0)
    ap.add_argument("--limit",type=int)
    ap.add_argument("--full")
    ap.add_argument("--mixed")
    ap.add_argument("--out",required=True)
    ap.add_argument("--timed",action="store_true",help="log monotonic timestamps around the generated declarations")
    a=ap.parse_args()
    value=winner_input(a.witnesses) if a.witnesses else certificate(a.certificate,a.first,a.limit,a.full,a.mixed)
    if a.timed:
        lines=value.splitlines()
        start=next(i for i,line in enumerate(lines) if line.startswith("namespace "))
        lines.insert(start+1,'run_cmd Lean.logInfo m!"begin_ms {← IO.monoMsNow}"')
        lines.insert(len(lines)-1,'run_cmd Lean.logInfo m!"end_ms {← IO.monoMsNow}"')
        value="\n".join(lines)+"\n"
    Path(a.out).write_bytes(value.encode())
