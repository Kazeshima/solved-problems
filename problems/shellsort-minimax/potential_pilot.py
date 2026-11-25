"""Export a full remaining-cost table and emit a kernel-replayable block of its edge inequalities."""
import argparse
from hashlib import sha256
from pathlib import Path
import struct
import subprocess
import tempfile
import zlib

def offsets(n,s):
    return [s | 1<<i for i in range(n) if not s>>i&1]

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--binary",required=True)
    ap.add_argument("--n",type=int,default=17)
    ap.add_argument("--gaps",nargs="+",type=int,default=[9,6,4,1])
    ap.add_argument("--first",type=int,default=0)
    ap.add_argument("--count",type=int,default=8)
    ap.add_argument("--out",default="Potential17.lean")
    ap.add_argument("--packed",default="evidence/potential17.zlib")
    args=ap.parse_args(); n=args.n; H=args.gaps
    first,end=args.first,args.first+args.count
    if first<0 or end>1<<n or first>=end:raise ValueError("block range")
    with tempfile.TemporaryDirectory() as tmp:
        path=Path(tmp)/"values"
        subprocess.run([args.binary,str(n),*map(str,H),"--save",str(path)],check=True)
        raw=path.read_bytes()
    if len(raw)!=2*(1<<n):raise ValueError("truncated potentials")
    packed=zlib.compress(raw,9)
    if zlib.decompress(packed)!=raw: raise ValueError("packing mismatch")
    Path(args.packed).parent.mkdir(parents=True,exist_ok=True)
    Path(args.packed).write_bytes(packed)
    use=set(range(first,end))
    for s in range(first,end):use.update(offsets(n,s))
    src=["import Certificates", "open ShellMinimax ShellMinimax.Certificate",
         "set_option maxRecDepth 65536","set_option maxHeartbeats 8000000",f"namespace ShellMinimax.Block{n}",
         f"def localValues (s : Finset (Fin {n})) : Nat :=", "  match s.sum (fun i => 2^i.val) with"]
    for s in sorted(use):
        v=struct.unpack_from("<H",raw,2*s)[0]
        src.append(f"  | {s} => {v}")
    src.append("  | _ => 0")
    for s in range(first,end):
        lit="{"+",".join(str(i) for i in range(n) if s>>i&1)+"}" if s else "∅"
        src.append(f"theorem state{s} : localCheck {H} localValues {lit} = true := by decide")
    src.append(f"end ShellMinimax.Block{n}")
    Path(args.out).write_bytes(("\n".join(src)+"\n").encode())
    print("full table UInt16LE",len(raw),sha256(raw).hexdigest())
    print("packed",len(packed),sha256(packed).hexdigest(),"block",first,end,"checked outgoing edges",sum(len(offsets(n,s)) for s in range(first,end)))

if __name__=="__main__":main()
